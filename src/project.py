import logging
from collections import defaultdict
#from msilib.schema import MsiAssembly
import time
from tracemalloc import start

from requests import post
from src.cfg.cfg import CFG
from src.cfg.disassembly import generate_BBs
from src.cfg.opcodes import external_data
from src.evm.evm import run, run_symbolic
from src.evm.exceptions import IntractablePath, ExternalData, TimeoutException
from src.explorer.forward import ForwardExplorer
from src.slicing import interesting_slices, slice_to_program
from src.util.z3_extra_util import concrete
import src.util.utils
from src.flow.tainting import run_static
from src.flow import code_info as cinfo

def load(path):
    with open(path) as infile:
        return Project(bytes.fromhex(infile.read().strip()))

def load_json(path):
    import json
    with open(path) as infile:
        return Project.from_json(json.load(infile))

class Project(object):
    def __init__(self, code, cfg=None):
        self.code = code
        self._prg = None
        self._cfg = cfg
        self._writes = None

    @property
    def writes(self):
        if not self._writes:
            self._analyze_writes()
        return self._writes

    @property
    def symbolic_writes(self):
        return self.writes[None]

    @property
    def cfg(self):
        if not self._cfg:
            self._cfg = CFG(generate_BBs(self.code))
        return self._cfg

    @property
    def prg(self):
        if not self._prg:
            self._prg = {ins.addr: ins for bb in self.cfg.bbs for ins in bb.ins}
        return self._prg

    def to_json(self):
        return {'code': self.code.hex(), 'cfg': self.cfg.to_json()}

    @staticmethod
    def from_json(json_dict):
        code = bytes.fromhex(json_dict['code'])
        cfg = CFG.from_json(json_dict['cfg'], code)
        return Project(code, cfg)

    def run(self, program):
        return run(program, code=self.code)

    def run_symbolic(self, path, inclusive=False, mode=None, code_path=None, ac_jumpi=None):        
        #return run_symbolic(self.prg, path, self.code, inclusive=inclusive)
        return run_symbolic(self.prg, path, self.code, inclusive=inclusive, code_path=code_path, mode=mode, ac_jumpi=ac_jumpi)

    
    def get_constraints(self, instructions, args=None, inclusive=False, find_sstore=False):
        # only check instructions that have a chance to reach root
        instructions = [ins for ins in instructions if 0 in ins.bb.ancestors | {ins.bb.start}]
        
        if not instructions:
            return
        imap = {ins.addr: ins for ins in instructions}

        exp = ForwardExplorer(self.cfg)
        
        if args:
            slices = [s + (ins,) for ins in instructions for s in interesting_slices(ins, args, reachable=True)]                        
        else:
            # Are we looking for a state-changing path?
            if find_sstore:                
                sstores = self.cfg.filter_ins('SSTORE', reachable=True)
                slices = [(sstore, ins) for sstore in sstores for ins in instructions]                                
            else:
                slices = [(ins,) for ins in instructions]
            
        for path in exp.find(slices, avoid=external_data):                        
            logging.debug('Path %s', ' -> '.join('%x' % p for p in path))
            try:
                ins = imap[path[-1]]
                yield ins, path, self.run_symbolic(path, inclusive)
            except IntractablePath as e:
                bad_path = [i for i in e.trace if i in self.cfg._bb_at] + [e.remainingpath[0]]
                dd = self.cfg.data_dependence(self.cfg._ins_at[e.trace[-1]])
                if not any(i.name in ('MLOAD', 'SLOAD')     for i in dd):
                    ddbbs = set(i.bb.start for i in dd)
                    bad_path_start = next((j for j, i in enumerate(bad_path) if i in ddbbs), 0)
                    bad_path = bad_path[bad_path_start:]
                logging.info("Bad path: %s" % (', '.join('%x' % i for i in bad_path)))
                exp.add_to_blacklist(bad_path)
                continue
            except ExternalData:
                continue
            except TimeoutException:
                raise TimeoutException("Timed out!")
            except Exception as e:
                logging.exception('Failed path due to %s', e)
                continue
    def _analyze_writes(self):        
        sstore_ins = self.filter_ins('SSTORE')
        self._writes = defaultdict(set)
        for store in sstore_ins:
            for bs in interesting_slices(store):
                bs.append(store)
                prg = slice_to_program(bs)
                path = sorted(prg.keys())
                try:
                    r = run_symbolic(prg, path, self.code, inclusive=True)
                except IntractablePath:
                    logging.exception('Intractable Path while analyzing writes')
                    continue
                addr = r.state.stack[-1]
                if concrete(addr):
                    self._writes[addr].add(store)
                else:
                    self._writes[None].add(store)
        self._writes = dict(self._writes)

    def get_writes_to (self, addr):
        concrete_writes = set()
        if concrete(addr) and addr in self.writes:
            concrete_writes = self.writes[addr]
        return concrete_writes, self.symbolic_writes

    def reolve_struct_offset(self, ssa, slice, sload=False, sload_ins=None, sstore=False, sstore_ins=None):
        function = [f for f in ssa.functions][0]          
        if sload:                                            
            ssa_block=[ins for block in function if block.offset == sload_ins.bb.start for ins in block.insns]   
            ssa_ins= [s for s in ssa_block if s.offset == sload_ins.addr][0]
        elif sstore:
            ssa_block=[ins for block in function if block.offset == sstore_ins.bb.start for ins in block.insns]   
            ssa_ins= [s for s in ssa_block if s.offset == sstore_ins.addr][0]            
        struct_offset = None
        if ssa_ins.arguments[0]._writer is not None:
            if ssa_ins.arguments[0]._writer.insn.name =='ADD':
                if ssa_ins.arguments[0]._writer.arguments[0]._writer is not None and \
                    ssa_ins.arguments[0]._writer.arguments[1]._writer is None:
                    if  ssa_ins.arguments[0]._writer.arguments[0]._writer.insn.name=='SHA3':                        
                        struct_offset =ssa_ins.arguments[0]._writer.arguments[1].concrete_value
                elif  ssa_ins.arguments[0]._writer.arguments[0]._writer is None and \
                    ssa_ins.arguments[0]._writer.arguments[1]._writer is not None:
                    if ssa_ins.arguments[0]._writer.arguments[1]._writer.insn.name=='SHA3':
                        struct_offset =ssa_ins.arguments[0]._writer.arguments[0].concrete_value
            
        return struct_offset
        
    def resolve_slot_offset(self, ssa, slice, sload=False, sload_ins=None, sstore=False, sstore_ins=None):        
        function = [f for f in ssa.functions][0]                                                                                 
        if sload:            
            if [ins.name for ins in slice if ins.name in set(['SLOAD','EXP','DIV','SUB'])] ==['SLOAD','EXP','DIV']:            
                exp_ins = [ins for ins in slice if ins.name in set(['EXP'])]
                ssa_block=[ins for block in function if block.offset == exp_ins[0].bb.start for ins in block.insns]   
                ssa_ins =[s for s in ssa_block if s.offset == exp_ins[0].addr]
                if (ssa_ins[0].arguments[0].concrete_value==256):
                    start_byte=ssa_ins[0].arguments[1].concrete_value+1                                    
                elif (ssa_ins[0].arguments[0].concrete_value==2): #in binary
                    start_byte=ssa_ins[0].arguments[1].concrete_value/8+1                                
            elif [ins.name for ins in slice if ins.name in set(['SLOAD','EXP','DIV','SUB'])] ==['SLOAD','EXP','SUB']:
                #load starting first bye
                start_byte=1                      
            elif [ins.name for ins in slice if ins.name in set(['SLOAD','EXP','SUB','DIV'])] ==['SLOAD','EXP','SUB','DIV']:            
                div_ins = [ins for ins in slice if ins.name in set(['DIV'])]
                ssa_block=[ins for block in function if block.offset == div_ins[0].bb.start for ins in block.insns]   
                ssa_ins =[s for s in ssa_block if s.offset == div_ins[0].addr]
                if ssa_ins[0].arguments[1]._writer is None:
                    pos_str=str('%x' %ssa_ins[0].arguments[1].concrete_value)
                    start_byte=len(pos_str)//2+1-pos_str.find('1')            
                else:                    
                    exp_ins=ssa_ins[0].arguments[1]._writer
                    if exp_ins.insn.name =='EXP':
                        if (exp_ins.arguments[0].concrete_value==256):
                            start_byte= exp_ins.arguments[1].concrete_value+1                
                        elif (exp_ins.arguments[0].concrete_value==2): #in binary
                            start_byte=exp_ins.arguments[1].concrete_value/8+1                                                    
                    else:
                        start_byte='whole'
                        print('error, check resolve_slot_offset')                    
            else:
                start_byte='whole'                                            
        elif sstore:                        
            start_byte=None
            masking_pattern = [ins.name for ins in slice if ins.name in set(['SLOAD','EXP','SUB','NOT'])]                                    
            if len(masking_pattern)==0:
                start_byte='whole' # overapproximate the whole slot 

            elif 'NOT' not in masking_pattern or 'SLOAD' not in masking_pattern: #Cannot decide what is overwritten without SLOAD   
                start_byte='whole' #overapproximate  the whole slot 
            
            elif len([i for i in masking_pattern if i== 'NOT'])>1:# we may need to overapproximate as we do not know which not is for masking
                start_byte='whole' #overapproximate the whole slot                 
            
            elif len([i for i in masking_pattern if i == 'NOT'])==1 and 'SLOAD' in masking_pattern:              
                not_ins =[ins for ins in slice if ins.name =='NOT']
                ssa_block=[ins for block in function if block.offset ==not_ins[0].bb.start for ins in block.insns]   
                ssa_not_ins =[s for s in ssa_block if s.offset in [ins.addr for ins in slice if ins.name in set(['NOT'])]]                
                if ssa_not_ins[0].arguments[0]._writer is None:
                    pos_str=str('%x' %ssa_not_ins[0].arguments[0].concrete_value)
                    start_byte=(len(pos_str)-pos_str.rfind('f'))//2+1
                else:                                
                    ssa_ins=ssa_not_ins[0].arguments[0]._writer.arguments[1]._writer                    
                    if ssa_ins is not None and ssa_ins.insn.name =='EXP' and ssa_ins.arguments[0]._writer is None and ssa_ins.arguments[1]._writer is None:
                        exp = pow(ssa_ins.arguments[0].concrete_value, ssa_ins.arguments[1].concrete_value, src.util.utils.TT256)
                        mul = None
                        if ssa_not_ins[0].arguments[0]._writer.arguments[0]._writer is None:
                            mul = ssa_not_ins[0].arguments[0]._writer.arguments[0].concrete_value * exp
                        else:
                            sub_ins=ssa_not_ins[0].arguments[0]._writer.arguments[0]._writer
                            if sub_ins.insn.name =='SUB':
                                if sub_ins.arguments[0]._writer.insn.name=='EXP':
                                    exp1 = pow(sub_ins.arguments[0]._writer.arguments[0].concrete_value, sub_ins.arguments[0]._writer.arguments[1].concrete_value, src.util.utils.TT256)                                    
                                    sub = exp1 - sub_ins.arguments[1].concrete_value
                                    mul = sub * exp
                        if mul is not None:           
                            bit_mask = '%x' % (src.util.utils.TT256M1 - mul)                         
                            start_byte= (len(bit_mask)-bit_mask.rfind('0'))//2+1                                                                        
                    elif ssa_not_ins[0].arguments[0]._writer is not None and ssa_not_ins[0].arguments[0]._writer.insn.name=='SUB':                        
                        sub_ins=ssa_not_ins[0].arguments[0]._writer
                        if sub_ins.arguments[0]._writer is not None and sub_ins.arguments[0]._writer.insn.name=='EXP':
                            exp_ins = sub_ins.arguments[0]._writer
                            if exp_ins.arguments[0]._writer is None and exp_ins.arguments[1]._writer is None:
                                exp = pow(exp_ins.arguments[0].concrete_value, exp_ins.arguments[1].concrete_value, src.util.utils.TT256)                                    
                                sub = exp - sub_ins.arguments[1].concrete_value                                
                                bit_mask = '%x' % (src.util.utils.TT256M1 - sub)                         
                                start_byte= (len(bit_mask)-bit_mask.rfind('0'))//2+1                                  
                        elif sub_ins.arguments[0]._writer is not None and sub_ins.arguments[0]._writer.insn.name=='SHL':                                   
                            shl_ins = sub_ins.arguments[0]._writer                      
                            if shl_ins.arguments[0]._writer is None and shl_ins.arguments[1]._writer is None:
                                shl= (shl_ins.arguments[1].concrete_value << shl_ins.arguments[0].concrete_value)
                                sub = shl- sub_ins.arguments[1].concrete_value                 
                                bit_mask = '%x' % (src.util.utils.TT256M1 - sub)                         
                                start_byte= (len(bit_mask)-bit_mask.rfind('0'))//2+1
                    else:                    
                        start_byte='whole' #overapproximate the whole slot                                     
            
            if not start_byte:
                print(sstore_ins)                
                print(masking_pattern)            
        return start_byte

    def resolve_access_control_slots(self, ssa, instructions, ac_check_ins, args=None, memory_info=None, restricted=True):        
        slices = []
        other_ac_checks = []
        # only check instructions that have a chance to reach root                        
        instructions = [ins for ins in instructions if 0 in ins.bb.ancestors | {ins.bb.start}] 
        if not instructions:
            return
        imap = {ins.addr: ins for ins in instructions}
        access_sloads = defaultdict(list)        
        if args:                            
            for jump_ins in instructions:                
                for bs in interesting_slices(jump_ins, args, reachable=True, restricted=False):
                    if('%x' %jump_ins.addr) == '2f9':                    
                        print(jump_ins)                        
                        print(bs)
                    cur_jump_sloads= [v['sload'] for k in access_sloads if k==jump_ins for v in access_sloads[k]]
                    if len(cur_jump_sloads)!=0 and any(ins in cur_jump_sloads for ins in bs if ins.name in frozenset(['SLOAD'])): 
                        slices.append(bs+(jump_ins,))                                                                        
                    elif len(set(ac_check_ins)&set([ins.name for ins in bs]))==len(ac_check_ins) and not any(ins.name in frozenset(['CALL']) for ins in bs):                          
                        slices.append(bs+(jump_ins,))  
                        sload= [i for i in bs if i.name in frozenset(['SLOAD'])]                                                              
                        slot_byte= self.resolve_slot_offset(ssa, bs+(jump_ins,), sload=True, sload_ins=sload[0])                        
                        struct_offset= self.reolve_struct_offset(ssa, bs+(jump_ins,), sload=True, sload_ins=sload[0] )
                        access_sloads[jump_ins].append({'sload':sload[0],'sbyte':slot_byte,'structOffset':struct_offset}) 
                    elif any(ins.name in frozenset(['SLOAD']) for ins in bs) and (any(ins.arg==b'\xff' for ins in bs if ins.name in frozenset(['PUSH1'])) or \
                        any(ins.name in frozenset(['CALLDATALOAD','CALLDATACOPY']) for bb in jump_ins.bb.pred for ins in bb.ins)) and not any(ins.name in frozenset(['CALL']) for ins in bs):                                                                                                
                        if any(ins.arg==b'\xff' for ins in bs if ins.name in frozenset(['PUSH1'])):
                            sload_ins=[ins for ins in bs if ins.name in frozenset(['SLOAD']) if any(
                            ss.arg==b'\xff' and ins.addr < ss.addr <jump_ins.addr for ss in bs if ss.name in frozenset(['PUSH1']))]
                        else:
                            sload_ins=[ins for ins in bs if ins.name in frozenset(['SLOAD']) if not any(
                            ss.name in frozenset(['GT','LT']) and ss.bb.start == jump_ins.bb.start for ss in bs)]                                                        
                        if not sload_ins: 
                            continue                         
                        for s in interesting_slices(sload_ins[0],[0], memory_info, reachable=False, restricted=False):
                            if any(ins.name in frozenset(['CALLER']) for ins in s):                                                                                                
                                slices.append(bs+(jump_ins,)) 
                                sload= [i for i in bs if i.name in frozenset(['SLOAD'])]                                                                                                             
                                slot_byte= self.resolve_slot_offset(ssa, bs+(jump_ins,), sload=True, sload_ins=sload[0])                                
                                struct_offset= self.reolve_struct_offset(ssa, bs+(jump_ins,), sload=True, sload_ins=sload[0] )

                                access_sloads[jump_ins].append({'sload':sload[0],'sbyte':slot_byte,'structOffset':struct_offset})                                                                                                                                        
                    elif set([ins.name for ins in bs])&set(['CALLER','PUSH20','EQ']) == set(['CALLER','PUSH20','EQ']):
                       other_ac_checks.append(jump_ins)
                                                            
        return access_sloads, slices, imap, other_ac_checks

    def extract_control_paths(self, slices, imap):
        exp = ForwardExplorer(self.cfg)        
        for path in exp.find(slices, avoid=[]):           
            ins = imap[path[-1]]                                                                                                                
            yield ins, path

    def extract_paths(self,ssa, instructions, sinks, taintedBy, defect_type, args=None, storage_slots=None, storage_sha3_bases=None, inclusive=False, find_sstore=False, restricted=True, memory_info=None):        
        # only check instructions that have a chance to reach root                        
        instructions = [ins for ins in instructions if 0 in ins.bb.ancestors | {ins.bb.start}] 
        if not instructions:
            return
        imap = {ins.addr: ins for ins in instructions}        
        exp = ForwardExplorer(self.cfg)                    
        slices= []
        slot_sbyte={}
        struct_offset={}
        for ins in instructions:
             for s in interesting_slices(ins, args, memory_info, reachable=True, taintedBy=taintedBy, restricted=restricted):
                slices.append(s+(ins,)) 
                if ins.name =='SSTORE':                    
                    sbyte = self.resolve_slot_offset(ssa, s+(ins,), sstore=True, sstore_ins=ins)
                    slot_sbyte[ins] = sbyte                                      
                elif ins.name  in set(['SELFDESTRUCT','DELEGATECALL']): 
                    sbyte = self.resolve_slot_offset(ssa, s+(ins,), sload=True)                    
                    slot_sbyte[ins]=sbyte
                    sload_ins =[ins for ins in s if ins.name in set(['SLOAD'])]               
                    if len(sload_ins)>0:                                        
                        soffset= self.reolve_struct_offset(ssa, s+(ins,),sload=True, sload_ins=sload_ins[0]) 
                        struct_offset[ins]=soffset
        
        checked_ins=[] 
        c=0      
        start_time=time.time()            
        for path in exp.find(slices, avoid=[]):            
            logging.debug('Path %s', ' -> '.join('%x' % p for p in path))                                                                 
            c+=1            
            try:                    
                ins = imap[path[-1]]                                                                                                                                                
                if sinks:        
                    result = run_static(self.prg, ssa, path, sinks, self.code, inclusive,defect_type=defect_type, storage_slots=storage_slots, storage_sha3_bases=storage_sha3_bases)                                                                
                    if result._tainted and ins.name in set(['SSTORE']):                                                    
                        sstore_slices = [s+(ins,) for s in interesting_slices(ins, [0], memory_info, reachable=True, taintedBy=None, restricted=False)]                                                                                                                                                                                
                        soffset= self.reolve_struct_offset(ssa, sstore_slices[0],sstore=True, sstore_ins=ins)
                        struct_offset[ins]=soffset                                                            
                    yield ins,slot_sbyte,struct_offset, path, result
                else:
                    yield ins, slot_sbyte, struct_offset, path, None                        
            except IntractablePath as e:                
                bad_path = [i for i in e.trace if i in self.cfg._bb_at] + [e.remainingpath[0]]
                dd = self.cfg.data_dependence(self.cfg._ins_at[e.trace[-1]])
                if not any(i.name in ('MLOAD', 'SLOAD')     for i in dd):
                    ddbbs = set(i.bb.start for i in dd)
                    bad_path_start = next((j for j, i in enumerate(bad_path) if i in ddbbs), 0)
                    bad_path = bad_path[bad_path_start:]
                logging.info("Bad path: %s" % (', '.join('%x' % i for i in bad_path)))
                exp.add_to_blacklist(bad_path)
                continue
            except ExternalData:
                continue
            except TimeoutException:
                raise TimeoutException("Timed out!")
            except Exception as e:
                logging.exception('Failed path due to %s', e)                     
                continue            


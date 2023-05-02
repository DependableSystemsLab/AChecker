import datetime
import logging
from collections import defaultdict
import numbers
import numpy as np
import src.util.utils
from src.evm.exceptions import ExternalData, VMException
from src.flow.analysis_results import   TainitAnalysisResult
from src.evm.state import  EVMState, AbstractEVMState

from src.cfg import opcodes

class taint(object):
    def __init__(self):
        self.tRegisters = []
        self.tMemory = []
        self.tStorage = []
        self.memory = {}
        self.storage = {}
        self.registers = {}    
        self.signed_memory =[]
        self.sha3_bases = {}        
        self.slot_types ={}
        self.balance = dict()
        self.origin = 0
        self.address = 0
        self.caller= 63
        self.callvalue = 513
        self.calldata = []
        self.returndata = []
        self.gasprice = 0
        self.gaslimit = 0
        self.coinbase = 0
        self.timestamp = 0
        self.blockhash = 0
        self.number = 0
        self.difficulty = 0
        
    def get_mem(self, start, size):        
        tmp = []        
        for k in range(start,size):            
            tmp.append(self.memory.get(k,0))        
        return tmp

    def isTainted_register(self, reg, from_storage=False):        
        if reg._writer is None:
            return False        
        
        if not from_storage:            
            if (reg._writer._return_value in [regs[0] for regs in self.tRegisters]):
                return True
            else:            
                return False            
        else:            
            if (reg._writer._return_value in [regs[0] for regs in self.tRegisters if regs[1]!={} and 'SLOAD' in regs[1]]):
                return True
            else:            
                return False            

    def isTainted_memory(self, loc, size=1):
        loc_range=range(loc, loc+size)                    
        if len([locs[0] for locs in self.tMemory if locs[0] in loc_range])!=0:     
            return True
        else:
            return False
        
    def isSha3_based(self, reg):                    
        if reg._writer is None:
            return False        

        if (reg._writer._return_value in self.sha3_bases):     
            return True
        else:
            return False
    
    def taint_register(self, reg, sources=[]):
        self.tRegisters.append([reg,sources])        

    def get_reg_taint_source(self, reg):                     
        try:
            return [treg[1] for treg in self.tRegisters if treg[0]==reg._writer._return_value][0]
        except IndexError:
            return []

    def get_mem_taint_source(self, loc,size=1):        
        loc_range=range(loc, loc+size)
        if size==1:
            return [tmem[1] for tmem in self.tMemory if tmem[0] in loc_range][0]
        else:
            t = [tmem[1] for tmem in self.tMemory if tmem[0] in loc_range]
            return [j for i in t for j in i]


    def get_reg_sha3_bases(self, reg):            
        try:
            return [base for treg, base in self.sha3_bases.items() if treg==reg._writer._return_value][0]
        except IndexError:
            return []

    def get_reg_slot_type(self, reg):            
        try:
            return [stype for treg, stype in self.slot_types.items() if treg==reg._writer._return_value][0]
        except IndexError:
            return []

    def propagate_sha3_bases(self, reg, arg1, arg2=None, arg3=None):               
        if arg3 is not None:
            arg3_Sha3_based = self.isSha3_based(arg3)
        else:
            arg3_Sha3_based =False
        if arg2 is not None:
            arg2_Sha3_based = self.isSha3_based(arg2)
        else:
            arg2_Sha3_based=False
        arg1_Sha3_based = self.isSha3_based(arg1)

        if arg1_Sha3_based and arg2_Sha3_based and arg3_Sha3_based:                                        
            self.sha3_bases[reg]=self.get_reg_sha3_bases(arg1)+self.get_reg_sha3_bases(arg2)+self.get_reg_sha3_bases(arg3)                
        elif arg1_Sha3_based and arg2_Sha3_based:                                                   
            self.sha3_bases[reg]=self.get_reg_sha3_bases(arg1)+self.get_reg_sha3_bases(arg2)
        elif arg1_Sha3_based:                                        
            self.sha3_bases[reg]=self.get_reg_sha3_bases(arg1)
        elif arg2_Sha3_based:                                        
            self.sha3_bases[reg]=self.get_reg_sha3_bases(arg2)
        elif arg1_Sha3_based and arg3_Sha3_based:                                        
            self.sha3_bases[reg]=self.get_reg_sha3_bases(arg1)+self.get_reg_sha3_bases(arg3)
        elif arg2_Sha3_based and arg3_Sha3_based:                                        
            self.sha3_bases[reg]=self.get_reg_sha3_bases(arg2)+self.get_reg_sha3_bases(arg3)
        elif arg3_Sha3_based:                                        
            self.sha3_bases[reg]=self.get_reg_sha3_bases(arg3)
        
    def propagate_slot_types(self, reg, arg1, arg2=None, arg3=None):               
        if arg3 is not None:
            arg3_Sha3_based = self.isSha3_based(arg3)
        else:
            arg3_Sha3_based =False
        if arg2 is not None:
            arg2_Sha3_based = self.isSha3_based(arg2)
        else:
            arg2_Sha3_based=False
        arg1_Sha3_based = self.isSha3_based(arg1)

        if arg1_Sha3_based and arg2_Sha3_based and arg3_Sha3_based:                                        
            self.slot_types[reg]=self.get_reg_slot_type(arg1)+self.get_reg_slot_type(arg2)+self.get_reg_slot_type(arg3)                
        elif arg1_Sha3_based and arg2_Sha3_based:                                        
            self.slot_types[reg]=self.get_reg_slot_type(arg1)+self.get_reg_slot_type(arg2)
        elif arg1_Sha3_based:                                        
            self.slot_types[reg]=self.get_reg_slot_type(arg1)
        elif arg2_Sha3_based:                                        
            self.slot_types[reg]=self.get_reg_slot_type(arg2)
        elif arg1_Sha3_based and arg3_Sha3_based:                                        
            self.slot_types[reg]=self.get_reg_slot_type(arg1)+self.get_reg_slot_type(arg3)
        elif arg2_Sha3_based and arg3_Sha3_based:                                        
            self.slot_types[reg]=self.get_reg_slot_type(arg2)+self.get_reg_slot_type(arg3)
        elif arg3_Sha3_based:                                        
            self.slot_types[reg]=self.get_reg_slot_type(arg3)

    def propagate_taint(self, reg, arg1, arg2=None, arg3=None):                    
        if arg3 is not None:
            arg3_tainted = self.isTainted_register(arg3)
        else:
            arg3_tainted=False
        if arg2 is not None:
            arg2_tainted = self.isTainted_register(arg2)
        else:
            arg2_tainted=False
        arg1_tainted = self.isTainted_register(arg1)

        if arg1_tainted and arg2_tainted and arg3_tainted:                                        
            self.taint_register(reg,self.get_reg_taint_source(arg1)+(self.get_reg_taint_source(arg2))+(self.get_reg_taint_source(arg3)))               
        elif arg1_tainted and arg2_tainted:                                        
            self.taint_register(reg,self.get_reg_taint_source(arg1)+(self.get_reg_taint_source(arg2)))                
        elif arg1_tainted:                                        
            self.taint_register(reg,self.get_reg_taint_source(arg1))
        elif arg2_tainted:                                        
            self.taint_register(reg,self.get_reg_taint_source(arg2))
        elif arg1_tainted and arg3_tainted:                                        
            self.taint_register(reg,self.get_reg_taint_source(arg1)+(self.get_reg_taint_source(arg3)))                
        elif arg2_tainted and arg3_tainted:                                        
            self.taint_register(reg,self.get_reg_taint_source(arg2)+(self.get_reg_taint_source(arg3)))                
        elif arg3_tainted:                                        
            self.taint_register(reg,self.get_reg_taint_source(arg3))
            
        self.propagate_sha3_bases(reg, arg1, arg2,arg3)
        self.propagate_slot_types(reg, arg1, arg2,arg3)
        
                                    
def concrete(v):    
    return isinstance(v, numbers.Number)

def addr(expr):
    return expr & (2 ** 160 - 1)


def run_static(program, ssa, path, sinks, code=None, state=None, ctx=None, inclusive=False, defect_type=None,storage_slots=None, storage_sha3_bases=None):    
    tnt =taint()
    state = state or AbstractEVMState(code=code) 
    
    min_timestamp = (datetime.datetime.now() - datetime.datetime(1970, 1, 1)).total_seconds()
    
    max_timestamp = (datetime.datetime(2021, 1, 1) - datetime.datetime(1970, 1, 1)).total_seconds()        

    instruction_count = 0    
    slot_live_access ={}
    slot_access_trace = defaultdict(list)    
    original_path =path
    tainted=False
    sources={}
    sload_bases={}
    sstore_bases={}
    sstore_slots=[]
    storage_slot_type ={}
    target_sink=program[path[-1]].name
    ssa_block =[]    
    ssa_visited_blocks =[]
    all_visited_blocks =[]
    current_ssa_block =None
    current_block =None
    function = [f for f in ssa.functions][0]    

    path_ssa_ins_args=[arg for b in path for block in function if block.offset ==b for ins in block.insns for arg in ins.arguments if arg.writer is not None]                                                        

    while state.pc in program:                        
        state.trace.append(state.pc)        
        instruction_count += 1

        # have we reached the end of our path?
        if ((inclusive and len(path) == 0)
                or (not inclusive and path == [state.pc])):                                                
            ssa_ins =[s for s in ssa_block if s.offset ==state.pc]                             
            
            if state.pc in sinks.keys():                                                                            
                if defect_type in set(['Storage-Tainting']):                                                                                
                    check_taint=False           
                    
                    if ssa_ins[0].arguments[0]._writer is None:
                        if ssa_ins[0].arguments[0].concrete_value in storage_slots or ssa_ins[0].arguments[0].concrete_value in list(storage_sha3_bases.values()):                        
                            check_taint=True                           
                    elif ssa_ins[0].arguments[0]._writer is not None:                      
                        if tnt.registers[ssa_ins[0].arguments[0]] in storage_slots or tnt.registers[ssa_ins[0].arguments[0]] in list(storage_sha3_bases.values()) or(set(tnt.get_reg_sha3_bases(ssa_ins[0].arguments[0])) & set(storage_slots+list(storage_sha3_bases.values()))):
                            check_taint=True                                                                       
                    if check_taint:                           
                        for i in sinks[state.pc]:     
                            if tnt.isTainted_register(ssa_ins[0].arguments[i]):                                                                                                            
                                tainted=True                            
                                sources=tnt.get_reg_taint_source(ssa_ins[0].arguments[i])                                                        
                                break                                                                                                     
                else:                    
                    for i in sinks[state.pc]:     
                        if tnt.isTainted_register(ssa_ins[0].arguments[i]):                                                                                                            
                            tainted=True                            
                            sources=tnt.get_reg_taint_source(ssa_ins[0].arguments[i])                                                        
                            break        

            state.success = True                        
            return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases, sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)            

        # if not, have we reached another step of our path
        elif state.pc == path[0]:               
            ##get_ssa_block
            ssa_block=[ins for block in function if block.offset ==path[0] for ins in block.insns]                                                                    
            if current_ssa_block is not None:
                ssa_visited_blocks.append(current_ssa_block)
            if current_block is not None:
                all_visited_blocks.append(current_block)
            if len(ssa_block)!=0:
                current_ssa_block=path[0]
            else:
                current_ssa_block=None                            
            current_block=path[0]
            path = path[1:]                            
        elif state.pc in path and program[state.pc].bb.start==state.pc:            
            ssa_block=[ins for block in function if block.offset ==state.pc for ins in block.insns]                                                                    
            if current_ssa_block is not None:
                ssa_visited_blocks.append(current_ssa_block)
            if current_block is not None:
                all_visited_blocks.append(current_block)
            if len(ssa_block)!=0:
                current_ssa_block=state.pc
            else:
                current_ssa_block=None                
            current_block=state.pc
            path = path[path.index(program[state.pc].bb.start)+1:]
            
        elif (program[state.pc].bb.start==state.pc and program[state.pc].bb.ancestors) and state.pc not in[b.offset for b in ssa_block] and state.pc not in path:                                                            
            state.success = False                
            return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)                                                
        
        ins = program[state.pc]
        opcode = ins.op 
        op = ins.name        
        ##get_ssa_ins               
        ssa_ins =[ins for ins in ssa_block if ins.offset ==state.pc]     
        if len(ssa_ins) ==0 and op not in (['POP','JUMP','JUMPDEST']) and op[:3]!='DUP' and  op[:4]!='SWAP' and not (0x60 <= opcode <= 0x7f):            
            if len([ins for block in function for ins in block.insns if ins.offset ==state.pc])==0:                
                state.success = False                        
                return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases, sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)                   
        # Valid operations        
        if (op == 'JUMPDEST' and len(ssa_ins)!=0) or (ins.addr==ins.bb.start and len(ssa_ins)!=0 and str(ssa_ins[0].insn)=='PHI'):                
                #manage PHI statement                           
                for insn in ssa_ins:                                                              
                    if len(insn.arguments)!=0:
                        stack_args=[]
                        concrete_args =[]
                        last_visited=-1                  
                        ssa_last_visited=-1
                        for i in range(len(insn.arguments)):
                            if insn.arguments[i]._writer is not None and insn.arguments[i].writer.parent_block.offset in ssa_visited_blocks:                                
                                stack_args.append(all_visited_blocks.index(insn.arguments[i].writer.parent_block.offset))
                            elif insn.arguments[i]._writer is None and insn.arguments[i].coming_from in all_visited_blocks:                                
                                concrete_args.append(all_visited_blocks.index(insn.arguments[i].coming_from))
                        if len(stack_args)!=0:
                            ssa_last_visited = all_visited_blocks[max(stack_args)]    
                        if len(concrete_args)!=0:
                            last_visited = all_visited_blocks[max(concrete_args)]    
                        c=0
                        for i in range(len(insn.arguments)):
                            if ssa_last_visited > last_visited:
                                if insn.arguments[i]._writer is not None and insn.arguments[i].writer.parent_block.offset ==ssa_last_visited:                                                                
                                    if insn.arguments[i] in tnt.registers:
                                        tnt.registers[insn._return_value]=tnt.registers[insn.arguments[i]]
                                    else:
                                        state.success = False
                                        return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)                                                
                                    tnt.propagate_taint(insn._return_value,insn.arguments[i])                                
                                    c=c+1
                                    break
                            elif ssa_last_visited <= last_visited:
                                if insn.arguments[i]._writer is None and insn.arguments[i].coming_from ==last_visited:                                                                                                                                        
                                    tnt.registers[insn._return_value]=insn.arguments[i].concrete_value                                                                                        
                                    c=c+1
                                    break
                        if c==0:                                                                                                  
                                non_constant=[f.writer.parent_block.offset for f in insn.arguments if f.writer is not None]
                                constant=[f.coming_from for f in insn.arguments if f.writer is None]
                                if len(insn.arguments)==len(non_constant)+len(constant):
                                    if (len(set(non_constant) & set(ssa_visited_blocks))==0) and (len(set(constant) & set(all_visited_blocks))==0):
                                        if len(constant)==1 and len(non_constant)==0:
                                            tnt.registers[insn._return_value]=insn.arguments[0].concrete_value                                                                                                                                                                        
                                        else:                         
                                            if insn._return_value not in path_ssa_ins_args:                    
                                                tnt.registers[insn._return_value]=None    
                                            else:
                                                state.success = False
                                                return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)                                                
                                if insn._return_value not in tnt.registers.keys():                                                                        
                                    state.success = False
                                    return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)                                                
                    else:                        
                        tnt.registers[insn._return_value] =55                                 
        elif 0x60 <= opcode <= 0x7f:            
            state.pc += opcode - 0x5f  
        elif opcode < 0x10:
            if op == 'STOP':                
                state.success = True
                return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)            
            
            elif op == 'ADD':
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])
                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value                    
                else:                                
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:                        
                    arg1 = ssa_ins[0].arguments[1].concrete_value                                                
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]                                        
                    if ssa_ins[0].arguments[1]._writer.insn.name =='SLOAD' and len(hex(arg0)) ==66:
                        if ssa_ins[0].arguments[1]._writer.arguments[0]._writer is None:
                            tnt.sha3_bases[ssa_ins[0]._return_value]= [ssa_ins[0].arguments[1]._writer.arguments[0].concrete_value]                                    
                            tnt.slot_types[ssa_ins[0]._return_value]='A'

                tnt.registers[ssa_ins[0]._return_value]= arg0 + arg1                
                
            elif op == 'SUB':
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])                                
                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value                    
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:                        
                    arg1 = ssa_ins[0].arguments[1].concrete_value                                                
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value]= arg0 - arg1                                

            elif op == 'MUL':                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])
                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value                    
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:                        
                    arg1 = ssa_ins[0].arguments[1].concrete_value                                                
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value]= arg0 * arg1
                                
            elif op == 'DIV':                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])
                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value                    
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:                        
                    arg1 = ssa_ins[0].arguments[1].concrete_value                                                
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]
        
                tnt.registers[ssa_ins[0]._return_value]=int(arg0 // arg1 if arg1 !=0 else 0)                        
                
            elif op == 'MOD':                                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])
                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value                    
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:                        
                    arg1 = ssa_ins[0].arguments[1].concrete_value                                                
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]
        
                tnt.registers[ssa_ins[0]._return_value]=int(arg0 % arg1 if arg1 !=0 else 0)                        
                
            elif op == 'SDIV':                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])
                                
                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = src.util.utils.to_signed(ssa_ins[0].arguments[0].concrete_value)
                    if ssa_ins[0].arguments[1]._writer is None:                        
                        arg1 = src.util.utils.to_signed(ssa_ins[0].arguments[1].concrete_value)                        
                    else:                        
                        arg1 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[1]])                    
                else:
                    arg0 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[0]])
                    if ssa_ins[0].arguments[1]._writer is None:                        
                        arg1 = src.util.utils.to_signed(ssa_ins[0].arguments[1].concrete_value)                                                
                    else:
                        arg1 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[1]])
                tnt.registers[ssa_ins[0]._return_value]=int(abs(arg0) // abs(arg1) * (-1 if arg0 * arg1 < 0 else 1) if arg1 !=0 else 0)                                                

            elif op == 'SMOD':                                                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = src.util.utils.to_signed(ssa_ins[0].arguments[0].concrete_value)
                else:
                    arg0 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[0]])
                    
                if ssa_ins[0].arguments[1]._writer is None:                        
                    arg1 = src.util.utils.to_signed(ssa_ins[0].arguments[1].concrete_value)                        
                else:                        
                    arg1 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[1]])                    
                
                tnt.registers[ssa_ins[0]._return_value]=int(abs(arg0) % abs(arg1) * (-1 if arg0 < 0 else 1) if arg1 !=0 else 0)                                                

            elif op == 'ADDMOD':                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1], ssa_ins[0].arguments[2])

                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value                    
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:                        
                    arg1 = ssa_ins[0].arguments[1].concrete_value                                                
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                if ssa_ins[0].arguments[2]._writer is None:                        
                    arg2 = ssa_ins[0].arguments[2].concrete_value                                                
                else:
                    arg2 = tnt.registers[ssa_ins[0].arguments[2]]

                tnt.registers[ssa_ins[0]._return_value]=int((arg0 + arg1) % arg2  if arg2 else 0)                                                

            elif op == 'MULMOD':                                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1], ssa_ins[0].arguments[2])

                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value                    
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:                        
                    arg1 = ssa_ins[0].arguments[1].concrete_value                                                
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                if ssa_ins[0].arguments[2]._writer is None:                        
                    arg2 = ssa_ins[0].arguments[2].concrete_value                                                
                else:
                    arg2 = tnt.registers[ssa_ins[0].arguments[2]]

                tnt.registers[ssa_ins[0]._return_value]=int((arg0 * arg1) % arg2  if arg2 else 0)                                                
            elif op == 'EXP':                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])
                
                if ssa_ins[0].arguments[0].writer is None:
                    base = ssa_ins[0].arguments[0].concrete_value
                else:
                    base = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    exponent = ssa_ins[0].arguments[1].concrete_value
                else:
                    exponent = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value]= pow(base, abs(exponent), src.util.utils.TT256)
                                
            elif op == 'SIGNEXTEND':                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                if arg0 <= 31:
                    testbit = arg0 * 8 + 7
                    if arg1 & (1 << testbit):
                        tnt.registers[ssa_ins[0]._return_value]= (arg1 | (src.util.utils.TT256 - (1 << testbit)))
                    else:
                        tnt.registers[ssa_ins[0]._return_value] = (arg1 & ((1 << testbit) - 1))
                else:
                    tnt.registers[ssa_ins[0]._return_value]=arg1
        
        elif opcode < 0x20:
            if op == 'LT':                              
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value] =(1 if arg0 < arg1 else 0)                
                
            elif op == 'GT':                        
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])
                
                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:                    
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]
                
                tnt.registers[ssa_ins[0]._return_value] =(1 if arg0 > arg1 else 0)                

            elif op == 'SLT':                    
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = src.util.utils.to_signed(ssa_ins[0].arguments[0].concrete_value)
                else:
                    arg0 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[0]])
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = src.util.utils.to_signed(ssa_ins[0].arguments[1].concrete_value)
                else:
                    arg1 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[1]])

                tnt.registers[ssa_ins[0]._return_value] =(1 if arg0 < arg1 else 0)                

            elif op == 'SGT':                    
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = src.util.utils.to_signed(ssa_ins[0].arguments[0].concrete_value)
                else:
                    arg0 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[0]])
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = src.util.utils.to_signed(ssa_ins[0].arguments[1].concrete_value)
                else:
                    arg1 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[1]])

                tnt.registers[ssa_ins[0]._return_value] =(1 if arg0 > arg1 else 0)                

            elif op == 'EQ':            
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]
                
                tnt.registers[ssa_ins[0]._return_value] =(1 if arg0 == arg1 else 0)                
                            
            elif op == 'ISZERO':                               
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0])
                
                if(ssa_ins[0].arguments[0]._writer) is None:                
                    tnt.registers[ssa_ins[0]._return_value] =(1 if ssa_ins[0].arguments[0].concrete_value==0 else 0)
                else:
                    tnt.registers[ssa_ins[0]._return_value] =(1 if tnt.registers[ssa_ins[0].arguments[0]]==0 else 0)                        
                
            elif op == 'AND':          
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:                    
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value] = arg0 & arg1
                
            elif op == 'OR':            
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value] = arg0 | arg1                

            elif op == 'XOR':                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value] = arg0 ^ arg1

            elif op == 'NOT':        
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0])

                if ssa_ins[0].arguments[0]._writer is None:
                    tnt.registers[ssa_ins[0]._return_value] = ~ssa_ins[0].arguments[0].concrete_value 
                else:
                    tnt.registers[ssa_ins[0]._return_value] = ~tnt.registers[ssa_ins[0].arguments[0]]

            elif op == 'BYTE':                
                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                if arg0 >= 32:
                    tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0])
                    tnt.registers[ssa_ins[0]._return_value]=0
                else:
                    tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])
                    tnt.registers[ssa_ins[0]._return_value]= ((arg1 // 256 ** (31 - arg0)) % 256)
                                    
            elif op == 'SHL':                                            
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value] =arg1 << arg0
                                
            elif op == 'SHR':
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])                
                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.registers[ssa_ins[0]._return_value] =arg1 >> arg0
                
            elif op == 'SAR':                
                tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1])

                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if ssa_ins[0].arguments[1].writer is None:
                    arg1 = src.util.utils.to_signed(ssa_ins[0].arguments[1].concrete_value)
                else:
                    arg1 = src.util.utils.to_signed(tnt.registers[ssa_ins[0].arguments[1]])

                tnt.registers[ssa_ins[0]._return_value] =arg1 >> arg0
                        
        elif opcode < 0x40:
            if op == 'SHA3':                        
                if ssa_ins[0].arguments[0].writer is None: 
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                                
                base=src.util.utils.bytes_to_int(tnt.get_mem(arg0,arg0+32))
                slot_live_access[base]=slot_live_access.get(base,1)-1
                slot_access_trace[base]=slot_access_trace[base][:-1]
                
                data=src.util.utils.bytearray_to_bytestr(tnt.get_mem(arg0,arg0+32))
                tnt.registers[ssa_ins[0]._return_value] = src.util.utils.big_endian_to_int(src.util.utils.sha3(data))                
                if ssa_ins[0].arguments[1].writer is None:  
                    tnt.sha3_bases[ssa_ins[0]._return_value]= [src.util.utils.bytes_to_int(tnt.get_mem(arg0,arg0+32))]
                    tnt.slot_types[ssa_ins[0]._return_value]='A'
                else:
                    size = tnt.registers[ssa_ins[0].arguments[1]]
                    if size>32: 
                        slot_loc=size-32    
                        tnt.sha3_bases[ssa_ins[0]._return_value]= [src.util.utils.bytes_to_int(tnt.get_mem(slot_loc,slot_loc+32))]
                        tnt.slot_types[ssa_ins[0]._return_value]='M'
                    else: #it is an array
                        tnt.sha3_bases[ssa_ins[0]._return_value]= [src.util.utils.bytes_to_int(tnt.get_mem(arg0,arg0+32))]
                        tnt.slot_types[ssa_ins[0]._return_value]='U'
                
                if tnt.isTainted_memory(arg0):                        
                    tnt.taint_register(ssa_ins[0]._return_value,tnt.get_mem_taint_source(arg0))                            

            elif op == 'ADDRESS':                
                tnt.registers[ssa_ins[0]._return_value] =tnt.address
                
            elif op == 'BALANCE':                
                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                if arg0 not in tnt.balance:
                    tnt.balance[arg0]=0

                tnt.registers[ssa_ins[0]._return_value]=tnt.balance[arg0]
                                
            elif op == 'ORIGIN':
                tnt.taint_register(ssa_ins[0]._return_value,[{op:None}])
                tnt.registers[ssa_ins[0]._return_value]=tnt.origin

            elif op == 'CALLER':
                tnt.taint_register(ssa_ins[0]._return_value,[{op:None}])
                tnt.registers[ssa_ins[0]._return_value]=tnt.caller

            elif op == 'CALLVALUE': 
                tnt.taint_register(ssa_ins[0]._return_value,[{op:None}])               

                tnt.registers[ssa_ins[0]._return_value]=tnt.callvalue    
            elif op == 'CALLDATALOAD': 
                tnt.taint_register(ssa_ins[0]._return_value,[{op:None}])                               
                if ssa_ins[0].arguments[0].writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
                tnt.calldata[arg0:arg0 + 32]=bytes([0]) *(31)+ b'\x20'                     
                tnt.registers[ssa_ins[0]._return_value]=src.util.utils.bytearray_to_int(tnt.calldata[arg0:arg0 + 32])                
                
            elif op == 'CALLDATASIZE': 
                tnt.taint_register(ssa_ins[0]._return_value,[{op:None}])                               
                tnt.registers[ssa_ins[0]._return_value]=256  
            elif op == 'CALLDATACOPY':  
                if ssa_ins[0].arguments[2]._writer is None:
                    size=ssa_ins[0].arguments[2].concrete_value
                else:
                    size= tnt.registers[ssa_ins[0].arguments[2]]

                if ssa_ins[0].arguments[1]._writer is None:
                    dstart=ssa_ins[0].arguments[1].concrete_value
                else:
                    dstart= tnt.registers[ssa_ins[0].arguments[1]]

                if ssa_ins[0].arguments[0]._writer is None:
                    mstart=ssa_ins[0].arguments[0].concrete_value
                else:
                    mstart= tnt.registers[ssa_ins[0].arguments[0]]
                                
                for i in range(size):
                    if dstart + i < len(tnt.calldata):                                                
                        tnt.memory[mstart+i]=tnt.calldata[dstart + i]
                        tnt.tMemory.append([mstart+i, [{op:None}]])  
                    else:
                        tnt.memory[mstart+i]=0
                        tnt.tMemory.append([mstart+i, [{op:None}]])  
            elif op == 'CODESIZE':                
                tnt.registers[ssa_ins[0]._return_value]=1  
            elif op == 'CODECOPY':
                if ssa_ins[0].arguments[2]._writer is None:
                    arg2 = ssa_ins[0].arguments[2].concrete_value
                else:
                    arg2 = tnt.registers[ssa_ins[0].arguments[2]]

                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                
            elif op == 'RETURNDATACOPY':
                if ssa_ins[0].arguments[2]._writer is None:
                    size=ssa_ins[0].arguments[2].concrete_value
                else:
                    size= tnt.registers[ssa_ins[0].arguments[2]]

                if ssa_ins[0].arguments[1]._writer is None:
                    bstart=ssa_ins[0].arguments[1].concrete_value
                else:
                    bstart= tnt.registers[ssa_ins[0].arguments[1]]

                if ssa_ins[0].arguments[0]._writer is None:
                    mstart=ssa_ins[0].arguments[0].concrete_value
                else:
                    mstart= tnt.registers[ssa_ins[0].arguments[0]]
                for i in range(size):
                    if bstart + i < len(tnt.returndata):                        
                        tnt.memory[mstart+i]=tnt.returndata[bstart + i]                        
                    else:
                        tnt.memory[mstart+i]=0                        

            elif op == 'RETURNDATASIZE':
                tnt.registers[ssa_ins[0]._return_value]=1    
            elif op == 'GASPRICE':
                tnt.registers[ssa_ins[0]._return_value]=tnt.gasprice                
            elif op == 'EXTCODESIZE':  
                tnt.taint_register(ssa_ins[0]._return_value,[{op:None}])               
                tnt.registers[ssa_ins[0]._return_value]=1    
            elif op == 'EXTCODECOPY':  
                if ssa_ins[0].arguments[2]._writer is None:
                    arg2 = ssa_ins[0].arguments[2].concrete_value
                else:
                    arg2 = tnt.registers[ssa_ins[0].arguments[2]]

                if ssa_ins[0].arguments[0]._writer is None:
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                                    
                for i in range(arg2):                    
                    tnt.tMemory.append([arg0+i, [{op:None}]])  
        
        elif opcode < 0x50:
            if op == 'BLOCKHASH':                
                tnt.registers[ssa_ins[0]._return_value]=tnt.blockhash     
            elif op == 'COINBASE':
                tnt.registers[ssa_ins[0]._return_value]=tnt.coinbase                
            elif op == 'TIMESTAMP':        
                tnt.registers[ssa_ins[0]._return_value]=tnt.timestamp     
            elif op == 'NUMBER':
                tnt.registers[ssa_ins[0]._return_value]=tnt.number        
            elif op == 'DIFFICULTY':
                tnt.registers[ssa_ins[0]._return_value]=tnt.difficulty   
            elif op == 'GASLIMIT':
                tnt.registers[ssa_ins[0]._return_value]=tnt.gaslimit
        elif opcode < 0x60:
            if op == 'POP':
               pass               
            elif op == 'MLOAD':                                                     
                if ssa_ins[0].arguments[0]._writer is None:            
                    arg0=ssa_ins[0].arguments[0].concrete_value                   
                    tnt.registers[ssa_ins[0]._return_value] =src.util.utils.bytes_to_int(tnt.get_mem(arg0,arg0+32)) * (-1 if arg0 in tnt.signed_memory else 1)                
                    if tnt.isTainted_memory(arg0):                        
                        tnt.taint_register(ssa_ins[0]._return_value,tnt.get_mem_taint_source(arg0))                            
                else:
                    arg0=tnt.registers[ssa_ins[0].arguments[0]]
                    try:                        
                        tnt.registers[ssa_ins[0]._return_value] =src.util.utils.bytes_to_int(tnt.get_mem(arg0,arg0+32)) * (-1 if arg0 in tnt.signed_memory else 1)                                                                                       
                    except KeyError:
                        for k in range(arg0,arg0+32):                     
                            tnt.memory[k]=0                  
                        tnt.registers[ssa_ins[0]._return_value] =src.util.utils.bytes_to_int(tnt.get_mem(arg0,arg0+32))                                                                       
                    if tnt.isTainted_memory(arg0):
                        tnt.taint_register(ssa_ins[0]._return_value, tnt.get_mem_taint_source(arg0))                                                        
            elif op == 'MSTORE':     
                if ssa_ins[0].arguments[0]._writer is None:
                    arg0=ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0= tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:                    
                    arg1=ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1= tnt.registers[ssa_ins[0].arguments[1]]
                if arg1<0:
                    tnt.signed_memory.append(arg0)
                    arg1=abs(arg1)                            
                tmp=src.util.utils.encode_int32(arg1)                                
                t=0
                for k in range(arg0,arg0+32):
                    tnt.memory[k]=tmp[t]
                    t+=1
                        
                if ssa_ins[0].arguments[1]._writer is not None:
                    if tnt.isTainted_register(ssa_ins[0].arguments[1]):                        
                        for i in range(arg0,arg0+32):
                            tnt.tMemory.append([i,tnt.get_reg_taint_source(ssa_ins[0].arguments[1])])                   
            elif op == 'MSTORE8':                
                if ssa_ins[0].arguments[0]._writer is None:
                    arg0=ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0= tnt.registers[ssa_ins[0].arguments[0]]

                if ssa_ins[0].arguments[1]._writer is None:
                    arg1=ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1= tnt.registers[ssa_ins[0].arguments[1]]
                tnt.memory[arg0]= arg1%256
                
                if ssa_ins[0].arguments[1]._writer is not None:
                    if tnt.isTainted_register(ssa_ins[0].arguments[1]):                        
                        tnt.tMemory.append([arg0,tnt.get_reg_taint_source(ssa_ins[0].arguments[1])])                                                     
            elif op == 'SLOAD': 
                if ssa_ins[0].arguments[0]._writer is None:                    
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]

                slot_live_access[arg0] = slot_live_access.get(arg0,0)+1
                slot_access_trace[arg0].append(ins)
                tnt.registers[ssa_ins[0]._return_value] =tnt.storage.get(arg0,0)
                tnt.taint_register(ssa_ins[0]._return_value,[{op+'-'+str(ins.addr):arg0}])                                   

                if ssa_ins[0].arguments[0]._writer is not None:                         
                    tnt.propagate_sha3_bases(ssa_ins[0]._return_value, ssa_ins[0].arguments[0])
                    tnt.propagate_slot_types(ssa_ins[0]._return_value, ssa_ins[0].arguments[0])
                    loc_bases=tnt.get_reg_sha3_bases(ssa_ins[0].arguments[0])
                    loc_type=tnt.get_reg_slot_type(ssa_ins[0].arguments[0])
                    if len(loc_bases)!=0:
                        sload_bases[arg0]=loc_bases[0]
                    if len(loc_type)!=0:
                        storage_slot_type[arg0]=loc_type[0]

            elif op == 'SSTORE':                
                if ssa_ins[0].arguments[0]._writer is None:                    
                    arg0 = ssa_ins[0].arguments[0].concrete_value
                else:
                    arg0 = tnt.registers[ssa_ins[0].arguments[0]]
                if ssa_ins[0].arguments[1]._writer is None:                    
                    arg1 = ssa_ins[0].arguments[1].concrete_value
                else:
                    arg1 = tnt.registers[ssa_ins[0].arguments[1]]

                tnt.storage[arg0]=arg1                        
                                
                if ssa_ins[0].arguments[1]._writer is not None:
                    if tnt.isTainted_register(ssa_ins[0].arguments[1]):
                        tnt.tStorage.append([arg0,tnt.get_reg_taint_source(ssa_ins[0].arguments[1])])                                                        

                slot_live_access[arg0]=0
                slot_access_trace[arg0].append(ins)                                            
                        
            elif op == 'JUMP':                
                if len(ssa_block)!=0:
                    if ssa_ins[0].arguments[0]._writer is None:
                        state.pc = ssa_ins[0].arguments[0].concrete_value
                    else:
                        state.pc = tnt.registers[ssa_ins[0].arguments[0]]
                    if len(str(state.pc)) ==77:
                        state.pc=path[0]

                    if state.pc not in original_path:                        
                        state.success = False
                        return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)            
                    if state.pc >= len(state.code) or not program[state.pc].name == 'JUMPDEST':
                        state.success = False
                        return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)                                            
                else:
                    state.pc = path[0]
                continue                                
            elif op == 'JUMPI':                          
                state.pc = path[0]
                continue
            elif op == 'PC':
                tnt.registers[ssa_ins[0]._return_value]=state.pc

            elif op == 'MSIZE':
                tnt.registers[ssa_ins[0]._return_value]=len(tnt.memory)
            elif op == 'GAS':               
                tnt.registers[ssa_ins[0]._return_value]=7000  
                
        elif op[:3] == 'DUP':    
            pass
        elif op[:4] == 'SWAP':            
            pass
        elif op[:3] == 'LOG': 
            pass 
        elif op == 'CREATE':
            tnt.registers[ssa_ins[0]._return_value]=1 
        # Calls
        elif op in ('CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL'):
            tnt.propagate_taint(ssa_ins[0]._return_value, ssa_ins[0].arguments[0], ssa_ins[0].arguments[1],ssa_ins[0].arguments[2])
            
            tnt.registers[ssa_ins[0]._return_value]=1            
        elif op == 'RETURN': 
            state.success = True            
            return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)                        

        elif op == 'REVERT':  
            return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)            

        elif op == 'SELFDESTRUCT':            
            state.success = True                
            return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)            
            
        state.pc += 1                                   
    state.success = True
    return TainitAnalysisResult(state,defect_type,target_sink,tainted,sources,sload_bases,sstore_bases,sstore_slots,slot_live_access,slot_access_trace, storage_slot_type)            

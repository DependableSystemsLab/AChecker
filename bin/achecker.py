#!/usr/bin/env python3
import json
import logging
import resource
import sys
import argparse
import subprocess
import os
import shlex
import re
from collections import deque
from src.project import Project
from src.cfg import opcodes
from src.slicing import interesting_slices, slice_to_program
from src.explorer.forward import ForwardExplorer
import src.cfg.rattle as rattle
from collections import defaultdict
from src.memory import resolve_all_memory
from src.flow.analysis_results import AnalysisBugDetails
from src.evm.results import CombinedSymbolicResult
import src.flow.code_info as cinfo
from src.storage import resolve_all_storage
from src.flow.symbolic import validate_path
from src.evm.exceptions import TimeoutException

logging.basicConfig(level=logging.INFO)

def hex_encode(d):
    return {k: v.hex() if isinstance(v, bytes) else v for k, v in d.items()}

def extract_bin_str(s):
    ''' 
    Extracts binary representation of smart contract from solc output.
    '''
    binary_regex = r"\r?\n======= (.*?) =======\r?\nBinary of the runtime part:\r?\n(.*?)\r?\n" 
    contracts = re.findall(re.compile(binary_regex), s.decode("utf-8"))
    contracts = [contract for contract in contracts if contract[1]]    
    if not contracts:
        logging.critical("Solidity compilation failed")
        print ("======= error =======")
        print ("Solidity compilation failed")
        print ("Check the used solc compiler version")
        exit()
    return contracts

def link_libraries(filename, libs):
    '''
    Compiles contract in filename and links libs by calling solc --link. Returns binary representation of linked contract.
    '''
    option = ""
    for idx, lib in enumerate(libs):
        lib_address = "0x" + hex(idx+1)[2:].zfill(40)
        option += " --libraries %s:%s" % (lib, lib_address)
    FNULL = open(os.devnull, 'w')
    cmd = "solc --bin-runtime %s" % filename
    p1 = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE, stderr=FNULL)
    cmd = "solc --link%s" %option
    p2 = subprocess.Popen(shlex.split(cmd), stdin=p1.stdout, stdout=subprocess.PIPE, stderr=FNULL)
    p1.stdout.close()
    out = p2.communicate()[0]
    return extract_bin_str(out)

def get_evm(contract):
    
    cmd = "solc --bin-runtime %s" % contract    
    FNULL = open(os.devnull, 'w')
    solc_p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE, stderr=FNULL)
    out= solc_p.communicate()[0]    
    #libs = re.findall(re.compile(r"_+(.*?)_+"), out.decode("utf-8"))
    #libs = set(libs)
    #if libs:        
    #    return link_libraries(contract, libs)
    #else:        
    #    return extract_bin_str(out)
    return extract_bin_str(out)

def analysis(p, initial_storage=dict(), sym_validation= None,
                    mode=None, initial_balance=None,
                    max_calls=3, controlled_addrs=set(), flags=None):

    user_alerts = {'Violated-AC-Check':'Violated access control check', \
                    'Missing-AC-Check':'Missing access control check', \
                    'acsbl_sdestruct': 'Non protected SELFDESTRUCT', \
                    'SELFDESTRUCT':'Controlable Address of SELFDESTRUCT', \
                    'DELEGATECALL':'Controlable Target of DELEGATECALL'}
    flags = flags or set(opcodes.CRITICAL)    
    ##convert_to_ssa
    sys.setrecursionlimit(10000)
    ssa = rattle.Recover(bytes.hex(p.code).encode(), edges=p.cfg.edges(), split_functions=False)      
    memory_info = resolve_all_memory(p.cfg, p.code)        
    storage_info = resolve_all_storage(p.cfg, p.code, memory_info)                                      
    violated_ac_count =0
    missing_ac_count = 0
    violated_ac_ib_count = 0    
    
    ac_checks_sloads = []            
    for defect_type in list(['Violated-AC-Check','Missing-AC-Check']):
        print("Checking contract for \033[4m{0}\033[0m ".format(defect_type))
        print("------------------")                    
        ins=[]
        taintedBy = []

        if not taintedBy:
            taintedBy=opcodes.potentially_user_controlled                                              
        if defect_type in (['Violated-AC-Check']):                
            ins = p.cfg.filter_ins('JUMPI', reachable=True)
            restricted=True
            if not ins:
                continue
            ins_type = set(s.name for s in ins).pop()            
            args = opcodes.CRITICAL_ARGS[ins_type] 
            sinks={s.addr: opcodes.CRITICAL_ARGS[ins_type] for s in ins}            

            tainted_sstores = defaultdict(list)                                        
            ac_checks_with_sloads, slices, imap, other_ac_cehcks = p.resolve_access_control_slots(ssa, ins, ac_check_ins=opcodes.ins_in_ac_check, args=args, memory_info=memory_info, restricted=restricted)            
            sstores = p.cfg.filter_ins('SSTORE', reachable=True)                                 
            ac_sload_slots = []

            for k in ac_checks_with_sloads:
                ac_checks_sloads.extend([ins for ins in [s['sload'] for s in ac_checks_with_sloads[k]] if ins in storage_info])                                                                                                                           
            ac_sload_slots = list(set([s for ins in ac_checks_sloads if ins in storage_info for s in storage_info[ins].reads]))            
            ac_sload_sha3_bases = {s:storage_info[ins].read_sha3_bases[s] for ins in ac_checks_sloads if ins in storage_info for s in storage_info[ins].reads if storage_info[ins].read_sha3_bases}                                                                  
            
            s_temp=[ins for ins in sstores if ins in storage_info and storage_info[ins].writes.union(set(storage_info[ins].write_sha3_bases.values())) & set(ac_sload_slots+list(ac_sload_sha3_bases.values()))]                            
            sstores =s_temp                                                            
            sstore_sinks={s.addr:[1] for s in sstores}  
            sstore_taintedBy=opcodes.potentially_direct_user_controlled            
            sload_sha3_bases= ac_sload_sha3_bases 
            
            for s, sstore_slot_sbyte, sstore_struct_offset, s_path, s_r in p.extract_paths(ssa, sstores, sstore_sinks, sstore_taintedBy, defect_type='Storage-Tainting', args=[1], storage_slots=ac_sload_slots,storage_sha3_bases=sload_sha3_bases, restricted=True):                
                logging.debug("%s: %s", 'SSTORE', s)
                logging.debug("Path: %s", '->'.join('%x' %p for p in s_path))                                                                              
                if s_r._tainted:  
                    tainted_sstores[s]=s_path                
                #break                         
            tainted_sstores_tmp = []
            for jump_ins in ac_checks_with_sloads:                
                current_ac_check_slots = [s for ins in [s['sload'] for s in ac_checks_with_sloads[jump_ins]] if ins in storage_info for s in storage_info[ins].reads]                                                                                                            
                current_ac_check_slot_sha3_bases = [ac_sload_sha3_bases[slot] for slot in current_ac_check_slots if len(str(slot))>5 and slot in ac_sload_sha3_bases]                 
                current_ac_check_slot_sbyte = [{'slot':s,'sbyte':sload['sbyte']} for s in current_ac_check_slots if len(str(s))<5  for sload in ac_checks_with_sloads[jump_ins]]                                                                                                                            
                current_ac_check_struct_offset = [sload['structOffset'] for s in current_ac_check_slots for sload in ac_checks_with_sloads[jump_ins]]                                                                                                                            
                current_ac_check_slots_sstores = [ins for ins in storage_info if ins.name=='SSTORE' and storage_info[ins].writes & set(current_ac_check_slots)]                                
                for sstore_ins in tainted_sstores:                                                            
                    current_sstore_slot = [s for s in storage_info[sstore_ins].writes]                                                    
                    if set(current_sstore_slot)& set([s['slot'] for s in current_ac_check_slot_sbyte]):                                                
                        if not set([sstore_slot_sbyte[sstore_ins]]).union({'whole'}) & set([s['sbyte'] for s in current_ac_check_slot_sbyte]):           
                            tainted_sstores_tmp.append(sstore_ins)                            
                    current_sstore_slot_sha3_base = [storage_info[sstore_ins].write_sha3_bases[s] for s in current_sstore_slot if len(str(s))>5 and s in storage_info[sstore_ins].write_sha3_bases]                    
                    if set(current_sstore_slot)& set([s['slot'] for s in current_ac_check_slot_sbyte]) or \
                        set(current_ac_check_slot_sha3_bases)& set(current_sstore_slot_sha3_base):                                                
                        if sstore_struct_offset[sstore_ins] not in current_ac_check_struct_offset:                                          
                            tainted_sstores_tmp.append(sstore_ins)
            
            for ins in set(tainted_sstores_tmp):
                del tainted_sstores[ins]
            tainted_sstores_tmp = []                    
            checked_tainted_sstores= []
            not_tainted_sstore =[]
            resolve_later = deque(ins for ins in tainted_sstores)
            todo = deque()    
            progress= True            
            while todo or (progress and resolve_later):
                if not todo:
                    todo = resolve_later
                    resolve_later = deque()
                    progress = False                    
                sstore_ins = todo.popleft()
                logging.debug("%s: %s", 'SSTORE', sstore_ins)
                logging.debug("Path: %s", '->'.join('%x' % p for p in tainted_sstores[sstore_ins]))                      
                sstore_path_ac_checks = [ins for ins in storage_info if ins in ac_checks_sloads and ins.bb.start in tainted_sstores[sstore_ins][:-1]]
                sstore_path_other_ac_checks = [ins for ins in other_ac_cehcks if ins.bb.start in tainted_sstores[sstore_ins][:-1]]
                
                if len(sstore_path_ac_checks)==0 and len(sstore_path_other_ac_checks)==0:                    
                    if sym_validation: 
                        try:                       
                            taint_valid_results= validate_path(p, tainted_sstores[sstore_ins])                                                                                            
                        except TimeoutException:                
                            raise TimeoutException("Timed out!")                        
                        if taint_valid_results:                                                        
                            checked_tainted_sstores.append(sstore_ins)
                        else: 
                            not_tainted_sstore.append(sstore_ins)                            
                    else:
                        checked_tainted_sstores.append(sstore_ins)                
                else:                    
                    other_access_sanitizers =[slot for ins in sstore_path_ac_checks for slot in storage_info[ins].reads]                                                                                                                                                                                                                                                                        
                    other_access_sanitizers_sstores = [ins for ins in storage_info if ins.name=='SSTORE' and storage_info[ins].writes & set(other_access_sanitizers)]                                         
                    if set(other_access_sanitizers_sstores) & set(checked_tainted_sstores):                                                   
                        if sym_validation:                            
                            taint_valid_results = validate_path(p, tainted_sstores[sstore_ins])                                                
                            if taint_valid_results:                                                           
                                checked_tainted_sstores.append(sstore_ins)
                            else: 
                                not_tainted_sstore.append(sstore_ins)
                        else:
                            checked_tainted_sstores.append(sstore_ins)                        
                        continue
                    if set(other_access_sanitizers_sstores) & set(not_tainted_sstore): 
                        not_tainted_sstore.append(sstore_ins)                        
                        continue
                    if tainted_sstores.keys() & set(other_access_sanitizers_sstores) != set(other_access_sanitizers_sstores):
                        not_tainted_sstore.append(sstore_ins)                    
                        continue                                            
                    if tainted_sstores.keys() & set(other_access_sanitizers_sstores): 
                        sstore_fun_sig = cinfo.get_function_sig(p.cfg, tainted_sstores[sstore_ins],'id')
                        other_tainted_santizers_sstores = [ins for ins in tainted_sstores.keys() if set([ins]) & set(other_access_sanitizers_sstores) and sstore_fun_sig!=cinfo.get_function_sig(p.cfg, tainted_sstores[ins],'id')]                                                                
                        if other_tainted_santizers_sstores and set(other_tainted_santizers_sstores)&set(checked_tainted_sstores)==set(other_tainted_santizers_sstores):                            
                            if sym_validation:                                
                                taint_valid_results= validate_path(p, tainted_sstores[sstore_ins])                                
                                if taint_valid_results:                                    
                                    checked_tainted_sstores.append(sstore_ins)
                                else: 
                                    not_tainted_sstore.append(sstore_ins)
                            else:
                                checked_tainted_sstores.append(sstore_ins)                            
                            continue                                                                                                        
                        else:
                            resolve_later.append(sstore_ins)                                                
            checked_access_paths = defaultdict(list)                                                                       
            for i, i_path in p.extract_control_paths(slices, imap):
                logging.debug("%s: %s", ins_type, i)
                logging.debug("Path: %s", '->'.join('%x' % p for p in i_path))                                                                                                
                current_ac_check_slots = [s for ins in [s['sload'] for s in ac_checks_with_sloads[i]] if ins in storage_info for s in storage_info[ins].reads]                                                                                            
                current_ac_check_slot_sbyte = [{'slot':s,'sbyte':sload['sbyte']} for s in current_ac_check_slots if len(str(s))<5  for sload in ac_checks_with_sloads[i]]                                                                                                            
                current_ac_check_slots_sha3_bs = [ac_sload_sha3_bases[slot] for slot in current_ac_check_slots if len(str(slot))>5 and slot in ac_sload_sha3_bases]
                current_ac_check_slots_sstores = [ins for ins in storage_info if ins.name=='SSTORE' and storage_info[ins].writes & set(current_ac_check_slots) or set(storage_info[ins].write_sha3_bases.values()) & set(current_ac_check_slots_sha3_bs)]                
                ac_function= cinfo.get_function_sig(p.cfg, i_path)
                reported= False   
                IntendedB = False                          
                for sstore_ins in current_ac_check_slots_sstores:                                        
                    if sstore_ins in checked_tainted_sstores: 
                        current_sstore_slot = [s for s in storage_info[sstore_ins].writes]                                                    
                        current_sstore_slot_sha3_bs = [storage_info[sstore_ins].write_sha3_bases[s] for s in storage_info[sstore_ins].writes if len(str(s))>5]
                        sstore_slot = list(set(current_sstore_slot) if len(str(current_sstore_slot[0]))<=5 else set(current_sstore_slot_sha3_bs))                                                
                        sstore_in_function= cinfo.get_function_sig(p.cfg, tainted_sstores[sstore_ins])
                        if ac_function+'-'+ sstore_in_function+'-'+str(sstore_slot[0]) in checked_access_paths[sstore_slot[0]]:                                                     
                            continue                                                                                    
                        checked_access_paths[sstore_slot[0]].append(ac_function +'-'+ sstore_in_function+'-'+str(sstore_slot[0]))                                                        
                        logging.debug("%s", sstore_ins)
                        logging.debug("Path: %s", '->'.join('%x' % p for p in tainted_sstores[sstore_ins]))                                                                                                            
                        if not reported:                                                                                         
                            print("\n{0} in function {1}".format(user_alerts[defect_type], ac_function))
                            print("\t%s" %i)                                                                                                                                                                                  
                            reported = True                            
                        if mode =='FIntendedB':                                                                                    
                            ac_checks_in_sstore_path = [ins for ins in storage_info if ins in ac_checks_sloads and ins.bb.start in tainted_sstores[sstore_ins][:-1]]                            
                            taint_valid_results =None
                            if len(ac_checks_in_sstore_path)==0: 
                                taint_valid_results= validate_path(p, tainted_sstores[sstore_ins], mode=mode, ac_jumpi=[s.addr for s in ac_checks_with_sloads])                                                                                                        
                            if taint_valid_results:                                                                
                                model, pib = taint_valid_results                                
                                if pib:                                             
                                    violated_ac_ib_count+=1
                                    IntendedB = True
                                    print("+--(Potentially Intended Behavior) Attacker can make changes to AC item {0} in function {1}".format(set(sstore_slot), sstore_in_function))                                                    
                                    continue                                                        
                        print("+--Attacker can make changes to AC item {0} in function {1}".format(set(sstore_slot), sstore_in_function))
                if reported and not IntendedB:
                    violated_ac_count+=1

            print("\n")                        
        elif defect_type in (['Missing-AC-Check']):                
            kill_ins= p.cfg.filter_ins('SELFDESTRUCT', reachable=True)
            call_ins= p.cfg.filter_ins('DELEGATECALL', reachable=True)
            ins = [*kill_ins, *call_ins]             
            if not ins:        
                continue
            ins_types= list(set(s.name for s in ins)) + ['acsbl_sdestruct']                       
            for ins_type in ins_types :                                            
                if ins_type=='acsbl_sdestruct': #accessible selfdestruct
                    args = opcodes.CRITICAL_ARGS['SELFDESTRUCT'] 
                    sub_ins = kill_ins                    
                    sinks={}                    
                    restricted=True
                else:
                    args = opcodes.CRITICAL_ARGS[ins_type]     
                    sub_ins =set([s for s in ins if s.name == ins_type])                                                              
                    sinks={s.addr: opcodes.CRITICAL_ARGS[ins_type] for s in sub_ins}            
                    restricted=True                            
                if taintedBy ==[]:
                    taintedBy=opcodes.potentially_user_controlled                                                                          
                
                tainted_ins = defaultdict(list)
                tainting_loc= defaultdict(list)                                           
                ins_with_preceded_ac = []
                for j, j_ins_slot_sbyte, j_ins_struct_offset, j_path, j_r in p.extract_paths(ssa, sub_ins, sinks, taintedBy, defect_type=defect_type, args=args, restricted=restricted, memory_info=None):
                    logging.debug("%s: %s", ins_type, j)
                    logging.debug("Path: %s", '->'.join('%x' %p for p in j_path))
                    if ins_type in (['SELFDESTRUCT','DELEGATECALL']) and j_r._tainted:                                                
                        if j in ins_with_preceded_ac:
                            continue                                                                        
                        if j in tainted_ins: 
                            continue
                        if any(k for i in j_r.sources for k,v in i.items() if k.split('-',1)[0]!='SLOAD'):                                                                                                                 
                            ins_path_ac_checks = [ins for ins in storage_info if ins in ac_checks_sloads and ins.bb.start in j_path[:-1]]                                                                                                                                                                                                                                                    
                            if len(ins_path_ac_checks)!=0:
                                ins_with_preceded_ac.append(j)
                                continue                            
                            tainted_ins[j]= {"path":j_path,"type":ins_type}            
                        else:                               
                            sload_slots= [v for i in j_r.sources for k,v in i.items() if k.split('-',1)[0]=='SLOAD']                                                                                        
                            sload_sha3_bases= {i:j_r.sload_sha3_bases[i] for i in j_r.sload_sha3_bases if i in sload_slots}                                                                                                                                                    
                            sstores = p.cfg.filter_ins('SSTORE', reachable=True)                                                                                                         
                            sstore_sinks={s.addr:[1] for s in sstores}                              
                            sstore_taintedBy=opcodes.potentially_direct_user_controlled                                   
                            for js, js_sstore_slot_sbyte, js_sstore_struct_offset, js_path, js_r in p.extract_paths(ssa, sstores, sstore_sinks, sstore_taintedBy, defect_type='Storage-Tainting', args=[1], storage_slots=sload_slots,storage_sha3_bases=sload_sha3_bases, restricted=True):                                                                                                
                                if js_r._tainted and (set([j_ins_slot_sbyte[j]])&set([js_sstore_slot_sbyte[js]])):                                                                                                                                                    
                                    ins_path_ac_checks = [ins for ins in storage_info if ins in ac_checks_sloads and ins.bb.start in js_path[:-1]]                                                                                                                                                                                                                        
                                    if len(ins_path_ac_checks)!=0:
                                        ins_with_preceded_ac.append(j)
                                        continue                                    
                                    tainted_ins[j]={"path":j_path,"type":ins_type} 
                                    tainting_loc[j]=js_path 
                                    break 
                    elif ins_type in (['acsbl_sdestruct']):                                                                                                                                            
                        tainted_ins[j]={"path":j_path,"type":ins_type}                
                                
                checked_ins_paths = defaultdict(list)                                                                           
                for s in tainted_ins:                    
                    logging.debug("%s", s)
                    logging.debug("Path: %s", '->'.join('%x' % p for p in tainted_ins[s]["path"]))                                                                                                    
                    ac_function= cinfo.get_function_sig(p.cfg, tainted_ins[s]["path"],'id')                                 
                    MissingIntendedB = False
                    if ac_function+'-'+str(s.addr) in checked_ins_paths[s.addr]:                                                     
                        continue                          
                    if tainting_loc[s]:
                        if sym_validation:
                            taint_valid_results = validate_path(p, tainting_loc[s])                    
                            if not taint_valid_results:                                                                                           
                                continue                            
                        ins_path_ac_checks = [ins for ins in storage_info if ins in ac_checks_sloads and ins.bb.start in tainting_loc[s][:-1]]                                                                                                                                                                                                                                                
                        ins_path_other_ac_checks = [ins for ins in other_ac_cehcks if ins.bb.start in tainting_loc[s][:-1]]
                        tainting_path=tainting_loc[s]
                    else:
                        ins_path_ac_checks = [ins for ins in storage_info if ins in ac_checks_sloads and ins.bb.start in tainted_ins[s]["path"][:-1]]
                        ins_path_other_ac_checks = [ins for ins in other_ac_cehcks if ins.bb.start in tainted_ins[s]["path"][:-1]]
                        tainting_path=tainted_ins[s]["path"]

                    if len(ins_path_ac_checks)==0 and len(ins_path_other_ac_checks)==0:                        
                        checked_ins_paths[s.addr].append(ac_function+'-'+str(s.addr))                            
                        logging.debug("%s", s)
                        logging.debug("Path: %s", '->'.join('%x' % p for p in tainted_ins[s]["path"]))                                                                                                                                    
                        logging.debug("Path: %s", '->'.join('%x' %p for p in j_path))                                    
                        print("({0}) {1} in function {2}".format(user_alerts[tainted_ins[s]["type"]], user_alerts[defect_type],cinfo.get_function_sig(p.cfg, tainting_path)))  
                        print("Needed to protect following instruction in function {0}".format(cinfo.get_function_sig(p.cfg,tainted_ins[s]["path"])))
                        print("%s\n" %s)  
                        if not MissingIntendedB:
                            missing_ac_count+=1
                
    return AnalysisBugDetails(violated_ac_count, missing_ac_count, violated_ac_ib_count)
def main():
    parser = argparse.ArgumentParser()
    grp = parser.add_mutually_exclusive_group(required=True)
    grp.add_argument("-f", "--file", type=str,
                       help="Code source file. Solidity by default. Use -b to process evm instead.")

    parser.add_argument(
        "-b", "--bytecode", help="read EVM bytecode in source instead of solidity file.", action="store_true")

    parser.add_argument(
        "--initial_storage_file", help="initial storage file")

    parser.add_argument(
        "-sf", "--savefile")

    parser.add_argument(
        "-m", "--memory", help="Max memory limit")

    parser.add_argument(
        "-fib", "--fib", help="Filter out intended behavior cases.", action="store_true")

    parser.add_argument(
        "-sv", "--sv", help="Validation through symbolic execution", action="store_true")
    
    args = parser.parse_args()
    
    if args.file is None:
        print('Usage: %s  <-f file>   [--memory] [--savefile]' % \
              sys.argv[0], file=sys.stderr)
        exit(-1)
    
    savefilebase = args.savefile or args.file     
    if args.memory:
        mem_limit = int(args.memory) * 1024 * 1024 * 1024
    else:
        # limit default memory to 6GB
        mem_limit = 6 * 1024 * 1024 * 1024
    try:
        rsrc = resource.RLIMIT_VMEM
    except:
        rsrc = resource.RLIMIT_AS
    resource.setrlimit(rsrc, (mem_limit, mem_limit)) 
   
    #symbolic_validation= True if args.sv else False
    symbolic_validation= True
    #mode = 'FIntendedB' if args.fib else None
    mode = 'FIntendedB' 
    
    initial_storage = dict()
    if args.initial_storage_file:
        with open(args.initial_storage_file, 'rb') as f:
            initial_storage = {int(k, 16): int(v, 16) for k, v in json.load(f).items()}

    if not args.bytecode:
        contracts = get_evm(args.file)

        # Analyze each contract
        for cname, bin_str in contracts:
            print("Contract {0}:".format(cname))                    
            print("------------------\n")            
            code = bytes.fromhex(bin_str)                        
            p = Project(code)            
            analysis(p, initial_storage, sym_validation =symbolic_validation, mode=mode)            
    else:
        with open(args.file)  as infile:
            inbuffer = infile.read().rstrip()            
        code = bytes.fromhex(inbuffer)                
        p = Project(code)        
        analysis(p, initial_storage, sym_validation =symbolic_validation, mode=mode)
            
    
if __name__ == '__main__':
    main()

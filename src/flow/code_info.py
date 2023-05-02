import os, sys
import logging

def get_function_sig(cfg,path, type='name'):    
    #bbs= {bb.start:ins.arg.hex() for bb in p.cfg.bbs for ins in bb.ins if bb.start in path[:-1] and ins.name =='PUSH4' and p.cfg._ins_at[ins.addr+ins.op-0x5f+1].name=='EQ'}
    logging.debug("Path: %s", '->'.join('%x' % p for p in path))                                                    
    bbs= {bb:ins.arg.hex() for bb in path[:-1] for ins in cfg._bb_at[bb].ins  if ins.name =='PUSH4' and ins.arg.hex() !='ffffffff' and cfg._ins_at[ins.addr+ins.op-0x5f+1].name=='EQ' and int.from_bytes(cfg._ins_at[ins.addr+ins.op-0x5f+2].arg,'big')==path[path.index(bb)+1]}    
    other_bbs= {bb:ins.arg.hex() for bb in path[:-1] for ins in cfg._bb_at[bb].ins  if ins.name =='PUSH4' and ins.arg.hex() !='ffffffff' and ins.addr+ins.op-0x5f+2 in cfg._ins_at and cfg._ins_at[ins.addr+ins.op-0x5f+2].name=='EQ' and int.from_bytes(cfg._ins_at[ins.addr+ins.op-0x5f+3].arg,'big')==path[path.index(bb)+1]}    
    bbs.update(other_bbs)
    #print(bbs)
    bbs_indices=[path.index(bb) for bb in bbs.keys()]    
    if len(bbs_indices)!=0 and type=='name':           
        with open(os.path.join(os.path.join(os.getcwd(),"src/flow"),"FSignatures.txt"), 'r') as f:      
            fsig=dict(x.rstrip().split(None,1) for x in f)  
        return fsig.get('0x'+str(bbs[path[max(bbs_indices)]]),bbs[path[max(bbs_indices)]])
    elif len(bbs_indices)==0 and type=='name':
        return '() payable'
    elif len(bbs_indices)!=0 and type=='id':
        return str(bbs[path[max(bbs_indices)]])
    elif len(bbs_indices)==0 and type=='id':
        return '0'
    elif len(bbs_indices)!=0 and type=='bb':
        return path[max(bbs_indices)]
    elif len(bbs_indices)==0 and type=='bb':
        return 0

def function_restricted_caller(p, path):    
    bbs_check_caller= [bb.start for bb in p.cfg.bbs for ins in bb.ins if bb.start in path[:-2] and len(bb.succ_addrs)>=2 and ins.name in ['CALLER', 'ORIGIN'] and (bb.ins[bb.ins.index(ins)+3].name=='EQ' or bb.ins[bb.ins.index(ins)+1].name=='EQ' or bb.ins[-3].name=='EQ')]
    if len(bbs_check_caller)!=0:
        return True
    return False

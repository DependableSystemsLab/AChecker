from collections import deque

from src.cfg.opcodes import storage_reads, storage_writes
import src.util.utils
from src.evm.exceptions import TimeoutException


class InconsistentSlot(Exception):
    pass

class UninitializedRead(Exception):
    def __init__(self, index, *args):
        super(UninitializedRead, self).__init__(*args)
        if isinstance(index, slice):
            self.start = index.start or 0
            self.end = index.stop
        else:
            self.start = index
            self.end = index + 1

    def __repr__(self):
        return '%s from: %d to %d' % (super(UninitializedRead, self).__repr__(), self.start, self.end)

    def __str__(self):
        return '%s from: %d to %d' % (super(UninitializedRead, self).__repr__(), self.start, self.end)


class StorageInfo(object):
    def __init__(self, reads, writes, read_sha3_bases, write_sha3_bases):
        self.reads = reads
        self.writes = writes
        self.read_sha3_bases= read_sha3_bases
        self.write_sha3_bases= write_sha3_bases

def get_storage_info(ins, code, memory_info=None):
    from .slicing import backward_slice, slice_to_program
    from .evm.evm import run
    from .evm.state import EVMState
    from .evm.exceptions import ExternalData
    from .util.intrange import Range
    targets = []

    read = False
    write = False

    if ins.name in storage_reads:
        read = True
        read_slot_info = storage_reads[ins.name]        
        if read_slot_info < 0:
            targets.append(-1 - read_slot_info)
       
    if ins.name in storage_writes:
        write = True
        write_slot_info = storage_writes[ins.name]        
        if write_slot_info < 0:
            targets.append(-1 - write_slot_info)
       
    if not read and not write:
        return None
    bs = backward_slice(ins, targets, memory_info)
    read_slot = set()
    read_slot_sha3_base= dict()
    write_slot = set()
    write_slot_sha3_base= dict()
    for b in bs:
        try:
            state = run(slice_to_program(b), EVMState(code=code), check_initialized=False)                                                
        except UninitializedRead as e:
            raise e
        except ExternalData as e:
            raise e
        if read:
            new_slot = state.stack[read_slot_info] if read_slot_info < 0 else read_slot_info                                                           
            if new_slot not in read_slot:
                read_slot.add(new_slot)
                sha3_ins=[ins for ins in b if ins.name=='SHA3']                
                mstore_ins=[ins for ins in b if ins.name=='MSTORE']                
                if len(sha3_ins)==1 and len(mstore_ins)==1: 
                    read_slot_sha3_base[new_slot]=src.util.utils.bytearray_to_int(state.memory[0:32])
                elif len(sha3_ins)>=1 and len(mstore_ins)>=2: 
                    read_slot_sha3_base[new_slot]=src.util.utils.bytearray_to_int(state.memory[32:64])                                                                            
        if write:
            new_slot = state.stack[write_slot_info] if write_slot_info < 0 else write_slot_info                        
            if new_slot not in write_slot:
                write_slot.add(new_slot)     
                sha3_ins=[ins for ins in b if ins.name=='SHA3']                
                mstore_ins=[ins for ins in b if ins.name=='MSTORE']
                if len(sha3_ins)==1 and len(mstore_ins)==1: 
                    write_slot_sha3_base[new_slot]=src.util.utils.bytearray_to_int(state.memory[0:32])
                elif len(sha3_ins)>=1 and len(mstore_ins)>=2: 
                    write_slot_sha3_base[new_slot]=src.util.utils.bytearray_to_int(state.memory[32:64])                                                            
    return StorageInfo(read_slot, write_slot,read_slot_sha3_base,write_slot_sha3_base)


def resolve_all_storage(cfg, code, memory_info=None):
    storage_infos = dict()
    resolve_later = deque(
        ins for bb in cfg.bbs for ins in bb.ins if ins.name in storage_reads or ins.name in storage_writes)
    todo = deque()    
    progress = True    
    while todo or (progress and resolve_later):
        if not todo:
            todo = resolve_later
            resolve_later = deque()
            progress = False
        ins = todo.popleft()        
        try:            
            mi = get_storage_info(ins, code, memory_info)                                                        
            if mi:                             
                progress = True
                storage_infos[ins] = mi
        except TimeoutException:                
            raise TimeoutException("Timed out!")
        except Exception as e:
            resolve_later.append(ins)
    return storage_infos

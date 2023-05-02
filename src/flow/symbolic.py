import itertools
import logging
from collections import defaultdict
#from py import code

from z3 import z3
from src import cfg

from src.cfg import opcodes
from src.constraints import check_model_and_resolve, model_to_calls
from src.evm.exceptions import IntractablePath, TimeoutException
from src.evm.results import CombinedSymbolicResult
from src.util.z3_extra_util import concrete
from src.flow import code_info as cinfo

class InfeasibleExploit(Exception):
    pass


class ExploitContext(object):
    def __init__(self, target_addr, shellcode_addr, target_amount, amount_check, initial_balance, initial_storage,
                 controlled_addrs=set()):
        self.target_addr = target_addr
        self.shellcode_addr = shellcode_addr
        self.target_amount = target_amount
        self.amount_check = amount_check
        self.initial_balance = initial_balance
        self.initial_storage = initial_storage

        # assume we control the target address
        self.controlled_addrs = controlled_addrs | {target_addr}


def exploit_constraints_call(r, ctx):
    addr = r.state.stack[-2]
    if not concrete(addr):
        addr = z3.simplify(addr)

    amount = r.state.stack[-3]
    if not concrete(amount):
        amount = z3.simplify(amount)

    extra_constraints = []

    if not concrete(addr):
        extra_constraints.append(z3.Extract(159, 0, addr) == ctx.target_addr)
    else:
        if addr != ctx.target_addr:
            raise InfeasibleExploit

    if not concrete(amount):
        if ctx.amount_check == '+':
            extra_constraints.append(z3.UGE(amount, ctx.target_amount))
        elif ctx.amount_check == '-':
            extra_constraints.append(z3.UGT(amount, 0))
            extra_constraints.append(z3.ULE(amount, ctx.target_amount))
        else:
            extra_constraints.append(amount == ctx.target_amount)
        final_balance = r.state.balance
        extra_constraints.append(z3.ULE(amount, final_balance))

    # ensure we're not spending more for this exploit than we gain
    total_spent = None
    for res in r.results:
        callvalue = z3.BitVec('CALLVALUE_%d' % res.xid, 256)
        extra_constraints.append(z3.ULE(callvalue, 10 * (10 ** 18)))  # keep it semi-reasonable: at most 10 Eth per call
        if total_spent is None:
            total_spent = callvalue
        else:
            total_spent += callvalue

    extra_constraints.append(z3.ULT(total_spent, amount))

    # also, ensure the contract does not require a unreasonable start-balance (>100 Eth)
    if not ctx.initial_balance:
        start_balance = z3.BitVec('BALANCE_%d' % r.results[0].xid, 256)
        extra_constraints.append(z3.ULE(start_balance, 100 * (10 ** 18)))

    return extra_constraints


def exploit_constraints_callcode(r, ctx):
    addr = z3.simplify(r.state.stack[-2])

    extra_constraints = []

    if not concrete(addr):
        extra_constraints.append(z3.Extract(159, 0, addr) == ctx.shellcode_addr)
    else:
        if addr != ctx.shellcode_addr:
            raise InfeasibleExploit

    return extra_constraints


def exploit_constraints_delegatecall(r, ctx):
    addr = z3.simplify(r.state.stack[-2])

    extra_constraints = []

    if not concrete(addr):
        extra_constraints.append(z3.Extract(159, 0, addr) == ctx.shellcode_addr)
    else:
        if addr != ctx.shellcode_addr:
            raise InfeasibleExploit

    return extra_constraints


def exploit_constraints_selfdestruct(r, ctx):
    addr = z3.simplify(r.state.stack[-1])

    extra_constraints = []

    if not concrete(addr):
        extra_constraints.append(z3.Extract(159, 0, addr) == ctx.target_addr)
    else:
        if addr != ctx.target_addr:
            raise InfeasibleExploit

    return extra_constraints


EXPLOIT_CONSTRAINTS = {
    'CALL': exploit_constraints_call,
    'CALLCODE': exploit_constraints_callcode,
    'DELEGATECALL': exploit_constraints_callcode,
    'SELFDESTRUCT': exploit_constraints_selfdestruct
}


def get_exploit_constraints(r, ctx):
    target_op = r.results[-1].target_op    
    if target_op in EXPLOIT_CONSTRAINTS:
        return EXPLOIT_CONSTRAINTS[target_op](r, ctx)
    else:
        return []


def control_address_constraints(sym_addr, controlled_addrs):
    sub_exprs = [sym_addr == controlled_addr for controlled_addr in controlled_addrs]
    expr = sub_exprs[0]
    for sub_expr in sub_exprs[1:]:
        expr = z3.Or(expr, sub_expr)    
    return expr

def attempt_exploit(results, ctx):
    c = CombinedSymbolicResult()
    for r in results[::-1]:        
        c.prepend(r)
    c.combine(ctx.initial_storage, ctx.initial_balance)
    c.simplify()
    extra_constraints = get_exploit_constraints(c, ctx)

    for res in c.results:
        origin = z3.BitVec('ORIGIN_%d' % res.xid, 256)
        caller = z3.BitVec('CALLER_%d' % res.xid, 256)
        # ensure we control the origin
        #extra_constraints.append(control_address_constraints(origin, ctx.controlled_addrs))
        # and ensure the caller is either the origin or the shellcode address
        #extra_constraints.append(control_address_constraints(caller, {origin, ctx.shellcode_addr}))
    try:
        model = check_model_and_resolve(c.constraints + extra_constraints, c.sha_constraints)
                
        # enforce we control all ORIGIN-addresses
        if any(model[v].as_long() not in ctx.controlled_addrs for v in model if v.name().startswith('ORIGIN')):
            raise InfeasibleExploit

        return model_to_calls(model, c.idx_dict), c, model
    except TimeoutException:                
            raise TimeoutException("Timed out!")
    except IntractablePath:
        raise InfeasibleExploit


def validate_path(p, path, mode=None, ac_jumpi=None):    
    target_addr= int('0x1234', 16)
    shellcode_addr= int('0x1000', 16), +1000
    target_amount= +1000
    amount_check='+'
    initial_storage=dict()
    initial_balance=None
    max_calls=3
    controlled_addrs=set()

    fun_sig_bb = cinfo.get_function_sig(p.cfg, path,'bb')    
    code_path = path[path.index(fun_sig_bb)+2:-1]    
    if fun_sig_bb==0: #most probably payable()                
        c=0
        while (fun_sig_bb==0 and c+1<len(path)):            
            bb=path[c]
            if bb==0:
                c=c+1
                continue    
            bb_ins=[ins.name for ins in p.cfg._bb_at[bb].ins]
            if not set(bb_ins)& set(['CALLDATALOAD','CALLDATACOPY','CALLDATASIZE']) and \
                bb_ins != ['DUP1','PUSH4','EQ','PUSH2','JUMPI']:
                fun_sig_bb=bb
                code_path=path[path.index(fun_sig_bb):-1]
                break    
            else:
                c=c+1                
    ctx = ExploitContext(target_addr, shellcode_addr, target_amount, amount_check, initial_balance, initial_storage,
                         controlled_addrs)
    try:        
        symbolic_constr =p.run_symbolic(path, mode=mode, code_path=code_path, ac_jumpi=ac_jumpi)                                                                      
    except TimeoutException:                
            raise TimeoutException("Timed out!")
    except Exception:
        return 'error', None
    critical_paths = []
    try:        
        results = attempt_exploit([symbolic_constr], ctx)        
        if results:
            call, r, model = results

        return model, symbolic_constr.possible_intended_behavior
    except TimeoutException:                
            raise TimeoutException("Timed out!")
    except InfeasibleExploit:
        pass


from miasm.analysis.machine import Machine
from miasm.arch.x86.arch import mn_x86
from miasm.ir.symbexec import SymbolicExecutionEngine
from miasm.expression.expression import ExprInt, ExprMem, ExprId, LocKey
from miasm.arch.x86.regs import *
from miasm.analysis.binary import Container
from miasm.ir.ir import IntermediateRepresentation, AssignBlock
from miasm.expression.expression import ExprAssign, ExprOp
from miasm.expression.expression import ExprCond, ExprId, ExprInt, ExprMem
from miasm.expression.simplifications import expr_simp
from miasm.core import parse_asm, asmblock
from miasm.loader.strpatchwork import *
from miasm.ir.translators.translator import Translator
from future.utils import viewitems
from argparse import ArgumentParser
import sys, z3
import warnings
import r2pipe

parser = ArgumentParser("X-Tunnel Opaque Predicate Fixer")
parser.add_argument("target", help="Target binary")
parser.add_argument("addr", help="Target address")
parser.add_argument("--architecture", "-a", help="Force architecture")
args = parser.parse_args()

def check_path_feasibility(conds):
    solver = z3.Solver()
    for lval, rval in conds:
        z3_cond = Translator.to_language("z3").from_expr(lval)
        solver.add(z3_cond == int(rval.arg))

    rslt = solver.check()

    if rslt == z3.sat:
        return True
    else:
        return False

def remove_xtunnel_op(lockeys, asmcfg):
    # Opening File in r2
    r2 = r2pipe.open("./x-tunnel.bin", ["-w"])
    
    # applying reference analysis
    r2.cmd("aar")
    
    # iterating for each block label 
    for lbl in lockeys:
        # retrieving block for label
        asmblk = asmcfg.loc_key_to_block(lbl)
        if asmblk:
            for l in asmblk.lines:
                # seeking to address of instruction
                r2.cmd("s %s" % hex(l.offset))

                # checking if there is any xrefs to
                # current instruction
                xref = r2.cmdj("axtj")
                if  xref:
                    # retrieving the reference source address 
                    xref_from = xref[0]['from']
                   
                    # retrieving the opcode 
                    opcode = xref[0]['opcode']

                    # seeking to refrence source address
                    r2.cmd("s %s" % hex(xref_from))

                    # changing opcode for nop if its a je or a non 
                    # conditional jump if its any other branch instruction
                    r2.cmd("wao %s" % ("nop" if 'je' in opcode else "nocj"))

                # seek back to original block instrution
                r2.cmd("s %s" % hex(l.offset))
                
                # patching instruction with a nop
                r2.cmd("wao nop")
                
                # seeking to previous instruction
                r2.cmd("so -1")
                
                # retrieving its opcode
                opcode = r2.cmdj("pdj 1")[0]['opcode']

                # if its a jne, change it to its
                # non-conditional form
                if 'jne' in opcode:
                    r2.cmd("wao nocj")
                    
class FinalState:
    def __init__(self, result, sym, path_conds, path_history):
        self.result = result
        self.sb = sym
        self.path_conds = path_conds
        self.path_history = path_history

# Explore IRCFG for conditional branches and compute feasibility
def explore(ir, start_addr, start_symbols,
        ircfg, cond_limit=30, uncond_limit=100,
        lbl_stop=None, final_states=[]):

    def codepath_walk(addr, symbols, conds, depth, final_states, path):
        
        # recursion strict limiter
        if depth >= cond_limit:
            warnings.warn("'depth' is over the cond_limit :%d"%(depth))
            return
        
        # Instantiate MIASM Symbolic Execution Engine
        sb = SymbolicExecutionEngine(ir, symbols)

        for _ in range(uncond_limit):
            if isinstance(addr, ExprInt):
                # recursion limiter
                if addr._get_int() == lbl_stop:
                    final_states.append(FinalState(True, sb, conds, path))
                    return

            # Append all executed Paths
            path.append(addr)
            
            # Run Symbolic Engine at block
            pc = sb.run_block_at(ircfg, addr)
            
            # If IR Instruction is a Comparison
            if isinstance(pc, ExprCond):
                
                # Create conditions to take true or false paths
                cond_true  = {pc.cond: ExprInt(1, 32)}
                cond_false = {pc.cond: ExprInt(0, 32)}

                # Compute the destination addr of the true or false paths
                addr_true  = expr_simp(
                    sb.eval_expr(pc.replace_expr(cond_true), {}))

                addr_false = expr_simp(
                    sb.eval_expr(pc.replace_expr(cond_false), {}))

                # Adding previous conditions of previous blocks in path to reach current block
                conds_true = list(conds) + list(cond_true.items())
                conds_false = list(conds) + list(cond_false.items())

                # Check feasibility of True Condition in conditional Branch
                if check_path_feasibility(conds_true):
                    # If True path is feasible, continue with Symbolic Execution
                    codepath_walk(
                        addr_true, sb.symbols.copy(),
                        conds_true, depth + 1, final_states, list(path))
                else:
                    # If not, store the current block and stop recursion
                    final_states.append(FinalState(False, sb, conds_true, path))

                if check_path_feasibility(conds_false):
                    # If False path is feasible, continue with Symbolic Execution
                    codepath_walk(
                        addr_false, sb.symbols.copy(),
                        conds_false, depth + 1, final_states, list(path))
                else:
                    # If not, store the current block and stop recursion
                    final_states.append(FinalState(False, sb, conds_false, path))

                return
            else:
                # If pc is not a Condition, simplify current block
                # expresion to then symbolicly execute it
                addr = expr_simp(sb.eval_expr(pc))

        # Append Final current final state to
        # final states array
        final_states.append(FinalState(True, sb, conds, path))
        return

    # Start by walking function from its start address
    return codepath_walk(start_addr, start_symbols, [], 0, final_states, [])

# Opening Target File and storing it in a 'Container' object
cont = Container.from_stream(open(args.target, 'rb'))

# Instantiating Disassembler
machine = Machine(args.architecture if args.architecture else cont.arch)
dis = machine.dis_engine(cont.bin_stream, loc_db=cont.loc_db)

# Include this class to specify target function subfunctions calling convention
# since for x86 all arguments are in the stack, we can live this definition empty
class IRAX86FuncCalls(machine.ira):
        def call_effects(self, ad, instr):
            call_assignblk = AssignBlock(
            [

            ],
            instr
        )
            return [call_assignblk], []


# Disassembling and extracting CFG
asmcfg = dis.dis_multiblock(int(args.addr, 0))

# Extracting IR Archive and IRCFG
ir_arch = IRAX86FuncCalls(cont.loc_db)
ircfg = ir_arch.new_ircfg_from_asmcfg(asmcfg)

symbols_init =  {}

# for regs
for i, r in enumerate(all_regs_ids):
    symbols_init[r] = all_regs_ids_init[i]

# 0xdeadbeef is the mark to stop the exploring
symbols_init[ExprMem(ExprId('ESP_init', 32), 32)] = ExprInt(0xdeadbeef, 32)
final_states = []

explore(ir_arch, 
        int(args.addr, 0), 
        symbols_init, 
        ircfg, 
        lbl_stop=0xdeadbeef, 
        final_states=final_states)

executed_lockey   = []
unexecuted_lockey = []

# The IR nodes in final_states array are the path nodes that were executed.
# We collect the 'lock_key' or block labels of each of the nodes executed
for final_state in final_states:
    if final_state.result:
        for node in final_state.path_history:
            if isinstance(node, int):
                lbl = ircfg.get_loc_key(node)
            elif isinstance(node, ExprInt):
                lbl = ircfg.get_loc_key(node._get_int())
            elif isinstance(node, LocKey):
                lbl = node.loc_key
            if lbl not in executed_lockey:
                executed_lockey.append(lbl)

# We then collect the non-executed blocks by comparing the executed ones
# with the totality of the blocks in the IRCFG
for lbl, irblock in viewitems(ircfg.blocks):
    if lbl not in executed_lockey:
        unexecuted_lockey.append(lbl)

print('len(executed_lockey):', len(executed_lockey))
print('len(unexecuted_lockey):', len(unexecuted_lockey))

remove_xtunnel_op(unexecuted_lockey, asmcfg)

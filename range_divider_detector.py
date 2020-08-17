# -*- coding: utf-8 -*-
from miasm.analysis.machine import Machine
from miasm.ir.symbexec import SymbolicExecutionEngine
from miasm.ir.ir import IRCFG
from miasm.expression.expression import LocKey
from miasm.arch.x86.regs import *
from miasm.core import asmblock
from miasm.analysis.binary import Container
from future.utils import viewitems
from miasm.ir.translators.translator import Translator
import networkx as nx
from argparse import ArgumentParser
import random
import z3


def syntax_compare(blk0, blk1):
    # if blocks do not contain the same
    # number of instructions return
    if len(blk0.lines) != len(blk1.lines):
        return False

    # iterate through all instructions in blocks
    for l0, l1 in zip(blk0.lines, blk1.lines):

        # if intruction is a branch
        if str(l0)[0] == 'J':
            # retrieve instruction opcode
            instr0 = str(l0).split(' ')[0]
            instr1 = str(l1).split(' ')[0]
            if instr0 != instr1:
                return False

        # any other instruction
        else:
            if str(l0) != str(l1):
                return False

    return True


def execute_symbolic_execution(src_irb, dst_irb,
                                ir_arch0, ir_arch1,
                                src_ircfg, dst_ircfg,
                                flag_cmp):

    # Initialize symbols for src and dst blocks
    src_symbols = {}
    dst_symbols = {}

    # Initialize symbol context with register context
    for i, r in enumerate(all_regs_ids):
        src_symbols[r] = all_regs_ids_init[i]
        dst_symbols[r] = all_regs_ids_init[i]

    # Instantiate Symbolic Execution Engine for src block
    src_sb = SymbolicExecutionEngine(ir_arch0, src_symbols)

    # for each IR instruction in src block
    for assignblk in src_irb:
        skip_update = False

        # retrieve IR expression and operand in block
        for dst, src in viewitems(assignblk):
            # If operand involves EIP or ret
            if str(dst) in ['EIP', 'IRDst']:
                # skip symbolic execution
                skip_update = True

        # otherwise symbolically execute IR expression
        if not skip_update:
            src_sb.eval_updt_assignblk(assignblk)

    # Instantiate Symbolic Execution Engine for dest block
    dst_sb = SymbolicExecutionEngine(ir_arch1, dst_symbols)

    # retrieve IR expression and operand in block
    for assignblk in dst_irb:
        skip_update = False
        # If operand involves EIP or ret
        for dst, src in viewitems(assignblk):
            if str(dst) in ['EIP', 'IRDst']:
                # skip symbolic execution
                skip_update = True

        if not skip_update:
            # otherwise symbolically execute IR expression
            dst_sb.eval_updt_assignblk(assignblk)

    # set stack top for each symbolic engine
    src_sb.del_mem_above_stack(ir_arch0.sp)
    dst_sb.del_mem_above_stack(ir_arch1.sp)

    # Retrieve all memory accesses from src and dst symbolic engines
    all_memory_ids = [k for k, v in dst_sb.symbols.memory()] + [k for k, v in src_sb.symbols.memory()]

    # iterate through all register and memory symbols
    # from both symbolic engines
    for k in all_regs_ids + all_memory_ids:
        # keep iterating if symbol is EIP
        if str(k) == 'EIP':
            continue

        # keep iterating if symbol is eflags
        if not flag_cmp and k in [zf, nf, pf, of, cf, af, df, tf]:
            continue

        # retrieve value of symbol from each symbolic engine
        v0 = src_sb.symbols[k]
        v1 = dst_sb.symbols[k]

        # keep iterating if symbol is the same
        if v0 == v1:
            continue

        # instantiate z3 SAT solver
        solver = z3.Solver()
        try:
            # translate src symbol constraints to z3 readable form
            z3_r_cond = Translator.to_language('z3').from_expr(v0)
        except NotImplementedError:
            return False

        try:
            # translate dst symbol constraints to z3 readable form
            z3_l_cond = Translator.to_language('z3').from_expr(v1)
        except NotImplementedError:
            return False

        # add equality condition to solver
        solver.add(z3.Not(z3_r_cond == z3_l_cond))

        # if condition was unsatisfiable
        r = solver.check()
        if r == z3.unsat:
            # IR expression were equivalent
            # keep iterating
            continue

        # if condition was satisfiable
        else:
            # blocks are not equivalent
            #print(solver.model()) # Counterexample
            return False
    return True


def semantic_compare(blk0, blk1, ir_arch0, ir_arch1, asmcfg, flag_cmp=False):
    # create empty IR CFG for src block
    src_ircfg = IRCFG(None, ir_arch0.loc_db)
    try:
        # add src block to empty IR CFG
        ir_arch0.add_asmblock_to_ircfg(blk0, src_ircfg)
    except NotImplementedError:
        return False

    # create empty IR CFG for dst block
    dst_ircfg = IRCFG(None, ir_arch1.loc_db)
    try:
        # add dst block to empty IR CFG
        ir_arch1.add_asmblock_to_ircfg(blk1, dst_ircfg)
    except NotImplementedError:
        return False

    # Check if blocks were added to their IRCFG correctly
    if len(src_ircfg.blocks) != len(dst_ircfg.blocks):
        return False


    for src_lbl, dst_lbl in zip(src_ircfg.blocks, dst_ircfg.blocks):
        # retrieve both src and dst blocks from their labels
        src_irb = src_ircfg.blocks.get(src_lbl, None)
        dst_irb = dst_ircfg.blocks.get(dst_lbl, None)

        # symbolically execute them to evaluate
        # semantic equivalence
        r = execute_symbolic_execution(
                            src_irb, dst_irb,
                            ir_arch0, ir_arch1,
                            src_ircfg, dst_ircfg,
                            flag_cmp)
        if r is False:
            return False
    return True

# Return a list containing randomly generated colors
def gen_random_color():
    ret = []

    r = [x for x in range(256)]
    g = [x for x in range(256)]
    b = [x for x in range(256)]
    random.shuffle(r)
    random.shuffle(g)
    random.shuffle(b)

    for a2, a1, a0 in zip(r, g, b):
        color = a2 << 16 | a1 << 8 | a0
        ret.append(color)

    return ret

def main(args):
    # retrieve input file
    with open(args.target, 'rb') as fstream:
        cont = Container.from_stream(fstream)

    # disassemble file
    machine = Machine(args.architecture)
    mdis = machine.dis_engine(cont.bin_stream)

    # create to IR archives, one for each BB pair to compare
    ir_arch0 = machine.ira(mdis.loc_db)
    ir_arch1 = machine.ira(mdis.loc_db)

    # retirev native CFG
    asmcfg = mdis.dis_multiblock(int(args.addr, 0))

    # enumerate all blogs in target function
    target_blocks = []
    for cn, block in enumerate(asmcfg.blocks):
        target_blocks.append(block)

    results = {}

    # iterate over all blocks to select src block
    for src_blk in target_blocks:
        # retrieve src block label from src block
        src_ldl = src_blk._loc_key

        # Skip a basic blocks containing only single instruction
        if len(src_blk.lines) == 1 and src_blk.lines[0].dstflow():
            continue

        # iterate through all blocks again
        # to select dst block
        for dst_blk in target_blocks:
            # retrieve dst block label from dst block
            dst_ldl = dst_blk._loc_key

            # Skip a basic block containing only single instruction
            if len(dst_blk.lines) == 1 and dst_blk.lines[0].dstflow():
                continue

            # Skip if src and dst block are the same block
            if src_ldl == dst_ldl:
                continue

            # Skip If src and dst blocks have already been matched
            if (src_ldl, dst_ldl) in results.keys() or \
                    (dst_ldl, src_ldl) in results.keys():
                continue

            # Check for syntax equality
            r_syntax = syntax_compare(src_blk, dst_blk)

            if r_syntax:
                # If the syntax of two blocks is same, then the semantics of them is also same.
                r_semantic = True
            else:
                # Check for semantic equality
                r_semantic = semantic_compare(src_blk, dst_blk, ir_arch0, ir_arch1, asmcfg)

            # save results of syntax and semantic checks
            results[(src_ldl, dst_ldl)] = [(r_syntax, r_semantic)]

    # create graph
    G = nx.Graph()
    # add nodes
    G.add_nodes_from(target_blocks)

    # add edges based on syntax/semantic similarity
    for k, v in viewitems(results):
        if v[0][0] or v[0][1]:
            G.add_edge(k[0], k[1])

    random_colors = gen_random_color()
    body = ''

    # Iterate through the blocks which are equivalent
    for n, conn_nodes in enumerate(nx.connected_components(G)):

        if len(conn_nodes) == 1:
            continue

        for node in conn_nodes:  # node is asmblk
            # set the same color for equivalent nodes
            if isinstance(node, LocKey):
                asmblk = asmcfg.loc_key_to_block(node)
                if asmblk:
                    for l in asmblk.lines:
                        body += 'SetColor(0x%08x, CIC_ITEM, 0x%x);\n' % (l.offset, random_colors[n])
            else:
                for l in node.lines:
                    body += 'SetColor(0x%08x, CIC_ITEM, 0x%x);\n' % (l.offset, random_colors[n])

    header = '''
#include <idc.idc>
static main()
{
'''
    footer = '''
}
'''
    f = open('eq-color.idc', 'w')
    f.write(header + body + footer)
    f.close()


if __name__ == '__main__':
    parser = ArgumentParser("Range Divider Detector")
    parser.add_argument("target", help="Target binary")
    parser.add_argument("addr", help="Target address")
    parser.add_argument("--architecture", "-a", help="Force architecture")
    args = parser.parse_args()
    main(args)

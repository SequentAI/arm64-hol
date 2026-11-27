#!/usr/bin/env python3
"""Assemble and execute single-instruction probes on native AArch64."""
import argparse
from collections import Counter
from pathlib import Path
import platform
import re
import subprocess
import tempfile


L3_INTEGER_FORMS = {
    "cbz", "mov", "movz", "addext", "ldrb", "add", "cmp", "bne", "ret", "br",
    "stpx", "stpx_regs", "stpx_zero", "nop", "addsp", "ldrb_sp", "blr",
}

# Literal probes ("literal" mode) read a pool placed 48 bytes before the
# probe and 12 bytes after it (past the probe's two closing instructions);
# the HOL test state maps the same bytes at those offsets from PC 256.
LITERAL_POOL = [(0x35 + 0x9d * i) & 0xFF for i in range(48)]

# Each expected disassembly is paired with the exact HOL instruction value.
PROBES = {
    "cbz": ("CompareBranch F F 1w 2w", ("cbz w1,8",)),
    "mov": ("LogicalReg T 1w F 0w 2w 31w 0w 0w", ("mov x2,x0", "orr x2,xzr,x0")),
    "movz": ("MoveWide F 2w 0w 0w 0x8001w", ("mov w0,#32769", "movz w0,#32769")),
    "addext": ("AddExtend T F F 2w 3w 2w 1w 0w", ("add x3,x2,w1,uxtw",)),
    "ldrb": ("MemImm F 1w 0w 1w 2w (Unscaled PostIndex 1w)", ("ldrb w1,[x2],#1",)),
    "add": ("AddShift F F F 0w 0w 0w 1w 0w", ("add w0,w0,w1",)),
    "cmp": ("AddShift T T T 0w 31w 2w 3w 0w", ("cmp x2,x3", "subs xzr,x2,x3")),
    "bne": ("BCond 1w 0x7fffdw", ("b.ne -12",)),
    "ret": ("Ret 30w", ("ret", "ret x30")),
    "br": ("Br 1w", ("br x1",)),
    "blr": ("Blr 1w", ("blr x1",)),
    "ldpq": ("MemPair T 2w T Offset 0w 1w 1w 0w", ("ldp q0,q1,[x1]",)),
    "stpq": ("MemPair T 2w F Offset 0w 1w 0w 0w", ("stp q0,q1,[x0]",)),
    "stpx": ("MemPair F 2w F Offset 31w 31w 0w 2w", ("stp xzr,xzr,[x0,#16]",)),
    "movi": ("SimdImm T T 14w 0w 0w", ("movi v0.2d,#0",)),
    "nop": ("Nop", ("nop", "hint #0")),
    "stpx_regs": ("MemPair F 2w F Offset 1w 2w 0w 0w", ("stp x1,x2,[x0]",)),
    "stpx_zero": ("MemPair F 2w F Offset 31w 31w 0w 0w", ("stp xzr,xzr,[x0]",)),
    "addsp": ("AddExtend T F F 2w 31w 31w 1w 0w", ("add sp,sp,w1,uxtw",)),
    "ldrb_sp": ("MemImm F 1w 0w 1w 31w (Unscaled PostIndex 1w)", ("ldrb w1,[sp],#1",)),
    "ldpq_pos": ("MemPair T 2w T Offset 0w 1w 1w 1w", ("ldp q0,q1,[x1,#16]",)),
    "stpq_neg": ("MemPair T 2w F Offset 0w 1w 0w 127w", ("stp q0,q1,[x0,#-16]",)),
}


# Name, decoded instruction, assembly, pointer register, and optional mode
# Branch modes select the target direction, "stack" maps SP into the data
# buffer, "sp_result" captures a raw SP write, and "indexed" supplies X2.
SCALAR_PROBES = [
    ("b", "BranchImm F 2w", "b 1f", -1, "branch"),
    ("bl", "BranchImm T 2w", "bl 1f", -1, "branch"),
    ("blt", "BCond 11w 2w", "b.lt 1f", -1, "branch"),
    ("cbnzw", "CompareBranch F T 1w 2w", "cbnz w1,1f", -1, "branch"),
    ("cbzx", "CompareBranch T F 1w 2w", "cbz x1,1f", -1, "branch"),
    ("cbnzx", "CompareBranch T T 1w 2w", "cbnz x1,1f", -1, "branch"),
    ("tbz", "TestBranch F 31w 1w 2w", "tbz w1,#31,1f", -1, "branch"),
    ("tbnz", "TestBranch T 63w 1w 2w", "tbnz x1,#63,1f", -1, "branch"),
    ("movzx", "MoveWide T 2w 3w 0w 0x8123w", "movz x0,#0x8123,lsl #48", -1, ""),
    ("addimmw", "AddImm F F F F 0w 1w 7w", "add w0,w1,#7", -1, ""),
    ("addimmx", "AddImm T F F T 0w 1w 7w", "add x0,x1,#7,lsl #12", -1, ""),
    ("subimmw", "AddImm F T F F 0w 1w 7w", "sub w0,w1,#7", -1, ""),
    ("subimmx", "AddImm T T F F 0w 1w 7w", "sub x0,x1,#7", -1, ""),
    ("cmpimm", "AddImm F T T F 31w 1w 0w", "cmp w1,#0", -1, ""),
    ("ccmp_x", "CondCompare T T T 0w 9w 8w 2w", "ccmp x0,#9,#2,hi", -1, ""),
    ("ccmp_w", "CondCompare F T T 3w 1w 0w 0w", "ccmp w3,#1,#0,eq", -1, ""),
    ("addshiftx", "AddShift T F F 0w 0w 1w 2w 3w", "add x0,x1,x2,lsl #3", -1, ""),
    ("negshift", "AddShift F T F 1w 0w 31w 1w 3w", "neg w0,w1,lsr #3", -1, ""),
    ("adds_w", "AddShift F F T 0w 0w 1w 2w 0w", "adds w0,w1,w2", -1, ""),
    ("adds_x", "AddShift T F T 0w 0w 1w 2w 0w", "adds x0,x1,x2", -1, ""),
    ("subs_w", "AddShift F T T 0w 0w 1w 2w 0w", "subs w0,w1,w2", -1, ""),
    ("subs_x", "AddShift T T T 0w 0w 1w 2w 0w", "subs x0,x1,x2", -1, ""),
    ("adds_ext", "AddExtend T F T 6w 0w 1w 2w 2w", "adds x0,x1,w2,sxtw #2", -1, ""),
    ("adc_w", "AddCarry F F F 0w 1w 2w", "adc w0,w1,w2", -1, ""),
    ("adc_x", "AddCarry T F F 0w 1w 2w", "adc x0,x1,x2", -1, ""),
    ("adcs_w", "AddCarry F F T 0w 1w 2w", "adcs w0,w1,w2", -1, ""),
    ("adcs_x", "AddCarry T F T 0w 1w 2w", "adcs x0,x1,x2", -1, ""),
    ("sbc_w", "AddCarry F T F 0w 1w 2w", "sbc w0,w1,w2", -1, ""),
    ("sbc_x", "AddCarry T T F 0w 1w 2w", "sbc x0,x1,x2", -1, ""),
    ("sbcs_w", "AddCarry F T T 0w 1w 2w", "sbcs w0,w1,w2", -1, ""),
    ("sbcs_x", "AddCarry T T T 0w 1w 2w", "sbcs x0,x1,x2", -1, ""),
    ("eor_w", "LogicalReg F 2w F 0w 0w 1w 2w 0w", "eor w0,w1,w2", -1, ""),
    ("bic_w", "LogicalReg F 0w T 0w 0w 1w 2w 0w", "bic w0,w1,w2", -1, ""),
    ("orn_w", "LogicalReg F 1w T 0w 0w 1w 2w 0w", "orn w0,w1,w2", -1, ""),
    ("ands_x", "LogicalReg T 3w F 3w 0w 1w 2w 5w", "ands x0,x1,x2,ror #5", -1, ""),
    ("andmask", "LogicalImm F 0w F 0w 7w 0w 1w", "and w0,w1,#255", -1, ""),
    ("andimm7_x", "LogicalImm T 0w T 0w 6w 3w 3w", "and x3,x3,#127", -1, ""),
    ("andimm7_w", "LogicalImm F 0w F 0w 6w 3w 3w", "and w3,w3,#127", -1, ""),
    ("andimm7_sp", "LogicalImm T 0w T 0w 6w 31w 1w", "and sp,x1,#127", -1, "sp_result"),
    ("lslv", "VariableShift F 0w 0w 1w 2w", "lsl w0,w1,w2", -1, ""),
    ("lsrv", "VariableShift T 1w 0w 1w 2w", "lsr x0,x1,x2", -1, ""),
    ("asrv", "VariableShift F 2w 0w 1w 2w", "asr w0,w1,w2", -1, ""),
    ("ubfm", "Bitfield T 2w 0w 1w 61w 31w", "ubfiz x0,x1,#3,#32", -1, ""),
    ("sbfm", "Bitfield T 0w 0w 1w 3w 63w", "asr x0,x1,#3", -1, ""),
    ("sbfiz", "Bitfield F 0w 0w 1w 27w 9w", "sbfiz w0,w1,#5,#10", -1, ""),
    ("extr_w", "Extract F 0w 1w 2w 31w", "extr w0,w1,w2,#31", -1, ""),
    ("extr_x", "Extract T 0w 1w 2w 33w", "extr x0,x1,x2,#33", -1, ""),
    ("csel", "Select F 0w 0w 1w 2w 13w", "csel w0,w1,w2,le", -1, ""),
    ("csinc", "Select F 1w 0w 1w 2w 2w", "csinc w0,w1,w2,cs", -1, ""),
    ("csinv", "Select T 2w 0w 1w 2w 8w", "csinv x0,x1,x2,hi", -1, ""),
    ("csneg", "Select T 3w 0w 1w 2w 0w", "csneg x0,x1,x2,eq", -1, ""),
    ("smull", "MulLong F F 0w 1w 2w 31w", "smull x0,w1,w2", -1, ""),
    ("ldrb_reg", "MemReg F 1w 0w 1w 0w 2w 3w F", "ldrb w1,[x0,x2]", 0, "indexed"),
    ("strb_reg", "MemReg F 0w 0w 1w 0w 2w 3w F", "strb w1,[x0,x2]", 0, "indexed"),
    ("ldrh_reg", "MemReg F 1w 1w 1w 0w 2w 2w T", "ldrh w1,[x0,w2,uxtw #1]", 0, "indexed"),
    ("strh_reg", "MemReg F 0w 1w 1w 0w 2w 3w T", "strh w1,[x0,x2,lsl #1]", 0, "indexed"),
    ("ldr_w", "MemImm F 1w 2w 1w 0w (Scaled 1w)", "ldr w1,[x0,#4]", 0, ""),
    ("str_w", "MemImm F 0w 2w 1w 0w (Unscaled PostIndex 4w)", "str w1,[x0],#4", 0, ""),
    ("ldr_x", "MemImm F 1w 3w 1w 0w (Unscaled PostIndex 8w)", "ldr x1,[x0],#8", 0, ""),
    ("str_x", "MemImm F 0w 3w 1w 0w (Scaled 1w)", "str x1,[x0,#8]", 0, ""),
    ("ldur_x", "MemImm F 1w 3w 1w 0w (Unscaled Offset 3w)", "ldur x1,[x0,#3]", 0, ""),
    ("str_pre", "MemImm F 0w 3w 1w 0w (Unscaled PreIndex 8w)", "str x1,[x0,#8]!", 0, ""),
    ("ldp_w", "MemPair F 0w T Offset 1w 2w 0w 1w", "ldp w1,w2,[x0,#4]", 0, ""),
    ("stp_w", "MemPair F 0w F Offset 1w 2w 0w 1w", "stp w1,w2,[x0,#4]", 0, ""),
    ("ldp_x", "MemPair F 2w T Offset 1w 2w 0w 1w", "ldp x1,x2,[x0,#8]", 0, ""),
    ("ldp_pre", "MemPair F 2w T PreIndex 1w 2w 31w 126w", "ldp x1,x2,[sp,#-16]!", -1, "stack"),
    ("stp_pre", "MemPair F 2w F PreIndex 1w 2w 31w 126w", "stp x1,x2,[sp,#-16]!", -1, "stack"),
    ("ldp_post", "MemPair F 2w T PostIndex 1w 2w 31w 2w", "ldp x1,x2,[sp],#16", -1, "stack"),
    ("stp_post", "MemPair F 2w F PostIndex 1w 2w 31w 2w", "stp x1,x2,[sp],#16", -1, "stack"),
    ("andmask_sp", "LogicalImm F 0w F 0w 7w 31w 1w", "and wsp,w1,#255", -1, "sp_result"),
    ("b_back", "BranchImm F 0x3fffffew", "b 1b", -1, "backward"),
    ("bl_back", "BranchImm T 0x3fffffew", "bl 1b", -1, "backward"),
    ("ldrh_sxtw", "MemReg F 1w 1w 1w 0w 2w 6w T", "ldrh w1,[x0,w2,sxtw #1]", 0, "indexed"),
    ("ldr_sxtx", "MemReg F 1w 2w 1w 0w 2w 7w T", "ldr w1,[x0,x2,sxtx #2]", 0, "indexed"),
    ("ldp_w_pre", "MemPair F 0w T PreIndex 1w 2w 31w 126w", "ldp w1,w2,[sp,#-8]!", -1, "stack"),
    ("stp_w_pre", "MemPair F 0w F PreIndex 1w 2w 31w 126w", "stp w1,w2,[sp,#-8]!", -1, "stack"),
    ("ldp_w_post", "MemPair F 0w T PostIndex 1w 2w 31w 2w", "ldp w1,w2,[sp],#8", -1, "stack"),
    ("stp_w_post", "MemPair F 0w F PostIndex 1w 2w 31w 2w", "stp w1,w2,[sp],#8", -1, "stack"),
    ("eon_w", "LogicalReg F 2w T 1w 0w 1w 2w 3w", "eon w0,w1,w2,lsr #3", -1, ""),
    ("bics_x", "LogicalReg T 3w T 0w 0w 1w 2w 0w", "bics x0,x1,x2", -1, ""),
    ("bmi", "BCond 4w 2w", "b.mi 1f", -1, "branch"),
    ("bvs", "BCond 6w 2w", "b.vs 1f", -1, "branch"),
    ("csel_pl", "Select F 0w 0w 1w 2w 5w", "csel w0,w1,w2,pl", -1, ""),
    ("csel_vc", "Select T 0w 0w 1w 2w 7w", "csel x0,x1,x2,vc", -1, ""),
    ("csel_al", "Select T 0w 0w 1w 2w 14w", "csel x0,x1,x2,al", -1, ""),
    ("csel_nv", "Select T 0w 0w 1w 2w 15w", "csel x0,x1,x2,nv", -1, ""),
    ("add_uxtb", "AddExtend T F F 0w 0w 1w 2w 0w", "add x0,x1,w2,uxtb", -1, ""),
    ("add_uxth", "AddExtend T F F 1w 0w 1w 2w 0w", "add x0,x1,w2,uxth", -1, ""),
    ("add_sxtb", "AddExtend T F F 4w 0w 1w 2w 0w", "add x0,x1,w2,sxtb", -1, ""),
    ("add_sxth", "AddExtend T F F 5w 0w 1w 2w 0w", "add x0,x1,w2,sxth", -1, ""),
    ("ubfx_w", "Bitfield F 2w 0w 1w 8w 15w", "ubfx w0,w1,#8,#8", -1, ""),
    ("lsr_imm", "Bitfield T 2w 0w 1w 3w 63w", "lsr x0,x1,#3", -1, ""),
    ("ldr_pre", "MemImm F 1w 3w 1w 0w (Unscaled PreIndex 8w)", "ldr x1,[x0,#8]!", 0, ""),
    ("stur_w", "MemImm F 0w 2w 1w 0w (Unscaled Offset 3w)", "stur w1,[x0,#3]", 0, ""),
    ("addimm_sp", "AddImm T F F F 0w 31w 16w", "add x0,sp,#16", 0, "stack"),
    ("subimm_sp", "AddImm T T F F 31w 31w 16w", "sub sp,sp,#16", -1, "stack"),
    ("lslv_x", "VariableShift T 0w 0w 1w 2w", "lsl x0,x1,x2", -1, ""),
    ("lsrv_w", "VariableShift F 1w 0w 1w 2w", "lsr w0,w1,w2", -1, ""),
    ("asrv_x", "VariableShift T 2w 0w 1w 2w", "asr x0,x1,x2", -1, ""),
    ("ldr_pre_neg", "MemImm F 1w 3w 1w 0w (Unscaled PreIndex 504w)", "ldr x1,[x0,#-8]!", 0, ""),
    ("stur_w_neg", "MemImm F 0w 2w 1w 0w (Unscaled Offset 509w)", "stur w1,[x0,#-3]", 0, ""),
    ("tbnz_back", "TestBranch T 5w 1w 16382w", "tbnz w1,#5,1b", -1, "backward"),
    ("and_rem", "LogicalImm F 0w F 0w 1w 0w 1w", "and w0,w1,#3", -1, ""),
    ("and_blocks", "LogicalImm F 0w F 30w 29w 0w 1w", "and w0,w1,#4294967292", -1, ""),
    ("tst_byte", "LogicalImm F 3w F 0w 7w 31w 1w", "tst w1,#255", -1, ""),
    ("tst_half", "LogicalImm F 3w F 0w 15w 31w 1w", "tst w1,#65535", -1, ""),
    ("mul_x", "MulAdd T F 0w 1w 2w 31w", "mul x0,x1,x2", -1, ""),
    ("madd_x", "MulAdd T F 0w 1w 2w 3w", "madd x0,x1,x2,x3", -1, ""),
    ("madd_w", "MulAdd F F 0w 1w 2w 3w", "madd w0,w1,w2,w3", -1, ""),
    ("msub_x", "MulAdd T T 0w 1w 2w 3w", "msub x0,x1,x2,x3", -1, ""),
    ("msub_w", "MulAdd F T 0w 1w 2w 3w", "msub w0,w1,w2,w3", -1, ""),
    ("umulh", "MulHigh F 0w 1w 2w", "umulh x0,x1,x2", -1, ""),
    ("smulh", "MulHigh T 0w 1w 2w", "smulh x0,x1,x2", -1, ""),
    ("udiv_x", "Divide T F 0w 1w 2w", "udiv x0,x1,x2", -1, ""),
    ("udiv_w", "Divide F F 0w 1w 2w", "udiv w0,w1,w2", -1, ""),
    ("sdiv_x", "Divide T T 0w 1w 2w", "sdiv x0,x1,x2", -1, ""),
    ("sdiv_w", "Divide F T 0w 1w 2w", "sdiv w0,w1,w2", -1, ""),
    ("clz_x", "BitOp T Clz 0w 1w", "clz x0,x1", -1, ""),
    ("clz_w", "BitOp F Clz 0w 1w", "clz w0,w1", -1, ""),
    ("rbit_x", "BitOp T Rbit 0w 1w", "rbit x0,x1", -1, ""),
    ("rbit_w", "BitOp F Rbit 0w 1w", "rbit w0,w1", -1, ""),
    ("rev_x", "BitOp T Rev 0w 1w", "rev x0,x1", -1, ""),
    ("rev_w", "BitOp F Rev 0w 1w", "rev w0,w1", -1, ""),
    ("and_one", "LogicalImm T 0w T 0w 0w 0w 1w", "and x0,x1,#1", -1, ""),
    ("and_nibble", "LogicalImm T 0w T 0w 3w 0w 1w", "and x0,x1,#15", -1, ""),
    ("and_shift", "LogicalImm F 0w F 0w 5w 0w 1w", "and w0,w1,#63", -1, ""),
    ("orr_shift", "LogicalImm F 1w F 26w 25w 0w 1w", "orr w0,w1,#4294967232", -1, ""),
    ("rorv_x", "VariableShift T 3w 0w 1w 2w", "ror x0,x1,x2", -1, ""),
    ("rorv_w", "VariableShift F 3w 0w 1w 2w", "ror w0,w1,w2", -1, ""),
    ("ror_imm", "Extract F 0w 1w 1w 7w", "ror w0,w1,#7", -1, ""),
    ("adr", "PcAddress F 0w 12w", "adr x0,.+12", -1, "adr"),
    ("adr_back", "PcAddress F 0w 0x1ffff4w", "adr x0,.-12", -1, "adr_back"),
    ("adrp", "PcAddress T 0w 1w", ".inst 0xb0000000", -1, "adrp"),
    ("adrp_back", "PcAddress T 0w 0x1fffffw", ".inst 0xf0ffffe0", -1, "adrp_back"),
    ("ccmp_n", "CondCompare T T T 0w 9w 8w 8w", "ccmp x0,#9,#8,hi", -1, "ccmp_fallback"),
    ("ccmp_z", "CondCompare T T T 0w 9w 8w 4w", "ccmp x0,#9,#4,hi", -1, "ccmp_fallback"),
    ("ccmp_v", "CondCompare T T T 0w 9w 8w 1w", "ccmp x0,#9,#1,hi", -1, "ccmp_fallback"),
    ("movn_w", "MoveWide F 0w 1w 0w 0x1234w", "movn w0,#0x1234,lsl #16", -1, ""),
    ("movn_x", "MoveWide T 0w 0w 0w 0w", "movn x0,#0", -1, ""),
    ("movk_x", "MoveWide T 3w 2w 0w 0xbeefw", "movk x0,#0xbeef,lsl #32", -1, ""),
    ("movk_w", "MoveWide F 3w 0w 0w 0x8001w", "movk w0,#0x8001", -1, ""),
    ("and_imm_x", "LogicalImm T 0w F 8w 39w 0w 1w", "and x0,x1,#0xff00ff00ff00ff00", -1, ""),
    ("orr_imm_x", "LogicalImm T 1w F 0w 60w 0w 1w", "orr x0,x1,#0x5555555555555555", -1, ""),
    ("eor_imm_w", "LogicalImm F 2w F 4w 51w 0w 1w", "eor w0,w1,#0xf0f0f0f0", -1, ""),
    ("ands_imm_x", "LogicalImm T 3w T 32w 30w 0w 1w", "ands x0,x1,#0x7fffffff00000000", -1, ""),
    ("orr_imm_zr", "LogicalImm F 1w F 30w 3w 0w 31w", "orr w0,wzr,#0x3c", -1, ""),
    ("eor_imm_sp", "LogicalImm T 2w T 63w 62w 31w 1w", "eor sp,x1,#0xfffffffffffffffe", -1, "sp_result"),
    ("bfi_x", "Bitfield T 1w 0w 1w 56w 15w", "bfi x0,x1,#8,#16", -1, ""),
    ("bfxil_w", "Bitfield F 1w 0w 1w 3w 7w", "bfxil w0,w1,#3,#5", -1, ""),
    ("bfi_w_wrap", "Bitfield F 1w 0w 1w 4w 2w", "bfi w0,w1,#28,#3", -1, ""),
    ("sxtb_x", "Bitfield T 0w 0w 1w 0w 7w", "sxtb x0,w1", -1, ""),
    ("uxth_w", "Bitfield F 2w 0w 1w 0w 15w", "uxth w0,w1", -1, ""),
    ("asr_w31", "Bitfield F 0w 0w 1w 31w 31w", "asr w0,w1,#31", -1, ""),
    ("asr_x60", "Bitfield T 0w 0w 1w 60w 63w", "asr x0,x1,#60", -1, ""),
    ("cls_x", "BitOp T Cls 0w 1w", "cls x0,x1", -1, ""),
    ("cls_w", "BitOp F Cls 0w 1w", "cls w0,w1", -1, ""),
    ("rev16_x", "BitOp T Rev16 0w 1w", "rev16 x0,x1", -1, ""),
    ("rev16_w", "BitOp F Rev16 0w 1w", "rev16 w0,w1", -1, ""),
    ("rev32_x", "BitOp T Rev32 0w 1w", "rev32 x0,x1", -1, ""),
    ("ccmn_imm_w", "CondCompare F F T 0w 5w 1w 3w", "ccmn w0,#5,#3,ne", -1, ""),
    ("ccmp_reg_x", "CondCompare T T F 0w 1w 11w 4w", "ccmp x0,x1,#4,lt", -1, ""),
    ("ccmn_reg_x", "CondCompare T F F 0w 1w 10w 0w", "ccmn x0,x1,#0,ge", -1, ""),
    ("ccmp_reg_al", "CondCompare F T F 0w 1w 14w 15w", "ccmp w0,w1,#15,al", -1, ""),
    ("smaddl", "MulLong F F 0w 1w 2w 3w", "smaddl x0,w1,w2,x3", -1, ""),
    ("umaddl", "MulLong T F 0w 1w 2w 3w", "umaddl x0,w1,w2,x3", -1, ""),
    ("smsubl", "MulLong F T 0w 1w 2w 3w", "smsubl x0,w1,w2,x3", -1, ""),
    ("umsubl", "MulLong T T 0w 1w 2w 3w", "umsubl x0,w1,w2,x3", -1, ""),
    ("umull", "MulLong T F 0w 1w 2w 31w", "umull x0,w1,w2", -1, ""),
    ("ldr_lit_w", "LoadLiteral F 0w 1w 0x7fff5w", "ldr w1,8b+4", -1, "literal"),
    ("ldr_lit_x", "LoadLiteral F 1w 1w 5w", "ldr x1,9f+8", -1, "literal"),
    ("ldrsw_lit", "LoadLiteral F 2w 1w 0x7fff6w", "ldrsw x1,8b+8", -1, "literal"),
    ("ldrsw_lit_pos", "LoadLiteral F 2w 1w 6w", "ldrsw x1,9f+12", -1, "literal"),
    ("prfm_lit", "LoadLiteral F 3w 0w 3w", "prfm pldl1keep,9f", -1, "literal"),
    ("ldrsb_x", "MemImm F 2w 0w 1w 0w (Scaled 1w)", "ldrsb x1,[x0,#1]", 0, ""),
    ("ldrsb_w_post", "MemImm F 3w 0w 1w 0w (Unscaled PostIndex 1w)", "ldrsb w1,[x0],#1", 0, ""),
    ("ldrsh_w_pre", "MemImm F 3w 1w 1w 0w (Unscaled PreIndex 2w)", "ldrsh w1,[x0,#2]!", 0, ""),
    ("ldrsh_x", "MemImm F 2w 1w 1w 0w (Scaled 3w)", "ldrsh x1,[x0,#6]", 0, ""),
    ("ldrsw_x", "MemImm F 2w 2w 1w 0w (Scaled 1w)", "ldrsw x1,[x0,#4]", 0, ""),
    ("ldursh_x", "MemImm F 2w 1w 1w 0w (Unscaled Offset 1w)", "ldursh x1,[x0,#1]", 0, ""),
    ("ldursb_w", "MemImm F 3w 0w 1w 0w (Unscaled Offset 3w)", "ldursb w1,[x0,#3]", 0, ""),
    ("ldursw_x", "MemImm F 2w 2w 1w 0w (Unscaled Offset 5w)", "ldursw x1,[x0,#5]", 0, ""),
    ("ldrsw_post", "MemImm F 2w 2w 1w 0w (Unscaled PostIndex 4w)", "ldrsw x1,[x0],#4", 0, ""),
    ("ldrsb_reg", "MemReg F 2w 0w 1w 0w 2w 3w F", "ldrsb x1,[x0,x2]", 0, "indexed"),
    ("ldrsw_reg", "MemReg F 2w 2w 1w 0w 2w 3w T", "ldrsw x1,[x0,x2,lsl #2]", 0, "indexed"),
    ("ldrsh_uxtw", "MemReg F 3w 1w 1w 0w 2w 2w T", "ldrsh w1,[x0,w2,uxtw #1]", 0, "indexed"),
    ("ldtr_x", "MemImm F 1w 3w 1w 0w (Unscaled Unprivileged 8w)", "ldtr x1,[x0,#8]", 0, ""),
    ("ldtrb", "MemImm F 1w 0w 1w 0w (Unscaled Unprivileged 3w)", "ldtrb w1,[x0,#3]", 0, ""),
    ("ldtrsh_w", "MemImm F 3w 1w 1w 0w (Unscaled Unprivileged 2w)", "ldtrsh w1,[x0,#2]", 0, ""),
    ("ldtrsw", "MemImm F 2w 2w 1w 0w (Unscaled Unprivileged 1w)", "ldtrsw x1,[x0,#1]", 0, ""),
    ("sttrb", "MemImm F 0w 0w 1w 0w (Unscaled Unprivileged 3w)", "sttrb w1,[x0,#3]", 0, ""),
    ("sttr_w", "MemImm F 0w 2w 1w 0w (Unscaled Unprivileged 5w)", "sttr w1,[x0,#5]", 0, ""),
    ("sturh", "MemImm F 0w 1w 1w 0w (Unscaled Offset 1w)", "sturh w1,[x0,#1]", 0, ""),
    ("prfm_imm", "MemImm F 2w 3w 0w 0w (Scaled 1w)", "prfm pldl1keep,[x0,#8]", 0, ""),
    ("prfm_reg", "MemReg F 2w 3w 19w 0w 2w 3w F", "prfm pstl2strm,[x0,x2]", 0, "indexed"),
    ("prfum", "MemImm F 2w 3w 0w 0w (Unscaled Offset 1w)", "prfum pldl1keep,[x0,#1]", 0, ""),
    ("ldnp_x", "MemPair F 2w T NonTemporal 1w 2w 0w 1w", "ldnp x1,x2,[x0,#8]", 0, ""),
    ("stnp_w", "MemPair F 0w F NonTemporal 1w 2w 0w 1w", "stnp w1,w2,[x0,#4]", 0, ""),
    ("ldpsw", "MemPair F 1w T Offset 1w 2w 0w 2w", "ldpsw x1,x2,[x0,#8]", 0, ""),
    ("ldpsw_post", "MemPair F 1w T PostIndex 1w 2w 0w 2w", "ldpsw x1,x2,[x0],#8", 0, ""),
    ("ldpsw_pre", "MemPair F 1w T PreIndex 1w 2w 0w 2w", "ldpsw x1,x2,[x0,#8]!", 0, ""),
]

SCALAR_ALIASES = {
    "mul_x": ("madd x0,x1,x2,xzr",),
    "rev_x": ("rev64 x0,x1",),
    "rorv_x": ("rorv x0,x1,x2",),
    "rorv_w": ("rorv w0,w1,w2",),
    "ror_imm": ("extr w0,w1,w1,#7",),
    "tst_byte": ("ands wzr,w1,#255",),
    "tst_half": ("ands wzr,w1,#65535",),
    "movzx": (f"mov x0,#{0x8123 << 48}", f"mov x0,#{(0x8123 << 48) - (1 << 64)}"),
    "cmpimm": ("subs wzr,w1,#0",),
    "negshift": ("sub w0,wzr,w1,lsr#3",),
    "csinc": ("csinc w0,w1,w2,hs",),
    "lslv": ("lslv w0,w1,w2",),
    "lsrv": ("lsrv x0,x1,x2",),
    "asrv": ("asrv w0,w1,w2",),
    "lslv_x": ("lslv x0,x1,x2",),
    "lsrv_w": ("lsrv w0,w1,w2",),
    "asrv_x": ("asrv x0,x1,x2",),
    "smull": ("smaddl x0,w1,w2,xzr",),
    "umull": ("umaddl x0,w1,w2,xzr",),
    "movn_w": ("mov w0,#3989569535", "mov w0,#-305397761"),
    "movn_x": ("mov x0,#18446744073709551615", "mov x0,#-1"),
    "orr_imm_zr": ("mov w0,#60",),
    "asr_x60": ("sbfx x0,x1,#60,#4",),
    "sxtb_x": ("sbfm x0,x1,#0,#7",),
    "ccmp_reg_al": ("ccmp w0,w1,#15,al",),
    "ldr_lit_w": ("ldr w1,-44",),
    "ldr_lit_x": ("ldr x1,20",),
    "ldrsw_lit": ("ldrsw x1,-40",),
    "ldrsw_lit_pos": ("ldrsw x1,24",),
    "prfm_lit": ("prfm pldl1keep,12",),
}

# In the pinned L3 decoder, bit 10 sends the CLZ encodings to CLS.
L3_CLZ_FORMS = {"clz_x", "clz_w"}
# The same swap executes CLS as CLZ, and the pinned L3 decoder treats the
# no-allocate pair encodings (LDNP, STNP) as unallocated.
L3_UNMODELED_FORMS = {"cls_x", "cls_w", "ldnp_x", "stnp_w"}

PC_DISASSEMBLY = {
    "adr": "adr x0,12", "adr_back": "adr x0,-12",
    "adrp": "adrp x0,4096", "adrp_back": "adrp x0,-4096",
}

def canonical(assembly: str) -> str:
    """Match normalize_instruction's spacing and decimal immediates."""
    mnemonic, _, operands = assembly.partition(" ")
    expected = f"{mnemonic} {''.join(operands.split())}" if operands else mnemonic
    return re.sub(r"#0x[0-9a-f]+", lambda m: f"#{int(m[0][1:], 16)}", expected)


for name, instruction, assembly, _, mode in SCALAR_PROBES:
    expected = PC_DISASSEMBLY.get(mode, assembly)
    if mode == "branch":
        expected = assembly.replace("1f", "8")
    elif mode == "backward":
        expected = assembly.replace("1b", "-8")
    PROBES[name] = instruction, (canonical(expected), *SCALAR_ALIASES.get(name, ()))
    if name not in L3_CLZ_FORMS | L3_UNMODELED_FORMS:
        L3_INTEGER_FORMS.add(name)


CRC_PROBES = [
    (f"crc32{family}{width}", f"Crc32 {castagnoli} {size}w 0w 1w 2w",
     f"crc32{family}{width} w0,w1,{register}2", -1, "")
    for family, castagnoli in (("", "F"), ("c", "T"))
    for size, (width, register) in enumerate(zip("bhwx", "wwwx"))
]
for name, instruction, assembly, _, _ in CRC_PROBES:
    PROBES[name] = instruction, (assembly,)


def write_scalar_probes(directory: Path) -> None:
    asm = []
    declarations = []
    fallback = []
    crc = []
    for name, _, instruction, pointer, mode in SCALAR_PROBES + CRC_PROBES:
        if mode in ("branch", "backward"):
            asm += [f"start {name}"]
            if instruction.startswith("bl "):
                asm += [f"    adr x17, ins_{name}"]
            if mode == "backward":
                asm += ["    b 2f", "1:  mov x12, #-8", "    b .Lfinish",
                        "2:", f"word_label {name}", f"    {instruction}", "    next"]
            else:
                asm += [f"word_label {name}", f"    {instruction}", "    b 2f",
                        "1:  mov x12, #8", "    b .Lfinish", "2:  next"]
        else:
            macro = ("stack_probe" if mode in ("stack", "sp_result")
                     else "literal_probe" if mode == "literal" else "straight")
            asm += [f'{macro} {name}, "{instruction}"']
        declaration = f"X({name}, {pointer}, {int(mode == 'indexed')}, {int(mode == 'stack')}, 0)"
        if mode == "ccmp_fallback":
            fallback.append(declaration)
        elif name.startswith("crc32"):
            crc.append(declaration)
        else:
            declarations.append(declaration)
    pool = [".macro literal_pool", "    .byte " + ", ".join(map(str, LITERAL_POOL)), ".endm"]
    (directory / "scalar_probes.S").write_text("\n".join(pool + asm) + "\n")
    (directory / "scalar_probes.h").write_text(
        "#define SCALAR_CASES(X) " + " ".join(declarations) + "\n"
        "#define CCMP_FALLBACK_CASES(X) " + " ".join(fallback) + "\n"
        "#define CRC_CASES(X) " + " ".join(crc) + "\n"
    )


# Each SIMD form has a V30/V31 case. ADD also exercises the rest of the bank.
SIMD_PAIR_BASES = range(0, 32, 2)
HIGH_SIMD_PROBES = [
    ("ldr_q", "MemImm T 3w 0w 30w 1w (Scaled 1w)", "ldr q30,[x1,#16]", 1, ()),
    ("ldr_q_post", "MemImm T 3w 0w 31w 1w (Unscaled PostIndex 16w)", "ldr q31,[x1],#16", 1, ()),
    ("ldr_q_post_neg", "MemImm T 3w 0w 30w 1w (Unscaled PostIndex 496w)", "ldr q30,[x1],#-16", 1, ()),
    ("movi_4s", "SimdImm T F 0w 0w 30w", "movi v30.4s,#0", -1, ()),
    ("add_4s", "SimdBinary Add4S 30w 30w 31w", "add v30.4s,v30.4s,v31.4s", -1, ()),
    ("add_2d", "SimdBinary Add2D 31w 30w 31w", "add v31.2d,v30.2d,v31.2d", -1, ()),
    ("cmeq_16b", "SimdBinary Cmeq16B 31w 30w 31w", "cmeq v31.16b,v30.16b,v31.16b", -1, ()),
    ("cmeq_zero", "SimdUnary CmeqZero16B 31w 30w", "cmeq v31.16b,v30.16b,#0", -1, ()),
    ("uminv", "SimdUnary Uminv16B 31w 30w", "uminv b31,v30.16b", -1, ()),
    ("addv_s", "SimdUnary Addv4S 31w 30w", "addv s31,v30.4s", -1, ()),
    ("cnt_8b", "SimdUnary Cnt8B 31w 30w", "cnt v31.8b,v30.8b", -1, ()),
    ("addv_b", "SimdUnary Addv8B 31w 30w", "addv b31,v30.8b", -1, ()),
    ("fmov_to_d", "SimdTransfer FmovToD 31w 1w", "fmov d31,x1", -1, ()),
    ("addv_h", "SimdUnary Addv8H 30w 31w", "addv h30,v31.8h", -1, ()),
    ("uaddlp", "SimdUnary Uaddlp16B 31w 30w", "uaddlp v31.8h,v30.16b", -1, ()),
    ("uadalp", "SimdUnary Uadalp16B 31w 30w", "uadalp v31.8h,v30.16b", -1, ()),
    ("fmov_w", "SimdTransfer FmovW 0w 30w", "fmov w0,s30", -1, ()),
    ("fmov_x", "SimdTransfer FmovX 2w 31w", "fmov x2,d31", -1, ()),
    ("umov_b0", "SimdTransfer UmovB0 2w 31w", "umov w2,v31.b[0]", -1, ()),
    ("umov_d1", "SimdTransfer UmovD1 2w 31w", "umov x2,v31.d[1]", -1, ("mov x2,v31.d[1]",)),
    ("dup_2d", "SimdTransfer Dup2D 31w 1w", "dup v31.2d,x1", -1, ()),
    ("ldr_lit_s", "LoadLiteral T 0w 30w 4w", "ldr s30,9f+4", -1, ("ldr s30,16",)),
    ("ldr_lit_d", "LoadLiteral T 1w 31w 0x7fff8w", "ldr d31,8b+16", -1, ("ldr d31,-32",)),
    ("ldr_lit_q", "LoadLiteral T 2w 30w 7w", "ldr q30,9f+16", -1, ("ldr q30,28",)),
    ("ldr_lit_q_neg", "LoadLiteral T 2w 31w 0x7fff4w", "ldr q31,8b", -1, ("ldr q31,-48",)),
    ("ldr_b", "MemImm T 1w 0w 30w 1w (Scaled 1w)", "ldr b30,[x1,#1]", 1, ()),
    ("ldr_h_post", "MemImm T 1w 1w 31w 1w (Unscaled PostIndex 2w)", "ldr h31,[x1],#2", 1, ()),
    ("ldr_s_pre", "MemImm T 1w 2w 30w 1w (Unscaled PreIndex 4w)", "ldr s30,[x1,#4]!", 1, ()),
    ("ldr_d", "MemImm T 1w 3w 31w 1w (Scaled 1w)", "ldr d31,[x1,#8]", 1, ()),
    ("ldur_d", "MemImm T 1w 3w 30w 1w (Unscaled Offset 3w)", "ldur d30,[x1,#3]", 1, ()),
    ("ldr_q_pre", "MemImm T 3w 0w 30w 1w (Unscaled PreIndex 16w)", "ldr q30,[x1,#16]!", 1, ()),
    ("ldr_q_reg", "MemReg T 3w 0w 30w 1w 2w 3w F", "ldr q30,[x1,x2]", 1, ()),
    ("str_d_reg", "MemReg T 0w 3w 30w 1w 2w 3w F", "str d30,[x1,x2]", 1, ()),
    ("ldr_s_uxtw", "MemReg T 1w 2w 31w 1w 2w 2w F", "ldr s31,[x1,w2,uxtw]", 1, ()),
    ("stur_b", "MemImm T 0w 0w 31w 1w (Unscaled Offset 3w)", "stur b31,[x1,#3]", 1, ()),
    ("str_h", "MemImm T 0w 1w 30w 1w (Scaled 1w)", "str h30,[x1,#2]", 1, ()),
    ("stur_q", "MemImm T 2w 0w 31w 1w (Unscaled Offset 1w)", "stur q31,[x1,#1]", 1, ()),
    ("str_s_post", "MemImm T 0w 2w 30w 1w (Unscaled PostIndex 4w)", "str s30,[x1],#4", 1, ()),
    ("str_q_pre", "MemImm T 2w 0w 30w 1w (Unscaled PreIndex 16w)", "str q30,[x1,#16]!", 1, ()),
    ("ldp_s", "MemPair T 0w T Offset 30w 31w 1w 1w", "ldp s30,s31,[x1,#4]", 1, ()),
    ("ldp_d", "MemPair T 1w T Offset 30w 31w 1w 1w", "ldp d30,d31,[x1,#8]", 1, ()),
    ("stp_d_pre", "MemPair T 1w F PreIndex 30w 31w 1w 2w", "stp d30,d31,[x1,#16]!", 1, ()),
    ("stp_s_post", "MemPair T 0w F PostIndex 30w 31w 1w 2w", "stp s30,s31,[x1],#8", 1, ()),
    ("ldp_q_post", "MemPair T 2w T PostIndex 30w 31w 1w 2w", "ldp q30,q31,[x1],#32", 1, ()),
    ("ldnp_d", "MemPair T 1w T NonTemporal 30w 31w 1w 1w", "ldnp d30,d31,[x1,#8]", 1, ()),
    ("stnp_q", "MemPair T 2w F NonTemporal 30w 31w 1w 0w", "stnp q30,q31,[x1]", 1, ()),
    ("movi_16b", "SimdImm T F 14w 0xa5w 30w", "movi v30.16b,#0xa5", -1, ()),
    ("movi_8b", "SimdImm F F 14w 1w 30w", "movi v30.8b,#1", -1, ()),
    ("movi_4s_lsl", "SimdImm T F 2w 0x12w 31w", "movi v31.4s,#0x12,lsl #8", -1, ()),
    ("movi_2s_msl", "SimdImm F F 13w 0x7fw 31w", "movi v31.2s,#0x7f,msl #16", -1, ()),
    ("movi_d", "SimdImm F T 14w 0xaaw 31w", "movi d31,#0xff00ff00ff00ff00", -1, ()),
    ("movi_2d", "SimdImm T T 14w 0x66w 30w", "movi v30.2d,#0xffff0000ffff00", -1, ()),
    ("mvni_8h", "SimdImm T T 10w 0x34w 30w", "mvni v30.8h,#0x34,lsl #8", -1, ()),
    ("mvni_4s_msl", "SimdImm T T 12w 0x12w 30w", "mvni v30.4s,#0x12,msl #8", -1, ()),
    ("orr_4s_imm", "SimdImm T F 7w 0x80w 31w", "orr v31.4s,#0x80,lsl #24", -1, ()),
    ("orr_2s_imm", "SimdImm F F 1w 7w 30w", "orr v30.2s,#0x7", -1, ()),
    ("bic_8h_imm", "SimdImm T T 9w 0xffw 30w", "bic v30.8h,#0xff", -1, ()),
    ("bic_4h_imm", "SimdImm F T 11w 1w 31w", "bic v31.4h,#0x1,lsl #8", -1, ()),
    ("fmov_4s_imm", "SimdImm T F 15w 0x70w 31w", "fmov v31.4s,#1.0", -1,
     ("fmov v31.4s,#1.000000000000000000e+00", "fmov v31.4s,#1.00000000")),
    ("fmov_2d_imm", "SimdImm T T 15w 0x80w 30w", "fmov v30.2d,#-2.0", -1,
     ("fmov v30.2d,#-2.000000000000000000e+00", "fmov v30.2d,#-2.00000000")),
    ("fmov_2s_imm", "SimdImm F F 15w 0w 31w", "fmov v31.2s,#2.0", -1,
     ("fmov v31.2s,#2.000000000000000000e+00", "fmov v31.2s,#2.00000000")),
]

# Register-offset SIMD&FP transfers index by X2.
SIMD_INDEXED = {"ldr_q_reg", "str_d_reg", "ldr_s_uxtw"}

SIMD_PROBES = [
    (*probe, 30) for probe in HIGH_SIMD_PROBES
] + [
    (f"add_4s_v{base}", f"SimdBinary Add4S {base}w {base}w {base + 1}w",
     f"add v{base}.4s,v{base}.4s,v{base + 1}.4s", -1, (), base)
    for base in SIMD_PAIR_BASES if base != 30
]

PERMUTE_PROBES = [
    ("str_q", "MemImm T 2w 0w 31w 0w (Scaled 1w)", "str q31,[x0,#16]", 0),
    ("tbl", "SimdTable F 30w 30w 31w", "tbl v30.16b,{v30.16b},v31.16b", -1),
    ("tbx", "SimdTable T 30w 30w 31w", "tbx v30.16b,{v30.16b},v31.16b", -1),
    ("ext_0", "SimdExtract 31w 30w 31w 0w", "ext v31.16b,v30.16b,v31.16b,#0", -1),
    ("ext_15", "SimdExtract 30w 30w 31w 15w", "ext v30.16b,v30.16b,v31.16b,#15", -1),
    ("rev16b", "SimdUnary Rev16B 30w 31w", "rev16 v30.16b,v31.16b", -1),
    ("rev32b", "SimdUnary Rev32B 30w 31w", "rev32 v30.16b,v31.16b", -1),
    ("rev32h", "SimdUnary Rev32H 31w 30w", "rev32 v31.8h,v30.8h", -1),
    ("rev64b", "SimdUnary Rev64B 30w 31w", "rev64 v30.16b,v31.16b", -1),
    ("rev64h", "SimdUnary Rev64H 31w 30w", "rev64 v31.8h,v30.8h", -1),
    ("rev64s", "SimdUnary Rev64S 30w 31w", "rev64 v30.4s,v31.4s", -1),
    ("eor_16b", "SimdBinary Eor16B 31w 30w 31w", "eor v31.16b,v30.16b,v31.16b", -1),
    ("orr_16b", "SimdBinary Orr16B 30w 31w 30w", "orr v30.16b,v31.16b,v30.16b", -1),
    ("shl_4s", "SimdShift Shl 30w 31w 63w", "shl v30.4s,v31.4s,#31", -1),
    ("shl_2d", "SimdShift Shl 31w 30w 64w", "shl v31.2d,v30.2d,#0", -1),
    ("ushr_4s", "SimdShift Ushr 31w 30w 63w", "ushr v31.4s,v30.4s,#1", -1),
    ("ushr_2d", "SimdShift Ushr 31w 30w 64w", "ushr v31.2d,v30.2d,#64", -1),
    ("sri_4s", "SimdShift Sri 31w 30w 32w", "sri v31.4s,v30.4s,#32", -1),
    ("sri_2d", "SimdShift Sri 30w 31w 88w", "sri v30.2d,v31.2d,#40", -1),
    ("tbx_distinct_table", "SimdTable T 31w 30w 31w", "tbx v31.16b,{v30.16b},v31.16b", -1),
    ("shl_2d_interior", "SimdShift Shl 31w 30w 81w", "shl v31.2d,v30.2d,#17", -1),
    ("ushr_2d_interior", "SimdShift Ushr 31w 30w 115w", "ushr v31.2d,v30.2d,#13", -1),
    ("sri_4s_interior", "SimdShift Sri 31w 30w 51w", "sri v31.4s,v30.4s,#13", -1),
]
PERMUTE_SIMD_PROBES = [(name, instr, asm, ptr, (), 30)
                       for name, instr, asm, ptr in PERMUTE_PROBES]

CRYPTO_SIMD_PROBES = [
    ("pmull", "Pmull F 30w 30w 31w", "pmull v30.1q,v30.1d,v31.1d", -1, (), 30),
    ("pmull2", "Pmull T 31w 30w 31w", "pmull2 v31.1q,v30.2d,v31.2d", -1, (), 30),
    ("aese", "Aes Aese 30w 31w", "aese v30.16b,v31.16b", -1, (), 30),
    ("aesd", "Aes Aesd 30w 31w", "aesd v30.16b,v31.16b", -1, (), 30),
    ("aesmc", "Aes Aesmc 31w 30w", "aesmc v31.16b,v30.16b", -1, (), 30),
    ("aesimc", "Aes Aesimc 30w 31w", "aesimc v30.16b,v31.16b", -1, (), 30),
    ("sha1c", "ShaThree 0w 28w 29w 30w", "sha1c q28,s29,v30.4s", -1, (), 28),
    ("sha1p", "ShaThree 1w 28w 29w 30w", "sha1p q28,s29,v30.4s", -1, (), 28),
    ("sha1m", "ShaThree 2w 28w 29w 30w", "sha1m q28,s29,v30.4s", -1, (), 28),
    ("sha1su0", "ShaThree 3w 28w 29w 30w", "sha1su0 v28.4s,v29.4s,v30.4s", -1, (), 28),
    ("sha256h", "ShaThree 4w 28w 29w 30w", "sha256h q28,q29,v30.4s", -1, (), 28),
    ("sha256h2", "ShaThree 5w 28w 29w 30w", "sha256h2 q28,q29,v30.4s", -1, (), 28),
    ("sha256su1", "ShaThree 6w 28w 29w 30w", "sha256su1 v28.4s,v29.4s,v30.4s", -1, (), 28),
    ("sha1h", "ShaTwo 0w 28w 29w", "sha1h s28,s29", -1, (), 28),
    ("sha1su1", "ShaTwo 1w 28w 29w", "sha1su1 v28.4s,v29.4s", -1, (), 28),
    ("sha256su0", "ShaTwo 2w 28w 29w", "sha256su0 v28.4s,v29.4s", -1, (), 28),
    ("sha512h", "CryptoThree F 0w 28w 29w 30w", "sha512h q28,q29,v30.2d", -1, (), 28),
    ("sha512h2", "CryptoThree F 1w 28w 29w 30w", "sha512h2 q28,q29,v30.2d", -1, (), 28),
    ("sha512su1", "CryptoThree F 2w 28w 29w 30w", "sha512su1 v28.2d,v29.2d,v30.2d", -1, (), 28),
    ("rax1", "CryptoThree F 3w 28w 29w 30w", "rax1 v28.2d,v29.2d,v30.2d", -1, (), 28),
    ("sha512su0", "CryptoTwo 0w 28w 29w", "sha512su0 v28.2d,v29.2d", -1, (), 28),
    ("eor3", "CryptoFour 0w 28w 29w 30w 31w", "eor3 v28.16b,v29.16b,v30.16b,v31.16b", -1, (), 28),
    ("bcax", "CryptoFour 1w 28w 29w 30w 31w", "bcax v28.16b,v29.16b,v30.16b,v31.16b", -1, (), 28),
    ("xar_0", "Xar 28w 29w 30w 0w", "xar v28.2d,v29.2d,v30.2d,#0", -1, (), 28),
    ("xar_1", "Xar 31w 29w 30w 1w", "xar v31.2d,v29.2d,v30.2d,#1", -1, (), 28),
    ("xar_63", "Xar 28w 28w 30w 63w", "xar v28.2d,v28.2d,v30.2d,#63", -1, (), 28),
]

# Structure loads and stores use the four observed registers from V28 (or V30,
# wrapping to V1) and address the data window through X1; register post-index
# forms add X2.
ARRANGEMENTS = [("8b", 0, False), ("16b", 0, True), ("4h", 1, False), ("8h", 1, True),
                ("2s", 2, False), ("4s", 2, True), ("1d", 3, False), ("2d", 3, True)]
MULTI_FORMS = [("ld1", 7, 1, 1), ("ld1", 10, 2, 1), ("ld1", 6, 3, 1), ("ld1", 2, 4, 1),
               ("ld2", 8, 1, 2), ("ld3", 4, 1, 3), ("ld4", 0, 1, 4)]
LANE_SIZES = [("b", 1), ("h", 2), ("s", 4), ("d", 8)]
STRUCTURE_PROBES = []
STRUCTURE_INDEXED = set()
STRUCTURE_WIDE = set()


def register_list(base: int, count: int, suffix: str) -> tuple[str, ...]:
    names = [f"v{(base + i) % 32}.{suffix}" for i in range(count)]
    listed = "{" + ",".join(names) + "}"
    ranged = "{" + f"{names[0]}-{names[-1]}" + "}"
    return (listed,) if count == 1 else (listed, ranged)


def add_structure(name: str, instruction: str, mnemonic: str, registers: tuple[str, ...],
                  lane: str, mode: int, total: int, base: int) -> None:
    suffix = ("[x1]", f"[x1],#{total}", "[x1],x2")[mode]
    texts = [f"{mnemonic} {r}{lane},{suffix}" for r in registers]
    if mode == 2:
        STRUCTURE_INDEXED.add(name)
    if total > 56:
        STRUCTURE_WIDE.add(name)
    STRUCTURE_PROBES.append((name, instruction, texts[0], 1, tuple(texts[1:]), base))


def build_structure_probes() -> None:
    i = 0
    for load in (True, False):
        for op, opc, rpt, selem in MULTI_FORMS:
            for arrangement, size, q in ARRANGEMENTS:
                if size == 3 and not q and selem != 1:
                    continue
                count = rpt * selem
                mode, base = i % 3, 30 if i % 5 == 0 else 28
                i += 1
                mnemonic = op if load else "st" + op[2:]
                name = f"{mnemonic}_{count}r_{arrangement}_m{mode}"
                m = ("0w", "31w", "2w")[mode]
                instruction = (f"MemMulti {'T' if q else 'F'} {'T' if load else 'F'} "
                               f"{'F' if mode == 0 else 'T'} {m} {opc}w {size}w {base}w 1w")
                add_structure(name, instruction, mnemonic,
                              register_list(base, count, arrangement), "", mode,
                              count * (16 if q else 8), base)
        for (element, bytes_), scale in zip(LANE_SIZES, range(4)):
            for selem in range(1, 5):
                lanes = 16 // bytes_
                # Cycle through the top lane, lane 0 and an interior lane.
                choice = (selem + scale + (0 if load else 1)) % 3
                index = (lanes - 1, 0, (5 * selem + 3) % lanes)[choice]
                mode, base = i % 3, 30 if i % 5 == 0 else 28
                i += 1
                mnemonic = f"{'ld' if load else 'st'}{selem}"
                name = f"{mnemonic}_{element}{index}_m{mode}"
                if element == "b":
                    q, S, size, opc = index >> 3, (index >> 2) & 1, index & 3, 0
                elif element == "h":
                    q, S, size, opc = index >> 2, (index >> 1) & 1, (index & 1) << 1, 2
                elif element == "s":
                    q, S, size, opc = index >> 1, index & 1, 0, 4
                else:
                    q, S, size, opc = index, 0, 1, 4
                opc += (selem - 1) // 2
                r = (selem - 1) % 2
                m = ("0w", "31w", "2w")[mode]
                instruction = (f"MemLane {'T' if q else 'F'} {'T' if load else 'F'} "
                               f"{'F' if mode == 0 else 'T'} {m} {'T' if r else 'F'} {opc}w "
                               f"{'T' if S else 'F'} {size}w {base}w 1w")
                add_structure(name, instruction, mnemonic,
                              register_list(base, selem, element), f"[{index}]", mode,
                              selem * bytes_, base)
    for selem in range(1, 5):
        for arrangement, size, q in ARRANGEMENTS:
            mode, base = i % 3, 30 if i % 5 == 0 else 28
            i += 1
            mnemonic = f"ld{selem}r"
            name = f"{mnemonic}_{arrangement}_m{mode}"
            m = ("0w", "31w", "2w")[mode]
            instruction = (f"MemLane {'T' if q else 'F'} T {'F' if mode == 0 else 'T'} {m} "
                           f"{'T' if (selem - 1) % 2 else 'F'} {6 + (selem - 1) // 2}w F "
                           f"{size}w {base}w 1w")
            add_structure(name, instruction, mnemonic,
                          register_list(base, selem, arrangement), "", mode,
                          selem * 2 ** size, base)


build_structure_probes()

for name, instruction, assembly, _, aliases, _ in SIMD_PROBES + PERMUTE_SIMD_PROBES + CRYPTO_SIMD_PROBES + STRUCTURE_PROBES:
    PROBES[name] = instruction, tuple(canonical(text) for text in (assembly, *aliases))


def write_simd_probes(directory: Path) -> None:
    asm = [f'{"literal_probe" if name.startswith("ldr_lit") else "straight"} {name}, "{assembly}"'
           for name, _, assembly, _, _, _ in SIMD_PROBES + PERMUTE_SIMD_PROBES + CRYPTO_SIMD_PROBES + STRUCTURE_PROBES]
    cases = [
        f"X({name}, {pointer}, {int(name in SIMD_INDEXED)}, 0, {base})"
        for name, _, _, pointer, _, base in SIMD_PROBES
    ]
    # Native dispatch uses the even register number times eight as a byte offset
    # into 16-byte entries; the four registers wrap from V31 to V0.
    for label, op, done in (("load", "ldp", "loads"), ("store", "stp", "stores")):
        asm.append(f".L{label}_vectors:")
        for base in SIMD_PAIR_BASES:
            asm += [f"    {op} q{base}, q{base + 1}, [x9, #32]",
                    f"    {op} q{(base + 2) % 32}, q{(base + 3) % 32}, [x9, #64]",
                    f"    b .L{done}_done", "    nop"]
    permute_cases = [
        f"X({name}, {pointer}, 0, 0, {base})"
        for name, _, _, pointer, _, base in PERMUTE_SIMD_PROBES
    ]
    crypto_cases = [
        f"X({name}, {pointer}, 0, 0, {base})"
        for name, _, _, pointer, _, base in CRYPTO_SIMD_PROBES
    ]
    structure_cases = [
        f"X({name}, {pointer}, {int(name in STRUCTURE_INDEXED)}, 0, {base})"
        for name, _, _, pointer, _, base in STRUCTURE_PROBES
    ]
    wide = " || ".join(f"id == Case_{name}" for name in sorted(STRUCTURE_WIDE))
    (directory / "simd_probes.S").write_text("\n".join(asm) + "\n")
    (directory / "simd_probes.h").write_text(
        "#define SIMD_CASES(X) " + " ".join(cases)
        + "\n#define PERMUTE_CASES(X) " + " ".join(permute_cases) + "\n"
        "#define CRYPTO_SIMD_CASES(X) " + " ".join(crypto_cases) + "\n"
        "#define STRUCTURE_CASES(X) " + " ".join(structure_cases) + "\n"
        f"#define WIDE_CASE(id) ({wide})\n"
    )


def command(*args: str | Path) -> str:
    return subprocess.check_output(args, text=True)


def llvm_objdump(explicit: str | None) -> Path:
    if explicit:
        return Path(explicit)
    target_libdir = Path(command("rustc", "--print", "target-libdir").strip())
    filename = target_libdir.parent / "bin/llvm-objdump"
    if not filename.is_file():
        raise SystemExit("Install rustup's llvm-tools component or pass --llvm-objdump")
    return filename


def disassembled(objdump: str | Path, obj: Path) -> dict[int, tuple[int, str]]:
    rows = re.findall(
        r"^[ \t]*([0-9a-f]+):[ \t]+([0-9a-f]{8})[ \t]+(.+)$",
        command(objdump, "-d", obj), re.MULTILINE,
    )
    return {int(address, 16): (int(word, 16), text) for address, word, text in rows}


def normalize_instruction(address: int, text: str) -> str:
    mnemonic, _, operands = text.split("//", 1)[0].strip().replace("\t", " ").partition(" ")
    operands = "".join(operands.split("<", 1)[0].split())
    if mnemonic in {"b", "bl", "cbz", "cbnz", "tbz", "tbnz"} or mnemonic.startswith("b."):
        prefix, comma, target = operands.rpartition(",")
        operands = f"{prefix}{comma}{int(target, 16) - address}"
    if mnemonic in {"ldr", "ldrsw", "prfm"} and "[" not in operands:
        prefix, comma, target = operands.rpartition(",")
        operands = f"{prefix}{comma}{int(target, 16) - address}"
    if mnemonic in {"adr", "adrp"}:
        register, _, target = operands.partition(",")
        if target.startswith("#"):
            displacement = int(target[1:], 0)
        else:
            base = address & ~4095 if mnemonic == "adrp" else address
            displacement = (int(target, 16) - base + 2**63) % 2**64 - 2**63
        operands = f"{register},{displacement}"
    operands = re.sub(r"#(-?(?:0x[0-9a-f]+|[0-9]+))",
                      lambda m: f"#{int(m[1], 16 if '0x' in m[1] else 10)}", operands)
    return f"{mnemonic} {operands}" if operands else mnemonic


def observation(row: str) -> str:
    fields = row.split()
    if len(fields) != 17:
        raise ValueError(f"expected seventeen state fields, got {row}")
    pc = 256 + int(fields[0])
    sp = int(fields[1], 16)
    nzcv = int(fields[2], 16)
    registers = [int(w, 16) for w in fields[3:7]]
    vectors = [int(w, 16) for w in fields[7:15]]
    link = int(fields[15], 16)
    data = bytes.fromhex(fields[16])
    if len(data) != 64:
        raise ValueError(f"expected 64 bytes, got {len(data)}")
    regs = [f"0x{w:016x}w" for w in registers]
    packed = [vectors[i] | (vectors[i + 1] << 64) for i in (0, 2, 4, 6)]
    return (
        f"({pc}w, 0x{sp:x}w, {nzcv}w, 0x{link:016x}w, [{'; '.join(regs)}],\n"
        f"       [{'; '.join(f'0x{v:032x}w' for v in packed)}],\n"
        f"       [{'; '.join(f'{b}w' for b in data)}])"
    )


def generated(directory: Path, objdump: Path) -> tuple[str, int]:
    with tempfile.TemporaryDirectory(prefix="arm64-native-") as temporary:
        obj = Path(temporary) / "native.o"
        program = Path(temporary) / "native"
        write_scalar_probes(Path(temporary))
        write_simd_probes(Path(temporary))
        command("/usr/bin/as", "-march=armv8.2-a+crc+crypto+sha3", "-I", temporary, "-o", obj, directory / "native_a64.S")
        command("/usr/bin/gcc", "-O2", "-Wall", "-Wextra", "-Werror", "-I", temporary,
                directory / "native_a64.c", obj, "-o", program)
        addresses = {
            name: int(address, 16)
            for address, name in re.findall(
                r"^([0-9a-f]+) \w ins_(\w+)$",
                command("/usr/bin/nm", "--defined-only", obj), re.MULTILINE,
            )
        }
        if addresses.keys() != PROBES.keys():
            raise ValueError(f"unexpected probe symbols: {addresses.keys()}")
        gnu = disassembled("/usr/bin/objdump", obj)
        llvm = disassembled(objdump, obj)
        words = {}
        for name, address in addresses.items():
            _, expected = PROBES[name]
            words[name] = gnu[address][0]
            for tool, entries in (("GNU", gnu), ("LLVM", llvm)):
                word, text = entries[address]
                instruction = normalize_instruction(address, text)
                if word != words[name] or instruction not in expected:
                    raise ValueError(f"{tool} decoded {name} as {word:08x} {text}; "
                                     f"expected {words[name]:08x} and one of {expected}")
        rows = command(program).splitlines()

    if len(rows) % 3 != 0:
        raise ValueError("incomplete native observation")
    counts = Counter(header.split()[0] for header in rows[::3])
    if counts != Counter({name: 8 for name in PROBES}):
        raise ValueError(f"expected eight observations per probe, got {dict(counts)}")

    lines = ["(* Generated by generate_native.py on native AArch64. *)",
             "Theory arm64NativeCases", "Ancestors arm64Isa", "",
             'Type observation = ``:word64 # word64 # word4 # word64 # word64 list # word128 list # word8 list``',
             'Type native_case = ``:word32 # arm64_instr # observation # observation``',
             "",
             "Definition literal_pool_def:",
             "  literal_pool : word8 list =",
             "    [" + "; ".join(f"{b}w" for b in LITERAL_POOL) + "]",
             "End",
             ""]
    l3_cases = []
    l3_clz_zero = []
    crc_cases = []
    simd_cases = []
    simd_bases = {name: base for name, *_, base in SIMD_PROBES + PERMUTE_SIMD_PROBES + CRYPTO_SIMD_PROBES + STRUCTURE_PROBES}
    for i in range(0, len(rows), 3):
        n = i // 3
        header, initial, final = rows[i:i + 3]
        name = header
        if name.startswith("crc32"):
            crc_cases.append(str(n))
        if name in L3_INTEGER_FORMS:
            l3_cases.append(str(n))
        if name in L3_CLZ_FORMS and n % 8 == 0:
            l3_clz_zero.append(str(n))
        if name in simd_bases:
            simd_cases.append(f"({n},{simd_bases[name]})")
        instruction, _ = PROBES[name]
        lines += [
            f"Definition native_case_{n}_def:",
            f"  native_case_{n} : native_case =",
            f"    (0x{words[name]:08x}w, {instruction},",
            f"      {observation(initial)},",
            f"      {observation(final)})",
            "End", "",
        ]
    count = len(rows) // 3
    lines += ["Definition native_case_count_def:",
              f"  native_case_count = {count}", "End", ""]
    groups = ["; ".join(l3_cases[i:i + 16]) for i in range(0, len(l3_cases), 16)]
    lines += ["Definition native_l3_cases_def:",
              "  native_l3_cases : num list =",
              "    [" + ";\n     ".join(groups) + "]", "End", ""]
    lines += ["Definition native_l3_clz_zero_def:",
              "  native_l3_clz_zero : num list =",
              "    [" + "; ".join(l3_clz_zero) + "]", "End", ""]
    groups = ["; ".join(crc_cases[i:i + 16]) for i in range(0, len(crc_cases), 16)]
    lines += ["Definition native_crc_cases_def:",
              "  native_crc_cases : num list =",
              "    [" + ";\n     ".join(groups) + "]", "End", ""]
    groups = ["; ".join(simd_cases[i:i + 16]) for i in range(0, len(simd_cases), 16)]
    lines += ["Definition native_simd_cases_def:",
              "  native_simd_cases : (num # num) list =",
              "    [" + ";\n     ".join(groups) + "]", "End", ""]
    return "\n".join(lines), count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--llvm-objdump")
    args = parser.parse_args()
    if platform.machine() != "aarch64":
        raise SystemExit("Native conformance requires an AArch64 host")
    directory = Path(__file__).resolve().parent
    filename = directory / "arm64NativeCasesScript.sml"
    result, count = generated(directory, llvm_objdump(args.llvm_objdump))
    if args.check:
        if filename.read_text() != result:
            raise SystemExit("native observations differ from the checked-in fixture")
        print(f"{count} native hardware observations match; GNU and LLVM disassembly checked")
        print("Native R-- page denies stores and instruction fetch with SEGV_ACCERR")
    else:
        filename.write_text(result)


if __name__ == "__main__":
    main()

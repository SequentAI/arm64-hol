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
    "stpx", "stpx_regs", "stpx_zero", "nop", "addsp", "ldrb_sp",
}

# Each expected disassembly is paired with the exact HOL instruction value.
PROBES = {
    "cbz": ("CompareBranch F F 1w 2w", ("cbz w1,8",)),
    "mov": ("LogicalReg T 1w F 0w 2w 31w 0w 0w", ("mov x2,x0", "orr x2,xzr,x0")),
    "movz": ("MoveZero F 0w 0w 0x8001w", ("mov w0,#32769", "movz w0,#32769")),
    "addext": ("AddExtend T F F 2w 3w 2w 1w 0w", ("add x3,x2,w1,uxtw",)),
    "ldrb": ("MemImm T 0w 1w 2w (Unscaled PostIndex 1w)", ("ldrb w1,[x2],#1",)),
    "add": ("AddShift F F F 0w 0w 0w 1w 0w", ("add w0,w0,w1",)),
    "cmp": ("AddShift T T T 0w 31w 2w 3w 0w", ("cmp x2,x3", "subs xzr,x2,x3")),
    "bne": ("BCond 1w 0x7fffdw", ("b.ne -12",)),
    "ret": ("Ret 30w", ("ret", "ret x30")),
    "br": ("Br 1w", ("br x1",)),
    "ldpq": ("LdpQ 0w 1w 1w 0w", ("ldp q0,q1,[x1]",)),
    "stpq": ("StpQ 0w 1w 0w 0w", ("stp q0,q1,[x0]",)),
    "stpx": ("MemPair F T Offset 31w 31w 0w 2w", ("stp xzr,xzr,[x0,#16]",)),
    "movi": ("MoviZero 0w", ("movi v0.2d,#0",)),
    "nop": ("Nop", ("nop", "hint #0")),
    "stpx_regs": ("MemPair F T Offset 1w 2w 0w 0w", ("stp x1,x2,[x0]",)),
    "stpx_zero": ("MemPair F T Offset 31w 31w 0w 0w", ("stp xzr,xzr,[x0]",)),
    "addsp": ("AddExtend T F F 2w 31w 31w 1w 0w", ("add sp,sp,w1,uxtw",)),
    "ldrb_sp": ("MemImm T 0w 1w 31w (Unscaled PostIndex 1w)", ("ldrb w1,[sp],#1",)),
    "ldpq_pos": ("LdpQ 0w 1w 1w 1w", ("ldp q0,q1,[x1,#16]",)),
    "stpq_neg": ("StpQ 0w 1w 0w 127w", ("stp q0,q1,[x0,#-16]",)),
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
    ("movzx", "MoveZero T 3w 0w 0x8123w", "movz x0,#0x8123,lsl #48", -1, ""),
    ("addimmw", "AddImm F F F F 0w 1w 7w", "add w0,w1,#7", -1, ""),
    ("addimmx", "AddImm T F F T 0w 1w 7w", "add x0,x1,#7,lsl #12", -1, ""),
    ("subimmw", "AddImm F T F F 0w 1w 7w", "sub w0,w1,#7", -1, ""),
    ("subimmx", "AddImm T T F F 0w 1w 7w", "sub x0,x1,#7", -1, ""),
    ("cmpimm", "AddImm F T T F 31w 1w 0w", "cmp w1,#0", -1, ""),
    ("ccmp_x", "CompareImm T 0w 9w 8w 2w", "ccmp x0,#9,#2,hi", -1, ""),
    ("ccmp_w", "CompareImm F 3w 1w 0w 0w", "ccmp w3,#1,#0,eq", -1, ""),
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
    ("andmask", "AndByteMask 0w 1w", "and w0,w1,#255", -1, ""),
    ("andimm7_x", "LogicalMask AndLowSevenX 3w 3w", "and x3,x3,#127", -1, ""),
    ("andimm7_w", "LogicalMask AndLowSevenW 3w 3w", "and w3,w3,#127", -1, ""),
    ("andimm7_sp", "LogicalMask AndLowSevenX 31w 1w", "and sp,x1,#127", -1, "sp_result"),
    ("lslv", "VariableShift F 0w 0w 1w 2w", "lsl w0,w1,w2", -1, ""),
    ("lsrv", "VariableShift T 1w 0w 1w 2w", "lsr x0,x1,x2", -1, ""),
    ("asrv", "VariableShift F 2w 0w 1w 2w", "asr w0,w1,w2", -1, ""),
    ("ubfm", "Bitfield T F 0w 1w 61w 31w", "ubfiz x0,x1,#3,#32", -1, ""),
    ("sbfm", "Bitfield T T 0w 1w 3w 63w", "asr x0,x1,#3", -1, ""),
    ("sbfiz", "Bitfield F T 0w 1w 27w 9w", "sbfiz w0,w1,#5,#10", -1, ""),
    ("extr_w", "Extract F 0w 1w 2w 31w", "extr w0,w1,w2,#31", -1, ""),
    ("extr_x", "Extract T 0w 1w 2w 33w", "extr x0,x1,x2,#33", -1, ""),
    ("csel", "Select F 0w 0w 1w 2w 13w", "csel w0,w1,w2,le", -1, ""),
    ("csinc", "Select F 1w 0w 1w 2w 2w", "csinc w0,w1,w2,cs", -1, ""),
    ("csinv", "Select T 2w 0w 1w 2w 8w", "csinv x0,x1,x2,hi", -1, ""),
    ("csneg", "Select T 3w 0w 1w 2w 0w", "csneg x0,x1,x2,eq", -1, ""),
    ("smull", "SignedMulLong 0w 1w 2w", "smull x0,w1,w2", -1, ""),
    ("ldrb_reg", "MemReg T 0w 1w 0w 2w 3w F", "ldrb w1,[x0,x2]", 0, "indexed"),
    ("strb_reg", "MemReg F 0w 1w 0w 2w 3w F", "strb w1,[x0,x2]", 0, "indexed"),
    ("ldrh_reg", "MemReg T 1w 1w 0w 2w 2w T", "ldrh w1,[x0,w2,uxtw #1]", 0, "indexed"),
    ("strh_reg", "MemReg F 1w 1w 0w 2w 3w T", "strh w1,[x0,x2,lsl #1]", 0, "indexed"),
    ("ldr_w", "MemImm T 2w 1w 0w (Scaled 1w)", "ldr w1,[x0,#4]", 0, ""),
    ("str_w", "MemImm F 2w 1w 0w (Unscaled PostIndex 4w)", "str w1,[x0],#4", 0, ""),
    ("ldr_x", "MemImm T 3w 1w 0w (Unscaled PostIndex 8w)", "ldr x1,[x0],#8", 0, ""),
    ("str_x", "MemImm F 3w 1w 0w (Scaled 1w)", "str x1,[x0,#8]", 0, ""),
    ("ldur_x", "MemImm T 3w 1w 0w (Unscaled Offset 3w)", "ldur x1,[x0,#3]", 0, ""),
    ("str_pre", "MemImm F 3w 1w 0w (Unscaled PreIndex 8w)", "str x1,[x0,#8]!", 0, ""),
    ("ldp_w", "MemPair T F Offset 1w 2w 0w 1w", "ldp w1,w2,[x0,#4]", 0, ""),
    ("stp_w", "MemPair F F Offset 1w 2w 0w 1w", "stp w1,w2,[x0,#4]", 0, ""),
    ("ldp_x", "MemPair T T Offset 1w 2w 0w 1w", "ldp x1,x2,[x0,#8]", 0, ""),
    ("ldp_pre", "MemPair T T PreIndex 1w 2w 31w 126w", "ldp x1,x2,[sp,#-16]!", -1, "stack"),
    ("stp_pre", "MemPair F T PreIndex 1w 2w 31w 126w", "stp x1,x2,[sp,#-16]!", -1, "stack"),
    ("ldp_post", "MemPair T T PostIndex 1w 2w 31w 2w", "ldp x1,x2,[sp],#16", -1, "stack"),
    ("stp_post", "MemPair F T PostIndex 1w 2w 31w 2w", "stp x1,x2,[sp],#16", -1, "stack"),
    ("andmask_sp", "AndByteMask 31w 1w", "and wsp,w1,#255", -1, "sp_result"),
    ("b_back", "BranchImm F 0x3fffffew", "b 1b", -1, "backward"),
    ("bl_back", "BranchImm T 0x3fffffew", "bl 1b", -1, "backward"),
    ("ldrh_sxtw", "MemReg T 1w 1w 0w 2w 6w T", "ldrh w1,[x0,w2,sxtw #1]", 0, "indexed"),
    ("ldr_sxtx", "MemReg T 2w 1w 0w 2w 7w T", "ldr w1,[x0,x2,sxtx #2]", 0, "indexed"),
    ("ldp_w_pre", "MemPair T F PreIndex 1w 2w 31w 126w", "ldp w1,w2,[sp,#-8]!", -1, "stack"),
    ("stp_w_pre", "MemPair F F PreIndex 1w 2w 31w 126w", "stp w1,w2,[sp,#-8]!", -1, "stack"),
    ("ldp_w_post", "MemPair T F PostIndex 1w 2w 31w 2w", "ldp w1,w2,[sp],#8", -1, "stack"),
    ("stp_w_post", "MemPair F F PostIndex 1w 2w 31w 2w", "stp w1,w2,[sp],#8", -1, "stack"),
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
    ("ubfx_w", "Bitfield F F 0w 1w 8w 15w", "ubfx w0,w1,#8,#8", -1, ""),
    ("lsr_imm", "Bitfield T F 0w 1w 3w 63w", "lsr x0,x1,#3", -1, ""),
    ("ldr_pre", "MemImm T 3w 1w 0w (Unscaled PreIndex 8w)", "ldr x1,[x0,#8]!", 0, ""),
    ("stur_w", "MemImm F 2w 1w 0w (Unscaled Offset 3w)", "stur w1,[x0,#3]", 0, ""),
    ("addimm_sp", "AddImm T F F F 0w 31w 16w", "add x0,sp,#16", 0, "stack"),
    ("subimm_sp", "AddImm T T F F 31w 31w 16w", "sub sp,sp,#16", -1, "stack"),
    ("lslv_x", "VariableShift T 0w 0w 1w 2w", "lsl x0,x1,x2", -1, ""),
    ("lsrv_w", "VariableShift F 1w 0w 1w 2w", "lsr w0,w1,w2", -1, ""),
    ("asrv_x", "VariableShift T 2w 0w 1w 2w", "asr x0,x1,x2", -1, ""),
    ("ldr_pre_neg", "MemImm T 3w 1w 0w (Unscaled PreIndex 504w)", "ldr x1,[x0,#-8]!", 0, ""),
    ("stur_w_neg", "MemImm F 2w 1w 0w (Unscaled Offset 509w)", "stur w1,[x0,#-3]", 0, ""),
    ("tbnz_back", "TestBranch T 5w 1w 16382w", "tbnz w1,#5,1b", -1, "backward"),
    ("and_rem", "AndTailMask T 0w 1w", "and w0,w1,#3", -1, ""),
    ("and_blocks", "AndTailMask F 0w 1w", "and w0,w1,#4294967292", -1, ""),
    ("tst_byte", "TstLowMask F 1w", "tst w1,#255", -1, ""),
    ("tst_half", "TstLowMask T 1w", "tst w1,#65535", -1, ""),
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
    ("and_one", "LogicalMask AndOneX 0w 1w", "and x0,x1,#1", -1, ""),
    ("and_nibble", "LogicalMask AndNibbleX 0w 1w", "and x0,x1,#15", -1, ""),
    ("and_shift", "LogicalMask AndShiftCountW 0w 1w", "and w0,w1,#63", -1, ""),
    ("orr_shift", "LogicalMask OrrShiftHighW 0w 1w", "orr w0,w1,#4294967232", -1, ""),
    ("rorv_x", "VariableShift T 3w 0w 1w 2w", "ror x0,x1,x2", -1, ""),
    ("rorv_w", "VariableShift F 3w 0w 1w 2w", "ror w0,w1,w2", -1, ""),
    ("ror_imm", "Extract F 0w 1w 1w 7w", "ror w0,w1,#7", -1, ""),
    ("adr", "PcAddress F 0w 12w", "adr x0,.+12", -1, "adr"),
    ("adr_back", "PcAddress F 0w 0x1ffff4w", "adr x0,.-12", -1, "adr_back"),
    ("adrp", "PcAddress T 0w 1w", ".inst 0xb0000000", -1, "adrp"),
    ("adrp_back", "PcAddress T 0w 0x1fffffw", ".inst 0xf0ffffe0", -1, "adrp_back"),
    ("ccmp_n", "CompareImm T 0w 9w 8w 8w", "ccmp x0,#9,#8,hi", -1, "ccmp_fallback"),
    ("ccmp_z", "CompareImm T 0w 9w 8w 4w", "ccmp x0,#9,#4,hi", -1, "ccmp_fallback"),
    ("ccmp_v", "CompareImm T 0w 9w 8w 1w", "ccmp x0,#9,#1,hi", -1, "ccmp_fallback"),
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
}

# In the pinned L3 decoder, bit 10 sends the CLZ encodings to CLS.
L3_CLZ_FORMS = {"clz_x", "clz_w"}

PC_DISASSEMBLY = {
    "adr": "adr x0,12", "adr_back": "adr x0,-12",
    "adrp": "adrp x0,4096", "adrp_back": "adrp x0,-4096",
}

for name, instruction, assembly, _, mode in SCALAR_PROBES:
    expected = PC_DISASSEMBLY.get(mode, assembly)
    if mode == "branch":
        expected = assembly.replace("1f", "8")
    elif mode == "backward":
        expected = assembly.replace("1b", "-8")
    mnemonic, operands = expected.split(" ", 1)
    expected = f"{mnemonic} {''.join(operands.split())}"
    expected = re.sub(r"#0x[0-9a-f]+", lambda m: f"#{int(m[0][1:], 16)}", expected)
    PROBES[name] = instruction, (expected, *SCALAR_ALIASES.get(name, ()))
    if name not in L3_CLZ_FORMS:
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
            macro = "stack_probe" if mode in ("stack", "sp_result") else "straight"
            asm += [f'{macro} {name}, "{instruction}"']
        declaration = f"X({name}, {pointer}, {int(mode == 'indexed')}, {int(mode == 'stack')}, 0)"
        if mode == "ccmp_fallback":
            fallback.append(declaration)
        elif name.startswith("crc32"):
            crc.append(declaration)
        else:
            declarations.append(declaration)
    (directory / "scalar_probes.S").write_text("\n".join(asm) + "\n")
    (directory / "scalar_probes.h").write_text(
        "#define SCALAR_CASES(X) " + " ".join(declarations) + "\n"
        "#define CCMP_FALLBACK_CASES(X) " + " ".join(fallback) + "\n"
        "#define CRC_CASES(X) " + " ".join(crc) + "\n"
    )


# Each SIMD form has a V30/V31 case. ADD also exercises the rest of the bank.
SIMD_PAIR_BASES = range(0, 32, 2)
HIGH_SIMD_PROBES = [
    ("ldr_q", "LdrQ 30w 1w (Scaled 1w)", "ldr q30,[x1,#16]", 1, ()),
    ("ldr_q_post", "LdrQ 31w 1w (Unscaled PostIndex 16w)", "ldr q31,[x1],#16", 1, ()),
    ("ldr_q_post_neg", "LdrQ 30w 1w (Unscaled PostIndex 496w)", "ldr q30,[x1],#-16", 1, ()),
    ("movi_4s", "MoviZero4S 30w", "movi v30.4s,#0", -1, ()),
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
]

SIMD_PROBES = [
    (*probe, 30) for probe in HIGH_SIMD_PROBES
] + [
    (f"add_4s_v{base}", f"SimdBinary Add4S {base}w {base}w {base + 1}w",
     f"add v{base}.4s,v{base}.4s,v{base + 1}.4s", -1, (), base)
    for base in SIMD_PAIR_BASES if base != 30
]

PERMUTE_PROBES = [
    ("str_q", "StrQ 31w 0w 1w", "str q31,[x0,#16]", 0),
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
]

for name, instruction, assembly, _, aliases, _ in SIMD_PROBES + PERMUTE_SIMD_PROBES + CRYPTO_SIMD_PROBES:
    PROBES[name] = instruction, (assembly, *aliases)


def write_simd_probes(directory: Path) -> None:
    asm = [f'straight {name}, "{assembly}"' for name, _, assembly, _, _, _ in SIMD_PROBES + PERMUTE_SIMD_PROBES + CRYPTO_SIMD_PROBES]
    cases = [
        f"X({name}, {pointer}, 0, 0, {base})" for name, _, _, pointer, _, base in SIMD_PROBES
    ]
    # Native dispatch uses the even register number times four as a byte offset.
    for label, op, done in (("load", "ldp", "loads"), ("store", "stp", "stores")):
        asm.append(f".L{label}_pairs:")
        for base in SIMD_PAIR_BASES:
            asm += [f"    {op} q{base}, q{base + 1}, [x9, #32]", f"    b .L{done}_done"]
    permute_cases = [
        f"X({name}, {pointer}, 0, 0, {base})"
        for name, _, _, pointer, _, base in PERMUTE_SIMD_PROBES
    ]
    crypto_cases = [
        f"X({name}, {pointer}, 0, 0, {base})"
        for name, _, _, pointer, _, base in CRYPTO_SIMD_PROBES
    ]
    (directory / "simd_probes.S").write_text("\n".join(asm) + "\n")
    (directory / "simd_probes.h").write_text(
        "#define SIMD_CASES(X) " + " ".join(cases)
        + "\n#define PERMUTE_CASES(X) " + " ".join(permute_cases) + "\n"
        "#define CRYPTO_SIMD_CASES(X) " + " ".join(crypto_cases) + "\n"
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
    if len(fields) != 13:
        raise ValueError(f"expected thirteen state fields, got {row}")
    pc = 256 + int(fields[0])
    sp = int(fields[1], 16)
    nzcv = int(fields[2], 16)
    registers = [int(w, 16) for w in fields[3:7]]
    vectors = [int(w, 16) for w in fields[7:11]]
    link = int(fields[11], 16)
    data = bytes.fromhex(fields[12])
    if len(data) != 64:
        raise ValueError(f"expected 64 bytes, got {len(data)}")
    regs = [f"0x{w:016x}w" for w in registers]
    packed = [vectors[i] | (vectors[i + 1] << 64) for i in (0, 2)]
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
        command("/usr/bin/as", "-march=armv8-a+crc+crypto", "-I", temporary, "-o", obj, directory / "native_a64.S")
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
             ""]
    l3_cases = []
    l3_clz_zero = []
    crc_cases = []
    simd_cases = []
    simd_bases = {name: base for name, *_, base in SIMD_PROBES + PERMUTE_SIMD_PROBES + CRYPTO_SIMD_PROBES}
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

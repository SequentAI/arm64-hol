#!/usr/bin/env python3
"""Fixture-independent A64 EL0 inventory and HOL4 coverage checker.

The inventory is intentionally versioned in this file.  Its denominator does not
come from generated C bytes or native fixtures.  The checker reads only HOL4
source and theory/test scripts, and keeps decode, execution, and validation
signals separate in the report.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import shutil
import subprocess
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

INVENTORY_VERSION = "a64-el0-v1.1-armv9.4"
INVENTORY_SOURCE = "Arm DDI 0487 and DDI 0602 A64 instruction descriptions"
ARCHITECTURAL_TOTAL = 127


@dataclass(frozen=True)
class Form:
    form_id: str
    family: str
    constructor: str | None
    mask: int
    opcode: int
    variants: tuple[str, ...]
    architectural_status: str = "implemented"
    feature: str = "base"
    validation_hint: str = ""
    probe_words: tuple[int, ...] = ()
    encoding_partitions: tuple[tuple[int, int], ...] = ()


def _add_imm_probes(base: int) -> tuple[int, ...]:
    return tuple(
        base | (sub << 30) | (flags << 29) | (shift << 22)
        for sub in (0, 1) for flags in (0, 1) for shift in (0, 1)
    )


def _add_shift_probes(base: int) -> tuple[int, ...]:
    return tuple(
        base | (sub << 30) | (flags << 29) | (shift << 22) | ((shift + 1) << 10)
        for sub in (0, 1) for flags in (0, 1) for shift in (0, 1, 2)
    )


def _add_extend_probes(base: int) -> tuple[int, ...]:
    return tuple(
        base | (sub << 30) | (flags << 29) | (option << 13) | (amount << 10)
        for sub in (0, 1) for flags in (0, 1)
        for option in range(8) for amount in range(5)
    )


def _add_carry_probes(base: int) -> tuple[int, ...]:
    return tuple(base | (sub << 30) | (flags << 29)
                 for sub in (0, 1) for flags in (0, 1))


def _crc32_probes() -> tuple[int, ...]:
    return tuple(
        0x1AC04000 | (castagnoli << 12) | (size << 10) | ((size == 3) << 31)
        for castagnoli in (0, 1) for size in range(4)
    )


def _mul_high_probes() -> tuple[int, ...]:
    return (0x9B407C00, 0x9BC07C00)


# Masks/opcodes are the fixed fields from the Arm A64 encoding tables.  A row is
# an encoding partition at one architectural granularity.  The HOL model exposes
# its six logical-mask literals as separate partitions, so those literals stay
# explicit rather than being inferred from compiler fixtures.
INVENTORY: tuple[Form, ...] = (
    # Data processing immediate.
    Form("dp-imm.addsub-immediate.w", "data processing immediate", "AddImm", 0x9F800000, 0x11000000, ("sf=W", "S=0/1", "sub=0/1", "shift=0/12"), probe_words=_add_imm_probes(0x11000000)),
    Form("dp-imm.addsub-immediate.x", "data processing immediate", "AddImm", 0x9F800000, 0x91000000, ("sf=X", "S=0/1", "sub=0/1", "shift=0/12"), probe_words=_add_imm_probes(0x91000000)),
    Form("dp-imm.move-wide-zero.w", "data processing immediate", "MoveZero", 0xFF800000, 0x52800000, ("MOVZ", "sf=W", "hw=0/1")),
    Form("dp-imm.move-wide-zero.x", "data processing immediate", "MoveZero", 0xFF800000, 0xD2800000, ("MOVZ", "sf=X", "hw=0/1/2/3"), probe_words=(0xD2800000,)),
    Form("dp-imm.move-wide-not", "data processing immediate", "MoveNot", 0x7F800000, 0x12800000, ("MOVN", "sf=W/X", "hw=0/1"), "valid_but_unimplemented"),
    Form("dp-imm.move-wide-keep", "data processing immediate", "MoveKeep", 0x7F800000, 0x72800000, ("MOVK", "sf=W/X", "hw=0/1"), "valid_but_unimplemented"),
    Form("dp-reg.compare-immediate", "data processing register", "CompareImm", 0x7FE00C10, 0x7A400800, ("sf=W/X", "condition", "NZCV")),
    Form("dp-imm.pc-relative", "data processing immediate", "PcAddress", 0x1F000000, 0x10000000, ("ADR/ADRP", "sf=0/1")),
    Form("dp-imm.logical-mask-and", "data processing immediate", "LogicalMask", 0x7F800000, 0x12000000, ("AND W/X logical immediate", "modeled literals: 0x92400000, 0x92400c00, 0x12001400, 0x12001800, 0x92401800"), "partially_implemented", probe_words=(0x92400000, 0x92400C00, 0x12001400, 0x12001800, 0x92401800)),
    Form("dp-imm.logical-mask-orr", "data processing immediate", "LogicalMask", 0x7F800000, 0x32000000, ("ORR W/X logical immediate", "modeled literal: 0x321a6400"), "partially_implemented", probe_words=(0x321A6400,)),
    Form("dp-imm.and-byte-mask", "data processing immediate", "AndByteMask", 0xFFFFFC00, 0x12001C00, ("W" ,)),
    Form("dp-imm.and-tail-mask-t", "data processing immediate", "AndTailMask", 0xFFFFFC00, 0x12000400, ("tail mask T",)),
    Form("dp-imm.and-tail-mask-f", "data processing immediate", "AndTailMask", 0xFFFFFC00, 0x121E7400, ("tail mask F",), probe_words=(0x121E7400,)),
    Form("dp-imm.test-low-mask-byte", "data processing immediate", "TstLowMask", 0xFFFFFC1F, 0x72001C1F, ("byte",), validation_hint="TstLowMask F"),
    Form("dp-imm.test-low-mask-halfword", "data processing immediate", "TstLowMask", 0xFFFFFC1F, 0x72003C1F, ("halfword",), validation_hint="TstLowMask T"),
    Form("dp-imm.logical-immediate-eor", "data processing immediate", "LogicalImmediateEor", 0x7F800000, 0x52000000, ("EOR W/X logical immediate",), "valid_but_unimplemented"),
    Form("dp-imm.logical-immediate-ands", "data processing immediate", "LogicalImmediateAnds", 0x7F800000, 0x72000000, ("ANDS W/X logical immediate",), "valid_but_unimplemented", probe_words=(0x72000000,)),
    # Branches and EL0 system instructions.
    Form("branch.unconditional", "branches/system EL0", "BranchImm", 0x7C000000, 0x14000000, ("B/BL",)),
    Form("branch.conditional", "branches/system EL0", "BCond", 0xFF000010, 0x54000000, ("16 conditions",)),
    Form("branch.compare", "branches/system EL0", "CompareBranch", 0x7E000000, 0x34000000, ("CBZ/CBNZ", "W/X")),
    Form("branch.test", "branches/system EL0", "TestBranch", 0x7E000000, 0x36000000, ("TBZ/TBNZ", "W/X")),
    Form("branch.register", "branches/system EL0", "Br", 0xFFFFFC1F, 0xD61F0000, ("BR",)),
    Form("branch.register-link", "branches/system EL0", "Blr", 0xFFFFFC1F, 0xD63F0000, ("BLR",), "valid_but_unimplemented"),
    Form("branch.return", "branches/system EL0", "Ret", 0xFFFFFC1F, 0xD65F0000, ("RET",)),
    Form("system.nop", "branches/system EL0", "Nop", 0xFFFFFFFF, 0xD503201F, ("HINT #0",)),
    Form("system.svc", "branches/system EL0", "Svc", 0xFFE0001F, 0xD4000001, ("imm16",), "valid_but_unimplemented"),
    Form("system.brk", "branches/system EL0", "Brk", 0xFFE0001F, 0xD4200000, ("imm16",), "valid_but_unimplemented", probe_words=(0xD4200000,)),
    Form("system.hint-yield", "branches/system EL0", "Hint", 0xFFFFFFFF, 0xD503203F, ("YIELD",), "valid_but_unimplemented"),
    Form("system.hint-wfe", "branches/system EL0", "Hint", 0xFFFFFFFF, 0xD503205F, ("WFE",), "valid_but_unimplemented"),
    Form("system.hint-wfi", "branches/system EL0", "Hint", 0xFFFFFFFF, 0xD503207F, ("WFI",), "valid_but_unimplemented"),
    Form("system.hint-sev", "branches/system EL0", "Hint", 0xFFFFFFFF, 0xD503209F, ("SEV",), "valid_but_unimplemented"),
    Form("system.hint-sevl", "branches/system EL0", "Hint", 0xFFFFFFFF, 0xD50320BF, ("SEVL",), "valid_but_unimplemented", probe_words=(0xD50320BF,)),
    Form("system.barrier-dmb", "branches/system EL0", "Barrier", 0xFFFFF0FF, 0xD50330BF, ("DMB",), "valid_but_unimplemented"),
    Form("system.barrier-dsb", "branches/system EL0", "Barrier", 0xFFFFF0FF, 0xD503309F, ("DSB",), "valid_but_unimplemented"),
    Form("system.barrier-isb", "branches/system EL0", "Barrier", 0xFFFFF0FF, 0xD50330DF, ("ISB",), "valid_but_unimplemented"),
    # Loads and stores.
    Form("load-store.single-immediate-scaled", "loads/stores", "MemImm", 0x3F800000, 0x39000000, ("B/H/W/X", "scaled unsigned offset")),
    Form("load-store.single-immediate-unscaled", "loads/stores", "MemImm", 0x3FA00000, 0x38000000, ("B/H/W/X", "unscaled/pre/post-index"), probe_words=(0x38401441,)),
    Form("load-store.single-unprivileged", "loads/stores", "MemImm", 0x3FA00C00, 0x38000800, ("B/H/W/X", "unprivileged"), "valid_but_unimplemented", probe_words=(0x38000820,)),
    Form("load-store.single-register", "loads/stores", "MemReg", 0x3FA00C00, 0x38200800, ("B/H/W/X", "extend/shift"), probe_words=(0x38204800,)),
    Form("load-store.pair", "loads/stores", "MemPair", 0x7E000000, 0x28000000, ("W/X", "offset/pre/post-index"), probe_words=(0x28800440,)),
    Form("load-store.pair-nontemporal", "loads/stores", "MemPair", 0x7F800000, 0x28000000, ("LDNP/STNP",), "valid_but_unimplemented", probe_words=(0xA8000440,)),
    Form("load-store.q-pair-load", "loads/stores", "LdpQ", 0xFFC00000, 0xAD400000, ("Q", "offset"), feature="asimd", probe_words=(0xAD400440,)),
    Form("load-store.q-pair-store", "loads/stores", "StpQ", 0xFFC00000, 0xAD000000, ("Q", "offset"), feature="asimd"),
    Form("load-store.q-load", "loads/stores", "LdrQ", 0xFFC00000, 0x3DC00000, ("Q", "scaled unsigned offset"), feature="asimd"),
    Form("load-store.q-load-post", "loads/stores", "LdrQ", 0xFFE00C00, 0x3CC00400, ("Q", "post-index"), "implemented", "asimd"),
    Form("load-store.q-load-pre", "loads/stores", "LdrQ", 0xFFE00C00, 0x3CC00C00, ("Q", "pre-index"), "valid_but_unimplemented", "asimd", probe_words=(0x3CC00C00,)),
    Form("load-store.q-store", "loads/stores", "StrQ", 0xFFC00000, 0x3D800000, ("Q", "scaled"), feature="asimd"),
    Form("load-store.literal", "loads/stores", "LdrLiteral", 0xFF000000, 0x18000000, ("LDR literal", "W/X/LDRSW/S/D/Q"), "valid_but_unimplemented", probe_words=(0x18000000, 0x58000000, 0x98000000, 0x1C000000, 0x5C000000, 0x9C000000), encoding_partitions=((0xFF000000, 0x18000000), (0xFF000000, 0x58000000), (0xFF000000, 0x98000000), (0xFF000000, 0x1C000000), (0xFF000000, 0x5C000000), (0xFF000000, 0x9C000000))),
    Form("load-store.exclusive", "loads/stores", "Exclusive", 0x3F20FC00, 0x08007C00, ("LDXR/STXR", "B/H/W/X"), "valid_but_unimplemented"),
    Form("load-store.acquire-release", "loads/stores", "AcquireRelease", 0x3F20FC00, 0x0800FC00, ("LDAXR/STLXR", "B/H/W/X"), "valid_but_unimplemented"),
    # Data processing register.
    Form("dp-reg.addsub-shifted.w", "data processing register", "AddShift", 0x9F200000, 0x0B000000, ("sf=W", "S=0/1", "sub=0/1", "LSL/LSR/ASR"), probe_words=_add_shift_probes(0x0b000000)),
    Form("dp-reg.addsub-shifted.x", "data processing register", "AddShift", 0x9F200000, 0x8B000000, ("sf=X", "S=0/1", "sub=0/1", "LSL/LSR/ASR"), probe_words=_add_shift_probes(0x8b000000)),
    Form("dp-reg.addsub-extended.w", "data processing register", "AddExtend", 0x9FE00000, 0x0B200000, ("sf=W", "S=0/1", "sub=0/1", "UXTB..SXTX", "#0..#4"), probe_words=_add_extend_probes(0x0b200000)),
    Form("dp-reg.addsub-extended.x", "data processing register", "AddExtend", 0x9FE00000, 0x8B200000, ("sf=X", "S=0/1", "sub=0/1", "UXTB..SXTX", "#0..#4"), probe_words=_add_extend_probes(0x8b200000)),
    Form("dp-reg.addsub-carry.w", "data processing register", "AddCarry", 0x9FE0FC00, 0x1A000000, ("sf=W", "S=0/1", "ADC/SBC"), probe_words=_add_carry_probes(0x1a000000)),
    Form("dp-reg.addsub-carry.x", "data processing register", "AddCarry", 0x9FE0FC00, 0x9A000000, ("sf=X", "S=0/1", "ADC/SBC"), probe_words=_add_carry_probes(0x9a000000)),
    Form("dp-reg.logical-shifted", "data processing register", "LogicalReg", 0x1F000000, 0x0A000000, ("AND/ORR/EOR/ANDS", "W/X", "shift")),
    Form("dp-reg.variable-shift", "data processing register", "VariableShift", 0x7FE0F000, 0x1AC02000, ("LSL/LSR/ASR/ROR", "W/X")),
    Form("dp-imm.bitfield", "data processing immediate", "Bitfield", 0x3F800000, 0x13000000, ("SBFM/UBFM", "W/X")),
    Form("dp-imm.bitfield-bfm", "data processing immediate", "Bitfield", 0x3F800000, 0x33000000, ("BFM", "W/X"), "valid_but_unimplemented"),
    Form("dp-imm.extract", "data processing immediate", "Extract", 0x7FA00000, 0x13800000, ("W/X", "#0..#63")),
    Form("dp-reg.conditional-select", "data processing register", "Select", 0x3FE00800, 0x1A800000, ("CSEL/CSINC/CSINV/CSNEG", "W/X")),
    Form("dp-reg.signed-multiply-long", "data processing register", "SignedMulLong", 0xFFE0FC00, 0x9B207C00, ("SMULL",)),
    Form("dp-reg.multiply-add", "data processing register", "MulAdd", 0x7FE00000, 0x1B000000, ("MADD/MSUB", "W/X")),
    Form("dp-reg.multiply-high", "data processing register", "MulHigh", 0xFF60FC00, 0x9B407C00, ("SMULH/UMULH",), probe_words=_mul_high_probes()),
    Form("dp-reg.divide", "data processing register", "Divide", 0x7FE0F800, 0x1AC00800, ("UDIV/SDIV", "W/X")),
    Form("dp-reg.clz.w", "data processing register", "BitOp", 0xFFFFFC00, 0x5AC01000, ("CLZ", "sf=W"), validation_hint="Clz"),
    Form("dp-reg.clz.x", "data processing register", "BitOp", 0xFFFFFC00, 0xDAC01000, ("CLZ", "sf=X"), validation_hint="Clz"),
    Form("dp-reg.cls.w", "data processing register", "BitOp", 0xFFFFFC00, 0x5AC01400, ("CLS", "sf=W"), "valid_but_unimplemented", validation_hint="Cls", probe_words=(0x5AC01400,)),
    Form("dp-reg.cls.x", "data processing register", "BitOp", 0xFFFFFC00, 0xDAC01400, ("CLS", "sf=X"), "valid_but_unimplemented", validation_hint="Cls", probe_words=(0xDAC01400,)),
    Form("dp-reg.rbit.w", "data processing register", "BitOp", 0xFFFFFC00, 0x5AC00000, ("RBIT", "sf=W"), validation_hint="Rbit"),
    Form("dp-reg.rbit.x", "data processing register", "BitOp", 0xFFFFFC00, 0xDAC00000, ("RBIT", "sf=X"), validation_hint="Rbit"),
    Form("dp-reg.rev.w", "data processing register", "BitOp", 0xFFFFFC00, 0x5AC00800, ("REV", "sf=W"), validation_hint="Rev"),
    Form("dp-reg.rev.x", "data processing register", "BitOp", 0xFFFFFC00, 0xDAC00C00, ("REV", "sf=X"), validation_hint="Rev"),
    Form("dp-reg.rev16.w", "data processing register", "BitOp", 0xFFFFFC00, 0x5AC00400, ("REV16", "sf=W"), "valid_but_unimplemented", validation_hint="Rev16", probe_words=(0x5AC00400,)),
    Form("dp-reg.rev16.x", "data processing register", "BitOp", 0xFFFFFC00, 0xDAC00400, ("REV16", "sf=X"), "valid_but_unimplemented", validation_hint="Rev16", probe_words=(0xDAC00400,)),
    Form("dp-reg.ccmp", "data processing register", "Ccmp", 0x7FE00C10, 0x7A400000, ("CCMP", "W/X"), "valid_but_unimplemented"),
    # AdvSIMD and crypto.
    Form("simd.movi-zero", "AdvSIMD/crypto", "MoviZero", 0xFFFFFFE0, 0x6F00E400, ("MOVI Vd.2D,#0",), feature="asimd"),
    Form("simd.movi-zero-4s", "AdvSIMD/crypto", "MoviZero4S", 0xFFFFFFE0, 0x4F000400, ("MOVI Vd.4S,#0",), feature="asimd"),
    Form("simd.binary.add4s", "AdvSIMD/crypto", "SimdBinary", 0xFFE0FC00, 0x4EA08400, ("ADD V.4S",), feature="asimd"),
    Form("simd.binary.add2d", "AdvSIMD/crypto", "SimdBinary", 0xFFE0FC00, 0x4EE08400, ("ADD V.2D",), feature="asimd", probe_words=(0x4EE08400,)),
    Form("simd.binary.cmeq16b", "AdvSIMD/crypto", "SimdBinary", 0xFFE0FC00, 0x6E208C00, ("CMEQ V.16B",), feature="asimd", probe_words=(0x6E208C00,)),
    Form("simd.binary.eor16b", "AdvSIMD/crypto", "SimdBinary", 0xFFE0FC00, 0x6E201C00, ("EOR V.16B",), feature="asimd", probe_words=(0x6E201C00,)),
    Form("simd.binary.orr16b", "AdvSIMD/crypto", "SimdBinary", 0xFFE0FC00, 0x4EA01C00, ("ORR V.16B",), feature="asimd", probe_words=(0x4EA01C00,)),
    Form("simd.binary.add16b", "AdvSIMD/crypto", "SimdBinary", 0xFFE0FC00, 0x4E228400, ("ADD V.16B",), "valid_but_unimplemented", "asimd", probe_words=(0x4E228420,)),
    Form("simd.binary.add8h", "AdvSIMD/crypto", "SimdBinary", 0xFFE0FC00, 0x4E628400, ("ADD V.8H",), "valid_but_unimplemented", "asimd", probe_words=(0x4E628420,)),
    Form("simd.binary.sub16b", "AdvSIMD/crypto", "SimdBinary", 0xFFE0FC00, 0x6E228400, ("SUB V.16B",), "valid_but_unimplemented", "asimd", probe_words=(0x6E228420,)),
    Form("simd.unary.cmeq-zero", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x4E209800, ("CMEQ zero",), feature="asimd", probe_words=(0x4E209800,)),
    Form("simd.unary.uminv", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x6E31A800, ("UMINV",), feature="asimd", probe_words=(0x6E31A800,)),
    Form("simd.unary.addv4s", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x4EB1B800, ("ADDV V.4S",), feature="asimd", probe_words=(0x4EB1B800,)),
    Form("simd.unary.addv8h", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x4E71B800, ("ADDV V.8H",), feature="asimd", probe_words=(0x4E71B800,)),
    Form("simd.unary.uaddlp16b", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x6E202800, ("UADDLP",), feature="asimd", probe_words=(0x6E202800,)),
    Form("simd.unary.uadalp16b", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x6E206800, ("UADALP",), feature="asimd", probe_words=(0x6E206800,)),
    Form("simd.unary.cnt8b", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x0E205800, ("CNT",), feature="asimd", probe_words=(0x0E205800,)),
    Form("simd.unary.addv8b", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x0E31B800, ("ADDV V.8B",), feature="asimd", probe_words=(0x0E31B800,)),
    Form("simd.unary.rev16", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x4E201800, ("REV16",), feature="asimd"),
    Form("simd.unary.rev32b", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x6E200800, ("REV32 V.16B",), feature="asimd", probe_words=(0x6E200800,)),
    Form("simd.unary.rev32h", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x6E600800, ("REV32 V.8H",), feature="asimd", probe_words=(0x6E600800,)),
    Form("simd.unary.rev64b", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x4E200800, ("REV64 V.16B",), feature="asimd", probe_words=(0x4E200800,)),
    Form("simd.unary.rev64h", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x4E600800, ("REV64 V.8H",), feature="asimd", probe_words=(0x4E600800,)),
    Form("simd.unary.rev64s", "AdvSIMD/crypto", "SimdUnary", 0xFFFFFC00, 0x4EA00800, ("REV64 V.4S",), feature="asimd", probe_words=(0x4EA00800,)),
    Form("simd.table.tbl", "AdvSIMD/crypto", "SimdTable", 0xFFE0FC00, 0x4E000000, ("TBL",), feature="asimd"),
    Form("simd.table.tbx", "AdvSIMD/crypto", "SimdTable", 0xFFE0FC00, 0x4E001000, ("TBX",), feature="asimd", probe_words=(0x4E001000,)),
    Form("simd.extract", "AdvSIMD/crypto", "SimdExtract", 0xFFE08400, 0x6E000000, ("EXT",), feature="asimd"),
    Form("simd.shift", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x4F005400, ("SHL 32/64-bit lanes",), feature="asimd", probe_words=(0x4F205400, 0x4F405400)),
    Form("simd.shift-ushr", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x6F000400, ("USHR 32/64-bit lanes",), feature="asimd", probe_words=(0x6F200400, 0x6F400400)),
    Form("simd.shift-sri", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x6F004400, ("SRI 32/64-bit lanes",), feature="asimd", probe_words=(0x6F204400, 0x6F404400)),
    Form("simd.shift.shl-16", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x4F005400, ("SHL 16-bit lanes",), "valid_but_unimplemented", "asimd", probe_words=(0x4F105400,)),
    Form("simd.shift.shl-8", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x4F005400, ("SHL 8-bit lanes",), "valid_but_unimplemented", "asimd", probe_words=(0x4F085400,)),
    Form("simd.shift.ushr-16", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x6F000400, ("USHR 16-bit lanes",), "valid_but_unimplemented", "asimd", probe_words=(0x6F100400,)),
    Form("simd.shift.ushr-8", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x6F000400, ("USHR 8-bit lanes",), "valid_but_unimplemented", "asimd", probe_words=(0x6F080400,)),
    Form("simd.shift.sri-16", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x6F004400, ("SRI 16-bit lanes",), "valid_but_unimplemented", "asimd", probe_words=(0x6F104400,)),
    Form("simd.shift.sri-8", "AdvSIMD/crypto", "SimdShift", 0xFF80FC00, 0x6F004400, ("SRI 8-bit lanes",), "valid_but_unimplemented", "asimd", probe_words=(0x6F084400,)),
    Form("simd.transfer.fmov-w", "AdvSIMD/crypto", "SimdTransfer", 0xFFFFFC00, 0x1E260000, ("FMOV W",), feature="asimd"),
    Form("simd.transfer.fmov-x", "AdvSIMD/crypto", "SimdTransfer", 0xFFFFFC00, 0x9E660000, ("FMOV X",), feature="asimd", probe_words=(0x9E660000,)),
    Form("simd.transfer.umov-b0", "AdvSIMD/crypto", "SimdTransfer", 0xFFFFFC00, 0x0E013C00, ("UMOV B[0]",), feature="asimd", probe_words=(0x0E013C00,)),
    Form("simd.transfer.umov-d1", "AdvSIMD/crypto", "SimdTransfer", 0xFFFFFC00, 0x4E183C00, ("UMOV D[1]",), feature="asimd", probe_words=(0x4E183C00,)),
    Form("simd.transfer.dup2d", "AdvSIMD/crypto", "SimdTransfer", 0xFFFFFC00, 0x4E080C00, ("DUP 2D",), feature="asimd", probe_words=(0x4E080C00,)),
    Form("simd.transfer.fmov-to-d", "AdvSIMD/crypto", "SimdTransfer", 0xFFFFFC00, 0x9E670000, ("FMOV D",), feature="asimd", probe_words=(0x9E670000,)),
    Form("crypto.crc32", "AdvSIMD/crypto", "Crc32", 0x7FE0E000, 0x1AC04000, ("CRC32/CRC32C", "B/H/W/X", "sf=0 for B/H/W, sf=1 for X"), feature="crc32", probe_words=_crc32_probes()),
    Form("crypto.pmull", "AdvSIMD/crypto", "Pmull", 0xBFE0FC00, 0x0EE0E000, ("PMULL/PMULL2",), feature="pmull"),
    Form("crypto.aes.aese", "AdvSIMD/crypto", "Aes", 0xFFFFFC00, 0x4E284800, ("AESE",), "implemented", "aes", "Aese"),
    Form("crypto.aes.aesd", "AdvSIMD/crypto", "Aes", 0xFFFFFC00, 0x4E285800, ("AESD",), "implemented", "aes", "Aesd"),
    Form("crypto.aes.aesmc", "AdvSIMD/crypto", "Aes", 0xFFFFFC00, 0x4E286800, ("AESMC",), "implemented", "aes", "Aesmc"),
    Form("crypto.aes.aesimc", "AdvSIMD/crypto", "Aes", 0xFFFFFC00, 0x4E287800, ("AESIMC",), "implemented", "aes", "Aesimc"),
    Form("crypto.sha2", "AdvSIMD/crypto", "Sha2", 0xFFE0FC00, 0x5E000000, ("SHA1",), "valid_but_unimplemented", "asimd"),
    Form("crypto.sha2.sha256", "AdvSIMD/crypto", "Sha2", 0xFFE0FC00, 0x5E004000, ("SHA256",), "valid_but_unimplemented", "asimd", probe_words=(0x5E004000,)),
)

ADD_CONSTRUCTORS = {"AddImm", "AddShift", "AddExtend", "AddCarry"}
_HOL_TAGS = {
    "BranchImm": 1, "BCond": 2, "CompareBranch": 3, "TestBranch": 4,
    "Br": 5, "Ret": 6, "MoveZero": 7, "CompareImm": 8,
    "LogicalMask": 9, "PcAddress": 10, "AndByteMask": 11,
    "AndTailMask": 12, "TstLowMask": 13, "Nop": 14, "MemImm": 15,
    "MemReg": 16, "MemPair": 17, "LdpQ": 18, "StpQ": 19, "LdrQ": 20,
    "StrQ": 21, "LogicalReg": 22, "VariableShift": 23, "Bitfield": 24,
    "Extract": 25, "Select": 26, "SignedMulLong": 27, "MulAdd": 28,
    "MulHigh": 29, "Divide": 30, "BitOp": 31, "MoviZero": 32,
    "MoviZero4S": 33, "SimdBinary": 34, "SimdUnary": 35, "SimdTable": 36,
    "SimdExtract": 37, "SimdShift": 38, "SimdTransfer": 39, "Crc32": 40,
    "Pmull": 41, "Aes": 42,
}


def _hol_non_add_probe(form: Form, coverage_script: str) -> bool:
    tag = _HOL_TAGS.get(form.constructor or "")
    if tag is None:
        return False
    for match in re.finditer(r"Definition (a64_decode_coverage_probes_\w+)_def:.*?\nEnd", coverage_script, re.S):
        theorem = match.group(1)
        if not re.search(rf"Theorem\s+{re.escape(theorem)}_decode_encode\s*:", coverage_script):
            continue
        theorem_block = _block(coverage_script, f"Theorem {theorem}_decode_encode:")
        if not re.search(
            r"EVERY\s*\(λ\(w,t\)\.\s*case\s+decode\s+armv9_4\s+w\s+of\s+NONE\s*=>\s*F\s*\|\s*SOME\s+i\s*=>\s*coverage_tag\s+i\s*=\s*t\s*∧\s*encode\s+i\s*=\s*SOME\s+w\)",
            theorem_block,
        ):
            continue
        if not re.search(rf"\n\s+{re.escape(theorem)}\s*(?:\n|$)", theorem_block):
            continue
        definition = match.group(0)
        if all(re.search(rf"\(0x{word:08x}w\s*,\s*{tag}w\)", definition, re.I)
               for word in _probe_words(form)):
            return True
    return False


def _hol_add_probe(form: Form, coverage_script: str) -> bool:
    if form.constructor not in ADD_CONSTRUCTORS:
        return False
    width = next((variant for variant in form.variants if variant in ("sf=W", "sf=X")), None)
    if width is None:
        return False
    prefix = form.constructor[0].lower() + form.constructor[1:]
    width_name = "w" if width == "sf=W" else "x"
    stem = f"{prefix}_{width_name}_coverage_probes"
    blocks = []
    for match in re.finditer(rf"Definition ({re.escape(stem)}(?:_\d+)?)_def:.*?\nEnd", coverage_script, re.S):
        name = match.group(1)
        theorem = rf"Theorem\s+{re.escape(name)}_decode_encode\s*:"
        if not re.search(theorem, coverage_script):
            return False
        theorem_block = _block(coverage_script, f"Theorem {name}_decode_encode:")
        if not re.search(
            r"EVERY\s*\(λ\(w,i\)\.\s*decode\s+armv9_4\s+w\s*=\s*SOME\s+i\s*∧\s*encode\s+i\s*=\s*SOME\s+w\)",
            theorem_block,
        ):
            return False
        if not re.search(rf"\n\s+{re.escape(name)}\s*(?:\n|$)", theorem_block):
            return False
        blocks.append((name, match.group(0)))
    expected_blocks = (len(_probe_words(form)) + 15) // 16
    if len(blocks) != expected_blocks:
        return False
    return all(any(_hex_word(block, word) for _, block in blocks)
               for word in _probe_words(form))


def _hol_probe(form: Form, coverage_script: str) -> bool:
    return _hol_add_probe(form, coverage_script) if form.constructor in ADD_CONSTRUCTORS else _hol_non_add_probe(form, coverage_script)


def _hol_negative_probe(form: Form, coverage_script: str) -> bool:
    if form.architectural_status != "valid_but_unimplemented":
        return False
    for match in re.finditer(
        r"Definition (a64_decode_unimplemented_probes_\d+)_def:.*?\nEnd",
        coverage_script,
        re.S,
    ):
        name, definition = match.group(1), match.group(0)
        theorem_block = _block(coverage_script, f"Theorem {name}_none:")
        if not re.search(r"EVERY\s*\(λw\.\s*decode\s+armv9_4\s+w\s*=\s*NONE\)", theorem_block):
            continue
        if not re.search(rf"\)\s+{re.escape(name)}\s*(?:\n|$)", theorem_block):
            continue
        if all(_hex_word(definition, word) for word in _probe_words(form)):
            return True
    return False


def _hol_execution_probe(form: Form, coverage_script: str, execution_clause: str) -> bool:
    if not execution_clause:
        return False
    if form.constructor in ADD_CONSTRUCTORS:
        theorem = _block(coverage_script, "Theorem add_execute_with_forms:")
        required = (
            theorem,
            _block(coverage_script, "Theorem write_arith_flagged_outcome:"),
            _block(coverage_script, "Theorem write_arith_gpr_result:"),
            _block(coverage_script, "Theorem write_arith_sp_result:"),
            _block(coverage_script, "Theorem write_arith_unflagged_nzcv:"),
        )
        return _contains_word(theorem, f"Add{form.constructor[3:]}") and all(required)
    # The coverage theory currently proves execution equations only for the
    # integer ADD family.  A source-level execute_with equation is still
    # useful evidence, but it is not a HOL execution probe.
    return False


def _fault_test_evidence(root: Path, form: Form) -> bool:
    expected_faults = _execution_faults(form)
    if not expected_faults:
        return True
    tests = _source(root, "tests/arm64NativeScript.sml")
    names = {
        "load-store.single-immediate-unscaled": {
            "SPAlignment": ("sp_load_rejects_misaligned_base",),
            "Load": ("single_load_rejects_unreadable_last_byte",),
            "Store": ("single_store_rejects_executable_last_byte",),
        },
        "load-store.pair": {
            "SPAlignment": ("scalar_preindex_sp_checks_base",),
            "Load": ("scalar_pair_rejects_unreadable_last_byte",),
            "Store": ("scalar_pair_rejects_executable_last_byte",),
        },
        "load-store.q-pair-store": {
            "SPAlignment": ("q_pair_store_checks_sp_before_access",),
            "Store": ("store_rejects_read_only_last_byte", "store_rejects_executable_last_byte"),
            "Unsupported": ("q_store_requires_asimd",),
        },
        "load-store.q-load-post": {
            "SPAlignment": ("q_post_load_checks_sp_before_access",),
            "Load": ("q_post_load_rejects_unreadable_last_byte",),
        },
        "load-store.q-store": {
            "SPAlignment": ("q_store_checks_sp_before_access",),
            "Store": ("q_store_rejects_unwritable_last_byte",),
        },
        "crypto.crc32": {
            "Unsupported": ("crc_requires_crc32", "crc_rejects_wrong_sf"),
        },
        "crypto.pmull": {
            "Unsupported": ("pmull_requires_pmull", "pmull_rejects_unsupported_8h_form"),
        },
        "crypto.aes.aese": {"Unsupported": ("aese_requires_aes", "aese_requires_asimd")},
    }.get(form.form_id, {})
    return bool(names) and all(
        any(_contains_word(tests, name) for name in names.get(fault, ()))
        for fault in expected_faults
    )


def _feature_guarded(classify: str, form: Form) -> bool:
    token = f"feat.{form.feature}"
    if form.constructor in {"LdpQ", "StpQ", "Crc32", "Aes", "Pmull"}:
        return any(
            _contains_word(segment, form.constructor) and _contains_word(segment, token)
            for segment in re.split(r"\belse if\b", classify)
        )
    return _contains_word(classify, token) and _contains_word(classify, "classify_simd")


def _source(root: Path, relative: str) -> str:
    path = root / relative
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return ""


def _block(text: str, start: str, end: str = "End") -> str:
    begin = text.find(start)
    if begin < 0:
        return ""
    finish = text.find(end, begin + len(start))
    return text[begin:] if finish < 0 else text[begin:finish]


def _constructors(isa: str) -> set[str]:
    match = re.search(r"arm64_instr\s*=\s*(.*?)\nEnd", isa, re.S)
    if not match:
        return set()
    names = set()
    for line in match.group(1).splitlines():
        line = line.strip()
        if not line or line == "End":
            continue
        line = line.lstrip("|").strip()
        name = re.match(r"([A-Za-z][A-Za-z0-9_]*)", line)
        if name:
            names.add(name.group(1))
    return names


def _contains_word(text: str, word: str) -> bool:
    return re.search(rf"\b{re.escape(word)}\b", text) is not None


def _hex_word(text: str, value: int) -> bool:
    return re.search(rf"0x0*{value:x}w", text.lower()) is not None


def _source_mask_opcode(form: Form) -> tuple[int, int]:
    """Return the broad decode fields used by arm64Isa for a width row."""
    mask, opcode = form.mask, form.opcode
    if form.constructor == "SimdShift":
        return 0xFF80FC00, opcode & 0xFF80FC00
    if any(variant == "sf=W" or variant == "sf=X" for variant in form.variants):
        mask &= ~(1 << 31)
        opcode &= ~(1 << 31)
    return mask, opcode


def _probe_words(form: Form) -> tuple[int, ...]:
    """Representative words made from this row's fixed encoding fields."""
    return form.probe_words or (form.opcode,)


def _encoding_partitions(form: Form) -> tuple[tuple[int, int], ...]:
    return form.encoding_partitions or ((form.mask, form.opcode),)


def _encoding_matches(form: Form, word: int) -> bool:
    partitions = form.encoding_partitions or ((form.mask, form.opcode),)
    if not any((word & mask) == (opcode & mask) for mask, opcode in partitions):
        return False
    if form.constructor == "LdrLiteral":
        return True
    if form.form_id == "dp-imm.logical-immediate-ands":
        if (word & 0xFFFFFC1F) in {0x72001C1F, 0x72003C1F}:
            return False
    if form.form_id == "load-store.single-immediate-unscaled":
        return ((word >> 10) & 0x3) != 0x2
    if form.form_id == "load-store.pair":
        return ((word >> 23) & 0x3) != 0
    if form.form_id in {"dp-reg.addsub-shifted.w", "dp-reg.addsub-shifted.x"}:
        if ((word >> 22) & 0x3) == 0x3:
            return False
        if form.form_id.endswith(".w") and ((word >> 15) & 1):
            return False
    if form.form_id in {"dp-reg.addsub-extended.w", "dp-reg.addsub-extended.x"}:
        if ((word >> 10) & 0x7) > 4:
            return False
    if form.constructor == "SimdShift":
        immediate = (word >> 16) & 0x7F
        if form.architectural_status == "implemented":
            return immediate >= 32
        if form.form_id.endswith("-16"):
            return 16 <= immediate < 32
        if form.form_id.endswith("-8"):
            return 8 <= immediate < 16
    if form.constructor == "Crc32":
        return bool((word >> 31) & 1) == (((word >> 10) & 3) == 3)
    return True


def _case_has_form(text: str, form: Form) -> bool:
    constructor = form.constructor
    if not constructor or not _contains_word(text, constructor):
        return False
    width = next((v for v in form.variants if v in ("sf=W", "sf=X")), None)
    if width is None:
        return True
    expected = "F" if width == "sf=W" else "T"
    return re.search(rf"\b{re.escape(constructor)}\s+{expected}\b", text) is not None


def _execution_faults(form: Form) -> list[str]:
    constructor = form.constructor
    faults: list[str] = []
    if constructor in {"MemImm", "MemReg", "MemPair"}:
        faults.extend(("SPAlignment", "Load", "Store"))
    elif constructor == "LdrQ" or constructor == "LdpQ":
        faults.extend(("SPAlignment", "Load"))
    elif constructor == "StrQ" or constructor == "StpQ":
        faults.extend(("SPAlignment", "Store"))
    if form.feature in {"asimd", "crc32", "pmull", "aes"}:
        faults.append("Unsupported")
    return faults


def _execute_clause(execute: str, constructor: str | None) -> str:
    if not constructor:
        return ""
    if constructor == "Nop":
        match = re.search(r"execute_with ops Nop.*?(?=\n\s*execute_with ops |\nEnd|\Z)", execute, re.S)
        return match.group(0) if match else ""
    for segment in re.split(r"\n\s*(?:∧\s*)?execute_with ops \(", execute):
        if re.match(rf"{re.escape(constructor)}\b", segment.strip()):
            return segment
    return ""


def _execution_support(isa: str, execute: str, form: Form) -> tuple[bool, bool, str, bool]:
    clause = _execute_clause(execute, form.constructor)
    helper_name = {
        "MemImm": "execute_mem",
        "MemReg": "execute_mem",
        "MemPair": "execute_pair",
        "LdrQ": "execute_ldr_q",
    }.get(form.constructor)
    support = clause
    if helper_name and _contains_word(clause, helper_name):
        support += _block(isa, f"Definition {helper_name}_def:")
    if form.constructor in ADD_CONSTRUCTORS:
        support += _block(isa, "Definition write_arith_def:")
    state_update = bool(
        clause and "Next" in support and
        any(token in support for token in ("advance", "set_gpr", "set_base", "vregs :=", "pc :=", "write_bytes", "write_arith"))
    )
    if form.constructor in ADD_CONSTRUCTORS:
        state_update = state_update and re.search(r"write_arith\s+ops\s+[TF]\s+sf\s+sub\s+flags", clause) is not None
        state_update = state_update and all(_contains_word(support, token)
                                            for token in ("arm_add_with_carry", "if flags", "set_gpr", "nzcv"))
    execution = bool(clause and "Next" in support and state_update)
    expected_faults = _execution_faults(form)
    faults_modeled = execution and all(
        _contains_word(support, fault) for fault in expected_faults if fault != "Unsupported"
    )
    return execution, faults_modeled, clause, state_update


def _step_faults() -> list[str]:
    return ["PCAlignment", "Fetch", "Unsupported"]

def _named_indices(text: str, definition: str) -> set[int]:
    match = re.search(rf"Definition {re.escape(definition)}:.*?=\s*\[(.*?)\]\s*\nEnd", text, re.S)
    if not match:
        return set()
    return {int(value) for value in re.findall(r"\b(\d+)\b", match.group(1))}


def _native_cases(text: str) -> dict[int, str]:
    cases: dict[int, str] = {}
    for match in re.finditer(r"Definition native_case_(\d+)_def:.*?\nEnd", text, re.S):
        cases[int(match.group(1))] = match.group(0)
    return cases


def _case_matches_form(case: str, form: Form) -> bool:
    if not form.constructor or not _contains_word(case, form.constructor):
        return False
    if form.validation_hint and not _contains_word(case, form.validation_hint):
        return False
    word = re.search(r"\(\s*0x([0-9a-f]+)w\s*,", case, re.I)
    if not word:
        return False
    observed = int(word.group(1), 16)
    if not _encoding_matches(form, observed):
        return False
    width = next((v for v in form.variants if v in ("sf=W", "sf=X")), None)
    if width is None:
        return True
    expected = "F" if width == "sf=W" else "T"
    return re.search(rf"\b{re.escape(form.constructor)}\s+{expected}\b", case) is not None


def _code_has_form(code: str, form: Form) -> bool:
    return any(_encoding_wins(form, word)
               for word in (int(value, 16) for value in re.findall(r"0x([0-9a-f]+)w", code, re.I)))


def _encoding_wins(form: Form, word: int) -> bool:
    """Credit an encoding to the most specific inventory partition."""
    if not _encoding_matches(form, word):
        return False
    specificity = form.mask.bit_count()
    return not any(
        other is not form and _encoding_matches(other, word)
        and other.mask.bit_count() > specificity
        for other in INVENTORY
    )


def _contract_witnesses(root: Path, form: Form) -> list[str]:
    """Return contract theorems whose own code block contains this form."""
    witnesses: list[str] = []
    for proof_path in sorted((root / "examples").glob("*/*ProofScript.sml")):
        contracts = _source(root, str(proof_path.relative_to(root)))
        code_path = proof_path.with_name(proof_path.name.replace("ProofScript", "CodeScript"))
        code = _source(root, str(code_path.relative_to(root))) or contracts
        theory = proof_path.name.replace("Script.sml", "Theory")
        for match in re.finditer(
            r"Theorem\s+(\w+):\s*(.*?)(?=\n(?:Theorem|Definition|Triviality)\b|\Z)",
            contracts,
            re.S,
        ):
            theorem, theorem_block = match.groups()
            for code_name in re.findall(r"\bcode_at\s+\S+\s+\S+\s+(\w+_code)\b", theorem_block):
                code_block = _block(code, f"Definition {code_name}_def:")
                if _code_has_form(code_block, form):
                    witnesses.append(f"{theory}.{theorem}")
                    break
    return sorted(set(witnesses))


def _universal_theorems(root: Path, form: Form, decode: bool, hol_execution_probe: bool) -> list[str]:
    """Return form-level HOL theorems, separate from verified C contracts."""
    if not decode:
        return []
    sources: list[str] = []
    coverage_script = _source(root, "tests/arm64CoverageScript.sml")
    if form.constructor in ADD_CONSTRUCTORS and hol_execution_probe:
        for theorem in (
            "add_execute_with_forms",
            "write_arith_flagged_outcome",
            "write_arith_gpr_result",
            "write_arith_sp_result",
            "write_arith_unflagged_nzcv",
        ):
            if re.search(rf"Theorem\s+{theorem}\s*:", coverage_script):
                sources.append(f"arm64CoverageTheory.{theorem}")
    crypto = _source(root, "isa/arm64CryptoScript.sml")
    if form.constructor == "Aes":
        for theorem in ("aes_word_to_state", "aes_state_to_word"):
            if re.search(rf"Theorem\s+{theorem}(?:\[simp\])?\s*:", crypto):
                sources.append(f"arm64CryptoTheory.{theorem}")
    return sources


def _classify_branch_evidence(classify: str, form: Form, source_mask: int, source_opcode: int) -> bool:
    if not form.constructor:
        return False
    segments = re.split(r"\belse if\b", classify)
    for segment in segments:
        if not _contains_word(segment, form.constructor):
            continue
        if form.validation_hint and not _contains_word(segment, form.validation_hint):
            continue
        if _hex_word(segment, source_mask) and _hex_word(segment, source_opcode):
            return True
        if form.constructor in {"Aes", "LogicalMask", "BitOp", "SimdBinary", "SimdUnary", "SimdShift", "SimdTransfer"}:
            return True
    return False


def _source_rejects_probe(classify: str, form: Form, word: int) -> bool:
    """Recognize an explicit width guard in the affected classifier clause."""
    if form.constructor not in ADD_CONSTRUCTORS:
        return False
    expected = "T" if word & (1 << 31) else "F"
    for segment in re.split(r"\belse if\b", classify):
        if not _contains_word(segment, form.constructor):
            continue
        if re.search(rf"word_bit\s+31\s+w\s*=\s*{expected}\s+then\s+NONE", segment):
            return True
        if expected == "F" and re.search(r"¬\s*word_bit\s+31\s+w\s+then\s+NONE", segment):
            return True
        if expected == "T" and re.search(r"word_bit\s+31\s+w\s+then\s+NONE", segment):
            return True
        if expected == "F" and re.search(r"¬\s*sf\s+then\s+NONE", segment):
            return True
        if expected == "T" and re.search(r"\bsf\s+then\s+NONE", segment):
            return True
        if expected == "F" and re.search(r"\bsf\s*=\s*F\s+then\s+NONE", segment):
            return True
        if expected == "T" and re.search(r"\bsf\s*=\s*T\s+then\s+NONE", segment):
            return True
        if expected == "F" and re.search(r"if\s+sf\s+then\s+SOME\b.*?else\s+NONE", segment, re.S):
            return True
        if expected == "T" and re.search(r"if\s+sf\s+then\s+NONE\b.*?else\s+SOME", segment, re.S):
            return True
        if expected == "F" and re.search(r"if\s+word_bit\s+31\s+w\s+then\s+SOME\b.*?else\s+NONE", segment, re.S):
            return True
        if expected == "T" and re.search(r"if\s+word_bit\s+31\s+w\s+then\s+NONE\b.*?else\s+SOME", segment, re.S):
            return True
    return False


def _evidence(root: Path, form: Form, isa: str, hidden: set[str]) -> dict[str, object]:
    encode = _block(isa, "Definition encode_def:")
    classify = _block(isa, "Definition classify_def:") + _block(isa, "Definition classify_simd_def:")
    execute = _block(isa, "Definition execute_with_def:")
    constructor = form.constructor
    source_mask, source_opcode = _source_mask_opcode(form)
    probes = _probe_words(form)
    probe_shape_ok = all(_encoding_matches(form, word) for word in probes)
    source_fields_ok = (
        _hex_word(isa, source_opcode)
        if constructor == "Nop"
        else (_hex_word(classify, 0xFFFFFC00)
              if constructor == "LogicalMask"
              else _hex_word(classify, source_mask) and _hex_word(isa, source_opcode))
    )
    coverage_script = _source(root, "tests/arm64CoverageScript.sml")
    hol_probe = bool(constructor and _hol_probe(form, coverage_script))
    hol_negative_probe = _hol_negative_probe(form, coverage_script)
    branch_evidence = _classify_branch_evidence(classify, form, source_mask, source_opcode)
    rejected_probes = [word for word in probes if _source_rejects_probe(classify, form, word)]
    decode = bool(
        constructor
        and _contains_word(encode, constructor)
        and (branch_evidence or hol_probe)
        and probe_shape_ok
        and source_fields_ok
        and not rejected_probes
        and hol_probe
    )
    execution, faults_modeled, execution_clause, state_update_modeled = _execution_support(isa, execute, form)
    execution_faults = _execution_faults(form)
    hol_execution_probe = _hol_execution_probe(form, coverage_script, execution_clause)
    execution_evidence_level = (
        "theorem" if hol_execution_probe else
        "definition" if execution_clause else
        "none"
    )
    fault_test_evidence = _fault_test_evidence(root, form)
    if "Unsupported" in execution_faults:
        faults_modeled = faults_modeled and _feature_guarded(classify, form)
    if not hol_probe:
        execution = False
        faults_modeled = False
        state_update_modeled = False
    hidden_for_acceptance = form.form_id in hidden
    if hidden_for_acceptance:
        decode = False
        execution = False
    native_sources = _source(root, "tests/arm64NativeCasesScript.sml")
    l3_script = _source(root, "tests/arm64L3Script.sml")
    native_cases = _native_cases(native_sources)
    native = any(_case_matches_form(case, form) for case in native_cases.values()) and not hidden_for_acceptance
    l3_indices = _named_indices(native_sources, "native_l3_cases_def")
    crc_indices = _named_indices(native_sources, "native_crc_cases_def")
    l3_discrepancy_indices = _named_indices(native_sources, "native_l3_clz_zero_def")
    l3_integer_case = any(
        index in l3_indices and _case_matches_form(case, form)
        for index, case in native_cases.items()
    )
    l3_crc_case = any(
        index in crc_indices and _case_matches_form(case, form)
        for index, case in native_cases.items()
    )
    l3 = (
        (l3_integer_case and bool(re.search(r'"l3_agrees_"', l3_script)))
        or (l3_crc_case and bool(re.search(r'"l3_crc_agrees_"', l3_script)))
    )
    l3 = l3 and not hidden_for_acceptance
    l3_discrepancy = any(
        index in l3_discrepancy_indices and _case_matches_form(case, form)
        for index, case in native_cases.items()
    )
    universal_sources = _universal_theorems(root, form, decode, hol_execution_probe)
    contract_witnesses = _contract_witnesses(root, form) if decode else []
    definition_sources: list[str] = []
    if decode:
        definition_sources.append("arm64IsaTheory.encode_of_decode")
    if execution:
        definition_sources.append("arm64IsaTheory.execute_with_def")
    return {
        "decode": decode,
        "encode_round_trip": decode,
        "decode_probes": [f"0x{word:08x}" for word in probes],
        "hol_decode_probe": hol_probe,
        "hol_decode_negative_probe": hol_negative_probe,
        "execution": execution,
        "execution_clause": bool(execution_clause),
        "hol_execution_probe": hol_execution_probe,
        "execution_evidence_level": execution_evidence_level,
        "state_update_modeled": state_update_modeled,
        "execution_faults": execution_faults,
        "faults_modeled": faults_modeled,
        "fault_test_evidence": fault_test_evidence,
        "step_faults": _step_faults(),
        "native": native,
        "l3_arm8": l3,
        "l3_discrepancy": l3_discrepancy,
        "l3_discrepancy_sources": [
            f"arm64L3Theory.l3_clz_is_cls_native_case_{index}"
            for index in sorted(l3_discrepancy_indices)
            if index in native_cases and _case_matches_form(native_cases[index], form)
        ],
        "universal": bool(universal_sources),
        "universal_sources": universal_sources,
        "universal_contract_sources": contract_witnesses,
        "definition_sources": definition_sources,
        "verified_c_contract": bool(contract_witnesses),
        "hidden_for_acceptance": hidden_for_acceptance,
        "feature": form.feature,
    }

def coverage(root: Path, hidden: set[str] | None = None) -> dict[str, object]:
    isa = _source(root, "isa/arm64IsaScript.sml")
    hidden_set = hidden or set()
    constructors = _constructors(isa)
    rows: list[dict[str, object]] = []
    for form in INVENTORY:
        evidence = _evidence(root, form, isa, hidden_set)
        if form.architectural_status == "partially_implemented" and evidence["decode"] and evidence["execution"]:
            status = "partially_implemented"
        elif evidence["decode"] and evidence["execution"]:
            status = "implemented"
        elif evidence["decode"] or evidence["execution"]:
            status = "partially_implemented"
        else:
            status = "unimplemented"
        rows.append({
            **asdict(form),
            "mask": f"0x{form.mask:08x}",
            "opcode": f"0x{form.opcode:08x}",
            "encoding_partitions": [
                {"mask": f"0x{mask:08x}", "opcode": f"0x{opcode:08x}"}
                for mask, opcode in _encoding_partitions(form)
            ],
            "variants": list(form.variants),
            "evidence": evidence,
            "status": status,
            "constructor_declared": bool(form.constructor and form.constructor in constructors),
        })
    summary = {
        "architectural_total": len(rows),
        "implemented": sum(row["status"] == "implemented" for row in rows),
        "partially_implemented": sum(row["status"] == "partially_implemented" for row in rows),
        "unimplemented": sum(row["status"] == "unimplemented" for row in rows),
        "native_forms": sum(row["evidence"]["native"] for row in rows),
        "l3_forms": sum(row["evidence"]["l3_arm8"] for row in rows),
        "universal_forms": sum(row["evidence"]["universal"] for row in rows),
    }
    return {
        "inventory_version": INVENTORY_VERSION,
        "inventory_source": INVENTORY_SOURCE,
        "summary": summary,
        "rows": rows,
    }


def _coverage_with_marker(root: Path, form_id: str) -> dict[str, object]:
    """Run against a temporary ISA source with one real width guard inserted."""
    source_files = (
        "isa/arm64IsaScript.sml", "isa/arm64CryptoScript.sml", "prog/arm64ProgScript.sml",
        "arm64HolScript.sml", "tests/arm64NativeCasesScript.sml", "tests/arm64NativeScript.sml",
        "tests/arm64L3Script.sml", "tests/arm64CoverageScript.sml",
        "examples/c_crypto/c_cryptoCodeScript.sml", "examples/c_crypto/c_cryptoProofScript.sml",
    )
    matches = [item for item in INVENTORY if item.form_id == form_id]
    if not matches:
        raise ValueError(f"unknown form id for --hide: {form_id}")
    form = matches[0]
    if form.constructor not in ADD_CONSTRUCTORS:
        raise ValueError(f"--hide only supports ADD-family width rows: {form_id}")
    with tempfile.TemporaryDirectory(prefix="a64-coverage-") as directory:
        patched = Path(directory)
        for relative in source_files:
            destination = patched / relative
            source = root / relative
            if not source.exists():
                continue
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        for source in (root / "examples").glob("*/*Script.sml"):
            relative = source.relative_to(root)
            destination = patched / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        isa_path = patched / "isa/arm64IsaScript.sml"
        isa_text = isa_path.read_text(encoding="utf-8")
        source_mask, source_opcode = _source_mask_opcode(form)
        width = next((v for v in form.variants if v in ("sf=W", "sf=X")), None)
        if width is None:
            raise ValueError(f"--hide requires a width row with sf=W or sf=X: {form_id}")
        sf_opcode = "80000000" if width == "sf=X" else "00000000"
        branch = f"else if w && 0x{source_mask:x}w = 0x{source_opcode:x}w then"
        guard = f"\n        if word_bit 31 w = {'T' if width == 'sf=X' else 'F'} then NONE else"
        if branch not in isa_text:
            raise AssertionError(f"could not find classifier branch for {form_id}")
        isa_path.write_text(isa_text.replace(branch, branch + guard, 1), encoding="utf-8")
        return coverage(patched)


_HOL_ACCEPTANCE_CACHE: dict[tuple[str, str], tuple[bool, str]] = {}


def _hol_acceptance_probe(root: Path, form_id: str) -> tuple[bool, str]:
    """Rebuild the fixture-free HOL probe after mutating one real classifier clause."""
    cache_key = (str(root.resolve()), form_id)
    if cache_key in _HOL_ACCEPTANCE_CACHE:
        return _HOL_ACCEPTANCE_CACHE[cache_key]
    form = next(item for item in INVENTORY if item.form_id == form_id)
    source_mask, source_opcode = _source_mask_opcode(form)
    width = next(v for v in form.variants if v in ("sf=W", "sf=X"))
    branch = f"else if w && 0x{source_mask:x}w = 0x{source_opcode:x}w then"
    guard = f"\n        if word_bit 31 w = {'T' if width == 'sf=X' else 'F'} then NONE else"
    with tempfile.TemporaryDirectory(prefix="a64-hol-acceptance-") as directory:
        patched = Path(directory) / "repo"
        shutil.copytree(
            root,
            patched,
            ignore=shutil.ignore_patterns(".git", ".holbuild", "__pycache__", "*.pyc", "examples"),
        )
        isa_path = patched / "isa/arm64IsaScript.sml"
        isa_text = isa_path.read_text(encoding="utf-8")
        if branch not in isa_text:
            result = (False, f"ADD acceptance: classifier branch not found for {form_id}")
            _HOL_ACCEPTANCE_CACHE[cache_key] = result
            return result
        isa_path.write_text(isa_text.replace(branch, branch + guard, 1), encoding="utf-8")
        result = subprocess.run(
            ["holbuild", "-j4", "build", "arm64CoverageTheory"],
            cwd=patched,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=180,
            check=False,
        )
    output = result.stdout
    expected = {
        "dp-imm.addsub-immediate.w": "addImm_w_coverage_probes_1_decode_encode",
        "dp-imm.addsub-immediate.x": "addImm_x_coverage_probes_1_decode_encode",
        "dp-reg.addsub-shifted.w": "addShift_w_coverage_probes_1_decode_encode",
        "dp-reg.addsub-shifted.x": "addShift_x_coverage_probes_1_decode_encode",
        "dp-reg.addsub-extended.w": "addExtend_w_coverage_probes_1_decode_encode",
        "dp-reg.addsub-extended.x": "addExtend_x_coverage_probes_1_decode_encode",
        "dp-reg.addsub-carry.w": "addCarry_w_coverage_probes_1_decode_encode",
        "dp-reg.addsub-carry.x": "addCarry_x_coverage_probes_1_decode_encode",
    }[form_id]
    if result.returncode == 0:
        result_tuple = (False, "ADD acceptance: mutated HOL classifier still proves the ADD probe theorem")
    else:
        failed_theorems = set(re.findall(
            r"\b(add(?:Imm|Shift|Extend|Carry)_[wx]_coverage_probes(?:_\d+)?_decode_encode)\b",
            output,
        ))
        if failed_theorems != {expected}:
            result_tuple = (False, "ADD acceptance: HOL mutation failed outside the targeted ADD probe theorem")
        else:
            result_tuple = (True, f"ADD acceptance: HOL probe failed exactly at {expected}")
    _HOL_ACCEPTANCE_CACHE[cache_key] = result_tuple
    return result_tuple

def _add_rows(report: dict[str, object]) -> list[dict[str, object]]:
    return [row for row in report["rows"] if row["constructor"] in ADD_CONSTRUCTORS]


def acceptance(root: Path) -> tuple[bool, str]:
    baseline = coverage(root)
    baseline_total = baseline["summary"]["architectural_total"]
    add_rows = _add_rows(baseline)
    expected = {
        "dp-imm.addsub-immediate.w", "dp-imm.addsub-immediate.x",
        "dp-reg.addsub-shifted.w", "dp-reg.addsub-shifted.x",
        "dp-reg.addsub-extended.w", "dp-reg.addsub-extended.x",
        "dp-reg.addsub-carry.w", "dp-reg.addsub-carry.x",
    }
    actual = {row["form_id"] for row in add_rows}
    if actual != expected:
        return False, "ADD acceptance: fixed inventory does not contain every ADD family width row"
    if any(row["status"] != "implemented" for row in add_rows):
        return False, "ADD acceptance: an ADD family width row is already missing"
    hol_check = subprocess.run(
        ["holbuild", "check", "arm64CoverageTheory"],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=180,
        check=False,
    )
    if hol_check.returncode != 0:
        return False, "ADD acceptance: baseline arm64CoverageTheory check failed"
    hidden = "dp-imm.addsub-immediate.w"
    hol_ok, hol_message = _hol_acceptance_probe(root, hidden)
    if not hol_ok:
        return False, hol_message
    regression = _coverage_with_marker(root, hidden)
    baseline_missing = {
        row["form_id"] for row in baseline["rows"] if row["status"] != "implemented"
    }
    missing = {row["form_id"] for row in regression["rows"] if row["status"] != "implemented"}
    if regression["summary"]["architectural_total"] != baseline_total:
        return False, "ADD acceptance: hiding support changed the architectural denominator"
    if missing - baseline_missing != {hidden}:
        return False, f"ADD acceptance: hidden row {hidden} was not the exact new missing row"
    explicit_missing = [row for row in baseline["rows"] if row["architectural_status"] == "valid_but_unimplemented"]
    if not explicit_missing or not all(row["status"] != "implemented" and not row["evidence"]["decode"]
                                       for row in explicit_missing):
        return False, "ADD acceptance: valid unimplemented forms are not explicit in the missing list"
    return True, (
        f"ADD acceptance: PASS (rows={len(add_rows)}, implemented={len(add_rows)}, "
        f"hidden={hidden}, denominator={baseline_total}, explicit_missing={len(explicit_missing)}; {hol_message})"
    )


def validate(root: Path, report: dict[str, object]) -> list[str]:
    errors: list[str] = []
    isa = _source(root, "isa/arm64IsaScript.sml")
    if not isa:
        errors.append("missing isa/arm64IsaScript.sml")
    if "encode_of_decode" not in isa:
        errors.append("arm64Isa.encode_of_decode is not present")
    if len(INVENTORY) != ARCHITECTURAL_TOTAL:
        errors.append("inventory length changed without updating the versioned architectural total")
    if report["summary"]["architectural_total"] != ARCHITECTURAL_TOTAL:
        errors.append("architectural total is not the pinned versioned total")
    for row in report["rows"]:
        if row["architectural_status"] in ("implemented", "partially_implemented") and not row["constructor_declared"]:
            errors.append(f"implemented row has no HOL constructor: {row['form_id']}")
        if row["architectural_status"] == "valid_but_unimplemented" and row["constructor"] is None:
            errors.append(f"unimplemented row has no source name: {row['form_id']}")
        if row["architectural_status"] == "implemented" and row["status"] != "implemented":
            errors.append(f"implemented row lost coverage: {row['form_id']} ({row['status']})")
        if row["architectural_status"] == "partially_implemented" and row["status"] == "unimplemented":
            errors.append(f"partially implemented row lost all coverage: {row['form_id']}")
        evidence = row["evidence"]
        for key in ("decode", "encode_round_trip", "decode_probes", "hol_decode_probe", "hol_decode_negative_probe", "execution", "execution_clause", "hol_execution_probe", "execution_evidence_level", "state_update_modeled", "execution_faults", "faults_modeled", "fault_test_evidence", "step_faults", "native", "l3_arm8", "l3_discrepancy", "l3_discrepancy_sources", "universal", "universal_sources", "universal_contract_sources", "definition_sources", "verified_c_contract", "hidden_for_acceptance"):
            if key not in evidence:
                errors.append(f"missing evidence field {key}: {row['form_id']}")
        if row["architectural_status"] == "valid_but_unimplemented" and not evidence["hol_decode_negative_probe"]:
            errors.append(f"unimplemented row has no HOL NONE probe: {row['form_id']}")
    return errors


def print_report(report: dict[str, object]) -> None:
    summary = report["summary"]
    print(f"inventory={report['inventory_version']} source={report['inventory_source']}")
    print(
        "architectural_total={architectural_total} implemented={implemented} "
        "partially_implemented={partially_implemented} unimplemented={unimplemented}".format(**summary)
    )
    print("validation_evidence=native,l3_arm8,universal (reported independently)")
    for row in report["rows"]:
        e = row["evidence"]
        print(
            f"{row['form_id']:<34} {row['status']:<22} "
            f"decode={'yes' if e['decode'] else 'no':<3} "
            f"encode={'yes' if e['encode_round_trip'] else 'no':<3} "
            f"execute={'yes' if e['execution'] else 'no':<3} "
            f"exec_evidence={e['execution_evidence_level']:<10} "
            f"state={'yes' if e['state_update_modeled'] else 'no':<3} "
            f"native={'yes' if e['native'] else 'no':<3} "
            f"l3={'yes' if e['l3_arm8'] else 'no':<3} "
            f"l3_discrepancy={'yes' if e['l3_discrepancy'] else 'no':<3} "
            f"universal={'yes' if e['universal'] else 'no':<3} "
            f"faults={'yes' if e['faults_modeled'] else 'no':<3} "
            f"fault_classes={','.join(e['execution_faults']) or 'none'} "
            f"mask={row['mask']} opcode={row['opcode']}"
        )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--check", action="store_true", help="validate source/inventory consistency")
    parser.add_argument("--accept-add", action="store_true", help="run the fixture-free ADD-family acceptance test")
    parser.add_argument("--hide", action="append", default=[], help="hide one width-specific form id for a report")
    parser.add_argument("--json", action="store_true", help="emit the complete machine-readable report")
    args = parser.parse_args(argv)
    if len(args.hide) > 1:
        parser.error("--hide accepts one form id per run")
    try:
        report = _coverage_with_marker(args.root, args.hide[0]) if args.hide else coverage(args.root)
    except ValueError as error:
        parser.error(str(error))
    errors = validate(args.root, report) if args.check else []
    if args.accept_add:
        ok, message = acceptance(args.root)
        print(message, file=sys.stderr if args.json else sys.stdout)
        if not ok:
            errors.append(message)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print_report(report)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

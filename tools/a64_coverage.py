#!/usr/bin/env python3
"""Measure arm64-hol's A64 decoder against Arm's Armv9.4-A Sail decoder.

The inventory is every A64 encoding clause (`__DecodeA64_*`) in
`arm-v9.4-a/src/instrs64{,_sve,_sme}.sail` of rems-project/sail-arm. Each clause is
sampled: its fixed bits are kept and its operand bits filled with seeded
random values. A small interpreter for the subset of Sail that the
`decode_*` functions use classifies each sample as Sail decodes it:

  valid       the decoder reaches an `execute_*` call (or ends as a NOP)
              and the checks at the start of that function pass at EL0
  undefined   the decoder, or those checks, throw `Error_Undefined`
  unpredictable  they reach `ConstrainUnpredictable`
  unknown     the result depends on a value the interpreter does not model,
              such as the per-register EL0 access rules of system registers

The checks at the start of an `execute_*` function run up to the first
statement the interpreter cannot evaluate, with `PSTATE.EL` = EL0. A call
there to a helper elsewhere in the model (`v8_base.sail`) that can throw
`Error_Undefined` makes the sample unknown, except checks that depend on
how higher exception levels configure EL0 (FP, AdvSIMD, SVE, MOPS and
pointer-authentication enables), which count as passing like the features.
Every optional feature (`Have*()`) counts as implemented; each clause
lists the feature predicates its decoder consults. The same words are
decoded by `decode armv9_4` in HOL4 (`cv_eval`, through `holbuild run`).
A clause is covered when HOL4 decodes all its valid samples, and
unsampled when no sample is valid. Any sample HOL4 decodes but Sail
rejects is listed as a mismatch.

Usage: a64_coverage.py [--sail DIR] [--samples N] [--json FILE] [--accept-add]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

SAIL_COMMIT = "329d5009fe33afcf6fa2cda0e52c1c1ed3d8a1d8"
SAIL_URL = ("https://raw.githubusercontent.com/rems-project/sail-arm/"
            f"{SAIL_COMMIT}/arm-v9.4-a/src/")
SAIL_FILES = ("instrs64.sail", "instrs64_sve.sail", "instrs64_sme.sail", "v8_base.sail")

# Helpers whose UNDEFINED outcome depends on how higher exception levels
# configure EL0 (CPACR_EL1, SCTLR_EL1, SCR_EL3 and the like) rather than on
# the exception level itself; they count as passing, like the features.
ASSUMED_ENABLED = {"CheckFPEnabled64", "CheckFPAdvSIMDEnabled64", "AArch64_CheckFPEnabled",
                   "AArch64_CheckFPAdvSIMDEnabled", "CheckSVEEnabled",
                   "CheckNonStreamingSVEEnabled", "CheckOriginalSVEEnabled",
                   "CheckMOPSEnabled", "AddPACDA", "AddPACDB", "AddPACGA", "AddPACIA",
                   "AddPACIB", "AuthDA", "AuthDB", "AuthIA", "AuthIB"}

# Instruction classes (the `aarch64_instrs_<class>` suffix of each decode
# function) grouped into the profile areas the report is split by. The
# first matching prefix wins; anything else is reported as "other".
AREAS = [
    ("privileged", (
        "branch_unconditional_eret", "system_exceptions_debug_exception",
        "system_exceptions_runtime_hvc", "system_exceptions_runtime_smc",
        "system_exceptions_debug_halt", "system_register_system_128",
        "system_sysops_128", "system_sysinstwithreg")),
    ("extensions", (
        "integer_tags", "integer_pac", "memory_single_general_immediate_signed_pac",
        "memory_mcpymset", "system_tme", "memory_atomicops_ld_acc",
        "memory_atomicops_st_acc", "memory_rcw", "memory_gcs",
        "memory_atomicops_ld_128", "memory_atomicops_swp_128",
        "memory_ordered_pair", "integer_arithmetic_max_min",
        "integer_arithmetic_unary_abs", "integer_arithmetic_unary_cnt",
        "integer_arithmetic_unary_ctz", "integer_arithmetic_pointer",
        "integer_flags", "memory_single_general_range")),
    ("atomics and ordered", (
        "memory_atomicops", "memory_exclusive", "memory_ordered",
        "memory_single_general_immediate_signed_offset_lda_stl",
        "memory_single_simdfp_immediate_signed_offset_ordered",
        "memory_vector_single_no_wb_ordered")),
    ("system", ("system_", "branch_conditional_hinted")),
    ("integer", ("integer_", "branch_")),
    ("load/store", ("memory_single_general", "memory_pair_general",
                    "memory_literal_general")),
    ("SIMD&FP load/store", ("memory_single_simdfp", "memory_pair_simdfp",
                            "memory_literal_simdfp", "memory_vector")),
    ("floating point", ("float_",)),
    ("AdvSIMD", ("vector_",)),
    ("reserved", ("udf_",)),
]


def area_of(instr_class: str) -> str:
    for area, prefixes in AREAS:
        if instr_class.startswith(prefixes):
            return area
    return "other"


# ---------------------------------------------------------------------------
# Sail subset: tokens, parser and interpreter.

TOKEN = re.compile(r"""
    (?P<ws>\s+|/\*.*?\*/|//[^\n]*)
  | (?P<num>0b[01_]+|0x[0-9A-Fa-f_]+|\d+)
  | (?P<str>"[^"]*")
  | (?P<id>'?[A-Za-z_][A-Za-z0-9_]*)
  | (?P<op>\.\.|==|!=|<=|>=|<<|>>|=>|[-+*@&|<>=(){}\[\],;:.!])
  | (?P<other>.)
""", re.X | re.S)


def tokenize(text: str) -> list[str]:
    tokens, pos = [], 0
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m:
            raise SyntaxError(f"bad character {text[pos]!r}")
        pos = m.end()
        if m.lastgroup != "ws":
            tokens.append(m.group())
    return tokens


class Valid(Exception):
    pass


class Undefined(Exception):
    pass


class See(Exception):
    pass


class Unpredictable(Exception):
    pass


class Unknown(Exception):
    pass


class Unmodelled(Exception):
    """EL0 legality depends on state the interpreter does not model."""


# Their EL0 access rules live in the per-register accessors.
UNMODELLED = {"AArch64_SysRegRead", "AArch64_SysRegWrite", "AArch64_SysRegRead128",
              "AArch64_SysRegWrite128", "AArch64_SysInstr", "AArch64_SysInstr128",
              "AArch64_SysInstrWithResult"}


@dataclass(frozen=True)
class Bits:
    value: int
    width: int

    def __post_init__(self):
        object.__setattr__(self, "value", self.value & ((1 << self.width) - 1))


class Opaque:
    """A value the interpreter does not model."""


OPAQUE = Opaque()


def bits_literal(text: str) -> Bits:
    digits = text[2:].replace("_", "")
    if text.startswith("0b"):
        return Bits(int(digits, 2), len(digits))
    return Bits(int(digits, 16), 4 * len(digits))


class Parser:
    def __init__(self, tokens: list[str]):
        self.toks, self.i = tokens, 0

    def peek(self, k: int = 0) -> str:
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else ""

    def next(self) -> str:
        tok = self.peek()
        self.i += 1
        return tok

    def expect(self, tok: str) -> None:
        if self.next() != tok:
            raise SyntaxError(f"expected {tok!r} near {self.toks[self.i-5:self.i+5]}")

    def skip_type(self, stops: set[str]) -> None:
        depth = 0
        while True:
            tok = self.peek()
            if not tok:
                raise SyntaxError("unterminated type")
            if depth == 0 and tok in stops:
                return
            if tok in "({[":
                depth += 1
            elif tok in ")}]":
                depth -= 1
            self.next()

    # Statements -----------------------------------------------------------
    def prefix(self) -> tuple:
        """The statements of a function body up to the first it cannot parse."""
        self.expect("{")
        stmts = []
        try:
            while self.peek() != "}":
                stmts.append(self.statement())
                if self.peek() == ";":
                    self.next()
        except (SyntaxError, IndexError):
            stmts.append(("expr", ("call", "unmodelled", [])))
        return ("block", stmts)

    def block(self) -> tuple:
        self.expect("{")
        stmts = []
        while self.peek() != "}":
            stmts.append(self.statement())
            if self.peek() == ";":
                self.next()
        self.expect("}")
        return ("block", stmts)

    def pattern(self):
        if self.peek() == "(":
            self.next()
            names = []
            while True:
                names.append(self.next())
                if self.peek() == ":":
                    self.next()
                    self.skip_type({",", ")"})
                if self.next() == ")":
                    return ("tuple", names)
        name = self.next()
        if self.peek() == ":":
            self.next()
            self.skip_type({"="})
        return name

    def statement(self) -> tuple:
        tok = self.peek()
        if tok == "let":
            self.next()
            pat = self.pattern()
            self.expect("=")
            value = self.expr()
            if self.peek() == "in":
                self.next()
                body = self.block() if self.peek() == "{" else self.expr()
                return ("letin", pat, value, body)
            return ("let", pat, value)
        if re.match(r"[A-Za-z_]", tok) and self.peek(1) == ":":
            name = self.next()
            self.next()
            self.skip_type({"="})
            self.expect("=")
            return ("let", name, self.expr())
        if re.match(r"[A-Za-z_]", tok) and self.peek(1) == "=":
            name = self.next()
            self.next()
            return ("let", name, self.expr())
        if tok in ("foreach", "var", "while", "repeat"):
            raise SyntaxError(tok)
        return ("expr", self.expr())

    # Expressions ----------------------------------------------------------
    BINARY = [("|",), ("&",), ("==", "!=", "<", ">", "<=", ">="), ("@",),
              ("+", "-"), ("*",), ("<<", ">>")]

    def expr(self):
        if self.peek() == "if":
            self.next()
            cond = self.expr()
            self.expect("then")
            then = self.block() if self.peek() == "{" else self.expr()
            other = ("unit",)
            if self.peek() == "else":
                self.next()
                other = self.block() if self.peek() == "{" else self.expr()
            return ("if", cond, then, other)
        if self.peek() == "match":
            self.next()
            subject = self.expr()
            self.expect("{")
            arms = []
            while self.peek() != "}":
                pat = self.next()
                if pat == "[":
                    items = []
                    while self.peek() != "]":
                        items.append(self.next())
                        if self.peek() == ",":
                            self.next()
                    self.next()
                    pat = tuple(items)
                self.expect("=>")
                body = self.block() if self.peek() == "{" else self.expr()
                arms.append((pat, body))
                if self.peek() == ",":
                    self.next()
            self.expect("}")
            return ("match", subject, arms)
        return self.binary(0)

    def binary(self, level: int):
        if level == len(self.BINARY):
            return self.postfix()
        left = self.binary(level + 1)
        while self.peek() in self.BINARY[level]:
            op = self.next()
            left = ("bin", op, left, self.binary(level + 1))
        return left

    def postfix(self):
        node = self.primary()
        while True:
            if self.peek() == "[":
                self.next()
                hi = self.expr()
                if self.peek() == "..":
                    self.next()
                    lo = self.expr()
                    self.expect("]")
                    node = ("slice", node, hi, lo)
                else:
                    self.expect("]")
                    node = ("index", node, hi)
            elif self.peek() == ".":
                self.next()
                node = ("field", node, self.next())
            elif self.peek() == ":" and self.peek(1) == "bool":
                self.i += 2
            else:
                return node

    def primary(self):
        tok = self.next()
        if tok == "(":
            if self.peek() == ")":
                self.next()
                return ("unit",)
            items = [self.expr()]
            if self.peek() == ":":
                self.next()
                self.skip_type({")"})
            while self.peek() == ",":
                self.next()
                items.append(self.expr())
            self.expect(")")
            return items[0] if len(items) == 1 else ("tuple", items)
        if tok == "[":
            inner = self.expr()
            self.expect("]")
            return ("vec1", inner)
        if tok == "{":
            self.i -= 1
            return self.block()
        if tok.startswith(("0b", "0x")):
            return ("const", bits_literal(tok))
        if tok.isdigit():
            return ("const", int(tok))
        if tok in ("true", "false"):
            return ("const", tok == "true")
        if tok.startswith('"'):
            return ("const", tok[1:-1])
        if tok == "-":
            return ("bin", "-", ("const", 0), self.postfix())
        if self.peek() == "(" and tok in ("assert", "constraint"):
            depth = 0
            while True:
                t = self.next()
                depth += t == "("
                depth -= t == ")"
                if depth == 0:
                    return ("unit",)
        if self.peek() == "(":
            self.next()
            args = []
            while self.peek() != ")":
                args.append(self.expr())
                if self.peek() == ",":
                    self.next()
            self.next()
            return ("call", tok, args)
        return ("var", tok.lstrip("'"))


def ones(n: int) -> int:
    return (1 << n) - 1


def highest_set_bit(b: Bits) -> int:
    return b.value.bit_length() - 1


def decode_bit_masks(immn: Bits, imms: Bits, immr: Bits, immediate: bool, m: int):
    length = highest_set_bit(Bits((immn.value << 6) | (~imms.value & 63), 7))
    if length < 1:
        raise Undefined
    levels = ones(length)
    if immediate and imms.value & levels == levels:
        raise Undefined
    s, r = imms.value & levels, immr.value & levels
    esize = 1 << length
    d = (s - r) & levels
    welem, telem = ones(s + 1), ones(d + 1)
    welem = ((welem >> r) | (welem << (esize - r))) & ones(esize)
    wmask = tmask = 0
    for i in range(m // esize):
        wmask |= welem << (i * esize)
        tmask |= telem << (i * esize)
    return (Bits(wmask, m), Bits(tmask, m))


def as_int(v) -> int:
    if isinstance(v, Opaque):
        raise Unknown
    return v.value if isinstance(v, Bits) else int(v)


def builtin(name: str, args: list):
    if name.startswith(("Have", "IsFeatureImplemented")):
        return True
    if name == "throw":
        kind = args[0]
        if kind == "See":
            raise See
        if kind == "Unpredictable":
            raise Unpredictable
        if kind == "Undefined":
            raise Undefined
        raise Unknown
    if name == "Error_Undefined":
        return "Undefined"
    if name == "Error_See":
        return "See"
    if name == "Error_ConstrainedUnpredictable":
        return "Unpredictable"
    if name == "ConstrainUnpredictable":
        raise Unpredictable
    if name.startswith("execute_") or name in ("EndOfInstruction", "return"):
        raise Valid
    if name == "unmodelled":
        raise Unknown
    if name in UNMODELLED:
        raise Unmodelled
    if name in ("assert", "SetBTypeCompatible", "CheckMOPSEnabled",
                "AArch64_CheckSystemAccess"):
        return None
    if any(isinstance(a, Opaque) for a in args):
        return OPAQUE
    if name == "UInt":
        return args[0].value
    if name == "SInt":
        b = args[0]
        return b.value - (1 << b.width) if b.value >> (b.width - 1) else b.value
    if name == "not_bool":
        return not args[0]
    if name == "not_vec":
        return Bits(~args[0].value, args[0].width)
    if name == "DIV":
        return as_int(args[0]) // as_int(args[1])
    if name == "Slice":
        return Bits(args[0].value >> args[1], args[2])
    if name == "ZeroExtend":
        return Bits(args[0].value, args[1])
    if name == "SignExtend":
        b, n = args
        v = b.value - (1 << b.width) if b.value >> (b.width - 1) else b.value
        return Bits(v, n)
    if name == "LSL":
        return Bits(args[0].value << args[1], args[0].width)
    if name == "Zeros":
        return Bits(0, args[0])
    if name == "Ones":
        return Bits(ones(args[0]), args[0])
    if name == "HighestSetBit":
        return highest_set_bit(args[0])
    if name == "LowestSetBit":
        v = args[0].value
        return (v & -v).bit_length() - 1 if v else args[0].width
    if name == "DecodeBitMasks":
        return decode_bit_masks(*args)
    if name in ("Halted",):
        return False
    if name in ("CurrentVL_read", "CurrentSVL_read"):
        return 128  # the smallest SVE and SME vector lengths
    return OPAQUE


VALUE_BUILTINS = {"UInt", "SInt", "DIV", "Slice", "ZeroExtend", "SignExtend", "LSL",
                  "Zeros", "Ones", "HighestSetBit", "LowestSetBit", "DecodeBitMasks"}


class Interp:
    def __init__(self, functions: dict[str, tuple[list[str], tuple]], undefined: set[str]):
        self.functions = functions
        self.undefined = undefined

    def run(self, node, env: dict):
        kind = node[0]
        if kind == "block":
            result = None
            for stmt in node[1]:
                result = self.run(stmt, env)
            return result
        if kind == "let":
            value = self.run(node[2], env)
            pat = node[1]
            if isinstance(pat, tuple):
                for name, v in zip(pat[1], value if isinstance(value, tuple) else [OPAQUE] * 9):
                    env[name.lstrip("'")] = v
            else:
                env[pat.lstrip("'")] = value
            return None
        if kind == "letin":
            self.run(("let", node[1], node[2]), env)
            return self.run(node[3], env)
        if kind == "expr":
            return self.run(node[1], env)
        if kind == "unit":
            return None
        if kind == "const":
            return node[1]
        if kind == "var":
            name = node[1]
            if name in env:
                return env[name]
            return name  # an enumeration constant
        if kind == "tuple":
            return tuple(self.run(x, env) for x in node[1])
        if kind == "vec1":
            v = self.run(node[1], env)
            return v if isinstance(v, (Bits, Opaque)) else Bits(int(v), 1)
        if kind == "index":
            b, i = self.run(node[1], env), self.run(node[2], env)
            if isinstance(b, Opaque) or isinstance(i, Opaque):
                return OPAQUE
            return Bits(b.value >> as_int(i), 1)
        if kind == "slice":
            b = self.run(node[1], env)
            hi, lo = self.run(node[2], env), self.run(node[3], env)
            if isinstance(b, Opaque):
                return OPAQUE
            return Bits(b.value >> as_int(lo), as_int(hi) - as_int(lo) + 1)
        if kind == "field":
            base = node[1]
            if base == ("var", "PSTATE") and node[2] == "EL":
                return "EL0"
            return OPAQUE
        if kind == "if":
            cond = self.run(node[1], env)
            if isinstance(cond, Opaque):
                raise Unknown
            return self.run(node[2] if cond else node[3], env)
        if kind == "match":
            subject = self.run(node[1], env)
            if isinstance(subject, Opaque):
                raise Unknown
            for pat, body in node[2]:
                if pat == "_" or self.matches(pat, subject):
                    return self.run(body, env)
            raise Unknown
        if kind == "bin":
            return self.binary(node[1], self.run(node[2], env), self.run(node[3], env))
        if kind == "call":
            name = node[1]
            args = [self.run(a, env) for a in node[2]]
            if name in self.functions:
                params, body = self.functions[name]
                if not name.startswith("execute_"):
                    return self.run(body, dict(zip(params, args)))
                try:
                    self.run(body, dict(zip(params, args)))
                except (Unknown, KeyError, TypeError, AttributeError, ValueError,
                        IndexError, AssertionError):
                    pass
                raise Valid
            if any(isinstance(a, str) for a in args) and name in VALUE_BUILTINS:
                return OPAQUE
            if name in self.undefined and name not in VALUE_BUILTINS:
                raise Unmodelled
            return builtin(name, args)
        raise Unknown(kind)

    @staticmethod
    def matches(pat, subject) -> bool:
        if isinstance(pat, tuple):
            if isinstance(subject, Opaque):
                raise Unknown
            width = len(pat)
            return all(b == "_" or ((subject.value >> (width - 1 - i)) & 1) == (b == "bitone")
                       for i, b in enumerate(pat))
        if pat.startswith(("0b", "0x")):
            return bits_literal(pat).value == as_int(subject)
        if pat.isdigit():
            return int(pat) == as_int(subject)
        return pat == subject

    @staticmethod
    def binary(op: str, a, b):
        if op not in ("==", "!=") and (isinstance(a, str) or isinstance(b, str)):
            return OPAQUE
        if isinstance(a, Opaque) or isinstance(b, Opaque):
            if op == "&" and (a is False or b is False):
                return False
            if op == "|" and (a is True or b is True):
                return True
            return OPAQUE
        if op == "@":
            return Bits((a.value << b.width) | b.value, a.width + b.width)
        if op in ("&", "|") and isinstance(a, bool):
            return (a and b) if op == "&" else (a or b)
        if op in ("&", "|"):
            w = a.width
            return Bits(a.value & b.value if op == "&" else a.value | b.value, w)
        if op in ("==", "!="):
            if isinstance(a, Bits) or isinstance(b, Bits):
                eq = as_int(a) == as_int(b)
            else:
                eq = a == b
            return eq if op == "==" else not eq
        if op in ("<", ">", "<=", ">="):
            x, y = as_int(a), as_int(b)
            return {"<": x < y, ">": x > y, "<=": x <= y, ">=": x >= y}[op]
        if isinstance(a, Bits):
            v = {"+": a.value + as_int(b), "-": a.value - as_int(b),
                 "*": a.value * as_int(b), "<<": a.value << as_int(b),
                 ">>": a.value >> as_int(b)}[op]
            return Bits(v, a.width)
        x, y = as_int(a), as_int(b)
        return {"+": x + y, "-": x - y, "*": x * y, "<<": x << y, ">>": x >> y}[op]


# ---------------------------------------------------------------------------
# The inventory.

@dataclass
class Clause:
    index: int
    group: str
    see: int
    mask: int
    value: int
    exclude: tuple[int, int] | None
    decoder: str
    mnemonic: str
    instr_class: str
    area: str
    features: list[str]
    body: tuple = field(repr=False)


CLAUSE = re.compile(
    r"function clause __DecodeA64_(\w+) \(\(pc, \((.*?) as __opcode\)\) "
    r"if (.*?)SEE < (\d+)\) = (\{.*?\n\})", re.S)
EXCLUDE = re.compile(r"not_bool\(\(match Slice\(__opcode, (\d+), (\d+)\) \{\s*"
                     r"\[([^\]]*)\] => true,\s*_ => false\s*\}\) : bool\) & $", re.S)
FUNCTION = re.compile(r"\nfunction ((?:decode|execute)_\w+) \(?([^)=]*?)\)? = (\{.*?\n\})", re.S)
FEATURE = re.compile(r"\b(Have\w+|IsFeatureImplemented\(\w+\))")


def bit_pattern(bits: list[str], top: int) -> tuple[int, int]:
    mask = value = 0
    for pos, bit in zip(range(top, -1, -1), bits):
        if bit != "_":
            mask |= 1 << pos
            value |= (bit == "bitone") << pos
    return mask, value


def load_inventory(source: str):
    functions, texts = {}, {}
    for name, params, body in FUNCTION.findall(source):
        texts[name] = body
        params = [p.strip() for p in params.split(",")]
        try:
            parser = Parser(tokenize(body))
            functions[name] = (params, parser.prefix() if name.startswith("execute_")
                               else parser.block())
        except SyntaxError:
            functions[name] = ([], ("block", [("expr", ("call", "unmodelled", []))]))
    clauses = []
    for index, (group, pattern, guard, see, body) in enumerate(CLAUSE.findall(source)):
        if pattern.startswith("0b"):
            mask, value = 0xFFFFFFFF, int(pattern[2:], 2)
        else:
            bits = [b.strip() for b in pattern.strip("[]").split(",")]
            assert len(bits) == 32, (group, see)
            mask, value = bit_pattern(bits, 31)
        exclude = None
        if guard:
            m = EXCLUDE.fullmatch(guard)
            assert m, guard
            lo, width = int(m.group(1)), int(m.group(2))
            emask, evalue = bit_pattern([b.strip() for b in m.group(3).split(",")], width - 1)
            exclude = (emask << lo, evalue << lo)
        decoder = re.findall(r"(decode_\w+)\(", body)[-1]
        mnemonic, _, instr_class = decoder[len("decode_"):].partition("_aarch64_instrs_")
        area = group if group in ("SVE", "SME") else area_of(instr_class)
        ast = Parser(tokenize(body)).block()
        features = sorted(set(FEATURE.findall(guard + body + texts.get(decoder, ""))))
        clauses.append(Clause(index, group, int(see), mask, value, exclude, decoder,
                              mnemonic, instr_class, area, features, ast))
    return clauses, functions


HELPER = re.compile(r"\nfunction (\w+)[^\n]*?= (\{.*?\n\})", re.S)
CALL = re.compile(r"\b([A-Za-z_]\w*)\(")


def undefined_helpers(source: str) -> set[str]:
    """Functions outside decode_*/execute_* that can throw Error_Undefined."""
    bodies = defaultdict(str)
    for name, body in HELPER.findall(source):
        if not name.startswith(("decode_", "execute_")):
            bodies[name] += body
    calls = {name: set(CALL.findall(body)) for name, body in bodies.items()}
    undefined = {name for name, body in bodies.items() if "Error_Undefined" in body}
    while True:
        more = {name for name, called in calls.items() if called & undefined} - undefined
        if not more:
            return undefined - ASSUMED_ENABLED
        undefined |= more


def top_group(word: int) -> str:
    op0 = (word >> 25) & 0xF
    if op0 == 0:
        return "SME" if word >> 31 else "Reserved"
    if op0 in (1, 3):
        return "Unallocated"
    if op0 == 2:
        return "SVE"
    if (op0 & 0b1110) == 0b1000:
        return "DataProcImm"
    if (op0 & 0b1110) == 0b1010:
        return "BranchExcSys"
    if (op0 & 0b0101) == 0b0100:
        return "LoadStore"
    if (op0 & 0b0111) == 0b0101:
        return "DataProcReg"
    return "DataProcFPSIMD"


def sail_decode(word: int, clauses: list[Clause], by_group, interp: Interp):
    """Return (status, clause) for a word, as Sail's decoder would."""
    see = 0
    for clause in by_group.get(top_group(word), ()):
        if clause.see <= see or word & clause.mask != clause.value:
            continue
        if clause.exclude and word & clause.exclude[0] == clause.exclude[1]:
            continue
        env = {"__opcode": Bits(word, 32), "SEE": see}
        try:
            interp.run(clause.body, env)
            return "unknown", clause
        except Valid:
            return "valid", clause
        except Undefined:
            return "undefined", clause
        except Unpredictable:
            return "unpredictable", clause
        except See:
            see = clause.see
        except (Unknown, Unmodelled, KeyError, TypeError, AttributeError, ValueError,
                IndexError, AssertionError):
            return "unknown", clause
    return "undefined", None


def samples(clause: Clause, count: int, rng: random.Random) -> list[int]:
    free = ~clause.mask & 0xFFFFFFFF
    words = {clause.value, clause.value | free}
    while len(words) < count + 2 and len(words) < (1 << bin(free).count("1")):
        words.add(clause.value | (rng.getrandbits(32) & free))
    return sorted(words)


# ---------------------------------------------------------------------------
# HOL4 side.

HOL_SCRIPT = r"""
load "wordsLib";
load "cv_transLib";
load "arm64IsaCvTheory";
open HolKernel boolLib bossLib wordsLib arm64IsaTheory arm64IsaCvTheory cv_transLib;
val _ = new_theory "a64_coverage";
Definition a64_decodes_def:
  a64_decodes [] = [] ∧
  a64_decodes ((w:word32)::ws) = IS_SOME (decode armv9_4 w) :: a64_decodes ws
End
val _ = cv_trans armv9_4_def;
val _ = cv_trans a64_decodes_def;
val words = map (fn s => wordsSyntax.mk_wordii (valOf (Int.fromString s), 32))
  (String.tokens Char.isSpace (TextIO.inputAll (TextIO.openIn "WORDS")));
val out = TextIO.openOut "RESULT";
fun chunks [] = ()
  | chunks ws =
      let val (now, later) = (List.take (ws, 256), List.drop (ws, 256))
            handle Subscript => (ws, [])
          val result = cv_eval ``a64_decodes ^(listSyntax.mk_list (now, ``:word32``))``
      in app (fn t => TextIO.output (out, if Teq t then "1\n" else "0\n"))
           (fst (listSyntax.dest_list (rhs (concl result))));
         chunks later
      end;
val _ = chunks words;
val _ = TextIO.closeOut out;
"""


def run_hol(repo: Path, script: str, inputs: dict[str, str]) -> list[str]:
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        for name, data in inputs.items():
            (tmp / name).write_text(data)
            script = script.replace(name.upper(), str(tmp / name))
        (tmp / "coverage.sml").write_text(script.replace("RESULT", str(tmp / "result")))
        run = subprocess.run(["holbuild", "run", str(tmp / "coverage.sml")], cwd=repo,
                             stdin=subprocess.DEVNULL, capture_output=True, text=True)
        if run.returncode != 0:
            raise SystemExit("holbuild run failed:\n" + (run.stdout + run.stderr)[-3000:])
        return (tmp / "result").read_text().splitlines()


def hol_decodes(words: list[int], repo: Path) -> list[bool]:
    result = run_hol(repo, HOL_SCRIPT, {"words": "\n".join(map(str, words)) + "\n"})
    if len(result) != len(words):
        raise SystemExit("HOL4 returned the wrong number of results")
    return [r == "1" for r in result]


EVIDENCE_SCRIPT = r"""
load "wordsLib";
load "cv_transLib";
load "arm64L3Theory";
open HolKernel boolLib bossLib arm64IsaCvTheory cv_transLib;
val out = TextIO.openOut "RESULT";
fun emit kind name word =
  TextIO.output (out, kind ^ " " ^ name ^ " " ^
    Arbnum.toString (wordsSyntax.dest_word_literal word) ^ "\n");

(* The final theorem argument is a constant from arm64NativeCases. *)
fun observed kind (name, thm) =
  let val {Name, Thy, ...} = dest_thy_const (rand (concl thm))
      val _ = if Thy = "arm64NativeCases" then () else raise Fail name
      val sample = rhs (concl (DB.fetch Thy (Name ^ "_def")))
  in emit kind name (fst (pairSyntax.dest_pair sample)) end;

fun native (name, thm) =
  if String.isPrefix "native_case_" name andalso String.isSuffix "_agrees" name then
    observed "native" (name, thm)
  else if is_eq (concl thm) then
    case (strip_comb (lhs (concl thm)), strip_comb (rhs (concl thm))) of
      ((step, [_, state]), (fault, [reason])) =>
        if same_const step ``step_cv`` andalso
           same_const fault ``Fault : fault_kind -> finite_state arm64_result`` andalso
           not (aconv reason ``Fetch`` orelse aconv reason ``PCAlignment``) then
          emit "fault" name (rhs (concl (EVAL ``cv_fetch ^state``)))
        else ()
    | _ => ()
  else ();

fun l3 (name, thm) =
  if String.isPrefix "l3_agrees_native_case_" name orelse
     String.isPrefix "l3_crc_agrees_native_case_" name then
    observed "l3" (name, thm)
  else if String.isPrefix "l3_clz_is_cls_native_case_" name then
    observed "l3_discrepancy" (name, thm)
  else ();

val _ = List.app native (DB.theorems "arm64Native");
val _ = List.app l3 (DB.theorems "arm64L3");
val _ = TextIO.closeOut out;
"""


def hol_evidence(repo: Path, clauses: list[Clause], by_group, interp: Interp):
    evidence = defaultdict(lambda: defaultdict(list))
    unassigned = []
    for line in run_hol(repo, EVIDENCE_SCRIPT, {}):
        kind, theorem, word = line.split()
        status, owner = sail_decode(int(word), clauses, by_group, interp)
        if status == "valid":
            evidence[owner.index][kind].append(theorem)
        else:
            unassigned.append({"kind": kind, "theorem": theorem,
                               "word": f"{int(word):08x}", "sail": status})
    return evidence, unassigned


ADD_OPTIONS = {
    "immediate": (0, 1 << 22),
    "extendedreg": tuple((option << 13) | (amount << 10)
                          for option in range(8) for amount in range(5)),
    "carry": (0,),
    "shiftedreg": (),
}


def add_probes(clauses: list[Clause], by_group, interp: Interp) -> dict[tuple[str, int], list[tuple[int, Clause]]]:
    """Use the Sail ADD/SUB clauses to exercise each width and option field."""
    probes = defaultdict(list)
    prefix = "integer_arithmetic_add_sub_"
    for clause in clauses:
        if not clause.instr_class.startswith(prefix):
            continue
        form = clause.instr_class.removeprefix(prefix)
        for sf in (0, 1):
            options = ADD_OPTIONS[form]
            if form == "shiftedreg":
                amounts = (0, 1, 31, 32, 63) if sf else (0, 1, 31)
                options = tuple((shift << 22) | (amount << 10)
                                for shift in range(3) for amount in amounts)
            # Include nonzero operands and Rd = 31 as well as all-zero registers.
            operands = (1 << 10) if form == "immediate" else (3 << 16)
            operands |= (2 << 5) | 31
            for fields in (*options, *(option | operands for option in options)):
                word = clause.value | (sf << 31) | fields
                status, owner = sail_decode(word, clauses, by_group, interp)
                if status != "valid" or owner != clause:
                    raise SystemExit(f"Sail rejected ADD probe {word:08x}: {status}")
                probes[form, sf].append((word, owner))
    for form in ADD_OPTIONS:
        for sf in (0, 1):
            # Bits 30 and 29 select add/subtract and whether to set NZCV.
            variants = {(word >> 29) & 3 for word, _ in probes[form, sf]}
            if variants != {0, 1, 2, 3}:
                raise SystemExit(f"Sail inventory is missing ADD variants for {form}, sf={sf}")
    return dict(probes)


def decode_state(valid: int, hit: int) -> str:
    return ("unsampled" if valid == 0 else "covered" if hit == valid
            else "partial" if hit else "missing")


def coverage_report(repo: Path, clauses: list[Clause], rows, probes):
    words = sorted({w for w, *_ in rows})
    decoded = dict(zip(words, hol_decodes(words, repo), strict=True))
    per_clause = defaultdict(Counter)
    mismatches = []
    for word, sampled, status, owner in rows:
        clause = owner or sampled
        hol = decoded[word]
        per_clause[clause.index][(status, hol)] += 1
        if hol and status in ("undefined", "unpredictable"):
            mismatches.append((word, clause, status))

    report = []
    for clause in clauses:
        counts = per_clause[clause.index]
        valid = counts[("valid", True)] + counts[("valid", False)]
        hit = counts[("valid", True)]
        report.append({"clause": clause.index, "group": clause.group,
                       "mnemonic": clause.mnemonic, "class": clause.instr_class,
                       "decoder": clause.decoder, "area": clause.area,
                       "mask": f"{clause.mask:08x}", "value": f"{clause.value:08x}",
                       "exclude": clause.exclude and [f"{x:08x}" for x in clause.exclude],
                       "features": clause.features, "state": decode_state(valid, hit),
                       "valid": valid, "decoded": hit,
                       "unknown": counts[("unknown", True)] + counts[("unknown", False)]})
    add_widths = []
    for (form, sf), cases in sorted(probes.items()):
        hit = sum(decoded[word] for word, _ in cases)
        add_widths.append({"form": form, "width": 64 if sf else 32,
                           "state": decode_state(len(cases), hit),
                           "valid": len(cases), "decoded": hit})
    return report, add_widths, mismatches


def check_add(repo: Path, clauses: list[Clause], rows, probes, report, add_widths) -> None:
    def by_width(width_rows):
        return {(row["form"], row["width"]): row["state"] for row in width_rows}

    baseline = by_width(add_widths)
    missing = [row for row, state in baseline.items() if state != "covered"]
    if missing:
        raise SystemExit(f"ADD coverage is missing these width rows: {missing}")

    target = ("immediate", 32)
    condition = "else if w && 0x1f800000w = 0x11000000w then"
    with tempfile.TemporaryDirectory(prefix="a64-add-") as directory:
        copy = Path(directory)
        for name in ("holproject.toml", "holexamples.manifest.toml", "arm64HolScript.sml"):
            shutil.copy2(repo / name, copy / name)
        shutil.copytree(repo / "isa", copy / "isa")
        (copy / "tests").mkdir()
        for script in (repo / "tests").glob("*Script.sml"):
            shutil.copy2(script, copy / "tests" / script.name)
        # holbuild needs every member directory; the others aren't built here.
        import tomllib  # Python 3.11+; only this check needs it
        manifest = tomllib.loads((repo / "holproject.toml").read_text())
        for member in manifest["build"]["members"]:
            (copy / member).mkdir(parents=True, exist_ok=True)
        isa = copy / "isa/arm64IsaScript.sml"
        source = isa.read_text()
        if source.count(condition) != 1:
            raise SystemExit("Could not find the ADD immediate classifier branch to mutate")
        isa.write_text(source.replace(condition, condition + "\n        if ¬sf then NONE else"))
        subprocess.run(["holbuild", "-j4", "build", "arm64IsaCvTheory"], cwd=copy, check=True)
        mutant_report, mutant_widths, _ = coverage_report(copy, clauses, rows, probes)
    clause_ids = [row["clause"] for row in report]
    if len(clause_ids) != len(clauses) or [row["clause"] for row in mutant_report] != clause_ids:
        raise SystemExit("The ADD mutation changed the Sail coverage denominator")
    immediate_clauses = {clause.index for _, clause in probes["immediate", 0]}
    for original, mutant in zip(report, mutant_report, strict=True):
        if original["clause"] in immediate_clauses:
            if original["state"] != "covered" or mutant["state"] != "partial":
                raise SystemExit(f"Expected the {original['mnemonic']} clause to become partial")
        elif original["decoded"] != mutant["decoded"] or original["state"] != mutant["state"]:
            raise SystemExit(f"Unexpected coverage change for {original['mnemonic']}")
    expected = baseline | {target: "missing"}
    if by_width(mutant_widths) != expected:
        raise SystemExit(f"Expected only the W immediate ADD row missing, got {mutant_widths}")
    print(f"ADD acceptance passed: {len(add_widths)} width rows, only W immediate lost, "
          f"Sail denominator {len(clause_ids)} clauses")


# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--sail", type=Path,
                        help="arm-v9.4-a/src directory (default: fetch the pinned files)")
    parser.add_argument("--samples", type=int, default=64, help="random words per clause")
    parser.add_argument("--json", type=Path, help="write the per-clause report here")
    parser.add_argument("--accept-add", action="store_true",
                        help="verify the fixture-free ADD width regression")
    args = parser.parse_args()

    texts = []
    for name in SAIL_FILES:
        if args.sail:
            texts.append((args.sail / name).read_text())
        else:
            with urllib.request.urlopen(SAIL_URL + name) as response:
                texts.append(response.read().decode())
    source = "\n".join(texts)
    digest = hashlib.sha256(source.encode()).hexdigest()
    clauses, functions = load_inventory(source)
    by_group = defaultdict(list)
    for clause in clauses:
        by_group[clause.group].append(clause)
    interp = Interp(functions, undefined_helpers(source))

    rng = random.Random(0)
    rows = []
    for clause in clauses:
        for word in samples(clause, args.samples, rng):
            status, owner = sail_decode(word, clauses, by_group, interp)
            rows.append((word, clause, status, owner))
    # CAS W0, W1, [X2] is valid at EL0. The model omits atomic accesses.
    cas_word = 0x88A07C41
    status, cas_clause = sail_decode(cas_word, clauses, by_group, interp)
    if status != "valid" or cas_clause.mnemonic != "cas":
        raise SystemExit(f"Expected Sail to decode {cas_word:08x} as valid CAS, got {status}")
    probes = add_probes(clauses, by_group, interp)
    witnesses = [(cas_word, cas_clause)] + [case for cases in probes.values() for case in cases]
    umov_clause = next(clause for clause in clauses if clause.mnemonic == "umov_advsimd")
    umov_word = 0x0E013FE2
    status, owner = sail_decode(umov_word, clauses, by_group, interp)
    if status != "valid" or owner is not umov_clause:
        raise SystemExit(f"Expected Sail to decode {umov_word:08x} as UMOV, got {status}")
    witnesses.append((umov_word, umov_clause))
    sampled_words = {word for word, *_ in rows}
    for word, owner in witnesses:
        if word not in sampled_words:
            rows.append((word, owner, "valid", owner))
            sampled_words.add(word)
    repo = Path(__file__).resolve().parent.parent
    report, add_widths, mismatches = coverage_report(repo, clauses, rows, probes)

    totals = defaultdict(Counter)
    for row in report:
        totals[row["area"]][row["state"]] += 1
    origin = f"{args.sail} (sha256 {digest[:12]})" if args.sail else f"@ {SAIL_COMMIT[:12]}"
    print(f"Sail arm-v9.4-a {origin}: {len(clauses)} A64 clauses, "
          f"{len(rows)} sampled words")
    states = ("covered", "partial", "missing", "unsampled")
    print(f"{'area':22} {'clauses':>7}" + "".join(f" {s:>9}" for s in states))
    for area, _ in AREAS + [("SVE", ()), ("SME", ()), ("other", ())]:
        t = totals.get(area)
        if t:
            print(f"{area:22} {sum(t.values()):7}" + "".join(f" {t[s]:9}" for s in states))
    unknown = sum(r["unknown"] for r in report)
    print(f"samples Sail's decoder could not be evaluated on: {unknown}")
    print(f"words HOL4 decodes that Sail does not accept: {len(mismatches)}")
    for word, clause, status in mismatches[:20]:
        print(f"  {word:08x} {clause.mnemonic} ({clause.instr_class}): {status}")
    if args.json:
        evidence, unassigned = hol_evidence(repo, clauses, by_group, interp)
        for row in report:
            tests = evidence[row["clause"]]
            row["execution"] = {
                "state_update_observations": len(tests["native"]),
                "instruction_fault_theorems": sorted(tests["fault"]),
            }
            row["validation"] = {
                "native": sorted(tests["native"]),
                "l3": sorted(tests["l3"]),
                "l3_discrepancies": sorted(tests["l3_discrepancy"]),
            }
        args.json.write_text(json.dumps({
            "sail_commit": None if args.sail else SAIL_COMMIT,
            "sail_sha256": digest,
            "clauses": report,
            "add_widths": add_widths,
            "mismatches": [f"{w:08x}" for w, *_ in mismatches],
            "unassigned_evidence": unassigned,
            "universal": {
                "encode_after_successful_decode": "arm64IsaTheory.encode_of_decode",
                "finite_execution_refines_model": "arm64IsaCvTheory.step_cv_refines",
            },
        }, indent=1) + "\n")
    if args.accept_add:
        if mismatches:
            raise SystemExit("HOL4 accepted a sampled encoding rejected by Sail")
        if not any(row["clause"] == cas_clause.index and row["state"] == "missing"
                   for row in report):
            raise SystemExit("Expected the valid CAS clause to have state missing")
        check_add(repo, clauses, rows, probes, report, add_widths)


if __name__ == "__main__":
    main()

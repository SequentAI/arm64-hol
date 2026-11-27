.text

// Enter a case with X0-X3, one Q-register pair and NZCV from the supplied state.
// X9 holds the state pointer, X10 the host return address, and X13 the RET offset.
// X14 holds the host stack pointer and X15 the probe stack pointer.
.global native_step
.type native_step, %function
native_step:
    mov x9, x0
    mov x11, x1
    mov x10, x30
    mov x13, x2
    // AAPCS64 requires preserving the low halves of V8–V15.
    stp d8, d9, [sp, #-64]!
    stp d10, d11, [sp, #16]
    stp d12, d13, [sp, #32]
    stp d14, d15, [sp, #48]
    mov x14, sp
    uxtw x16, w3
    ldp x15, x30, [x9, #144]
    mov x17, #0
    ldp x0, x1, [x9]
    ldp x2, x3, [x9, #16]
    adr x7, .Lload_pairs
    add x7, x7, x16, lsl #2
    br x7
.Lloads_done:
    ldr x8, [x9, #64]
    msr nzcv, x8
    br x11

.Lfinish:
    stp x0, x1, [x9]
    stp x2, x3, [x9, #16]
    adr x7, .Lstore_pairs
    add x7, x7, x16, lsl #2
    br x7
.Lstores_done:
    mrs x8, nzcv
    stp x8, x12, [x9, #64]
    cbz x17, 1f
    sub x30, x30, x17
    add x30, x30, #256
1:  stp x15, x30, [x9, #144]
    ldp d10, d11, [sp, #16]
    ldp d12, d13, [sp, #32]
    ldp d14, d15, [sp, #48]
    ldp d8, d9, [sp], #64
    ret x10

.macro start name
    .global case_\name
    .type case_\name, %function
case_\name:
.endm

.macro word_label name
    .global ins_\name
ins_\name:
.endm

.macro next
    mov x12, #4
    b .Lfinish
.endm

.macro straight name, instruction
    start \name
    word_label \name
    \instruction
    next
.endm

// Literal probes address the pool 48 bytes before and 12 bytes after them.
.macro literal_probe name, instruction
    start \name
    b 1f
8:  literal_pool
1:
    word_label \name
    \instruction
    next
9:  literal_pool
.endm

.macro stack_probe name, instruction
    start \name
    mov sp, x15
    word_label \name
    \instruction
    mov x15, sp
    mov sp, x14
    next
.endm

start cbz
word_label cbz
    cbz w1, 1f
    b 2f
1:  mov x12, #8
    b .Lfinish
2:  next

straight mov, "mov x2, x0"
straight movz, "movz w0, #0x8001"
straight addext, "add x3, x2, w1, uxtw"
straight ldrb, "ldrb w1, [x2], #1"
straight add, "add w0, w0, w1"
straight cmp, "cmp x2, x3"

start bne
    b 2f
1:  mov x12, #-12
    b .Lfinish
2:  nop
word_label bne
    b.ne 1b
    next

start ret
    adr x17, .Lret
    mov x30, x17
    add x30, x30, x13
word_label ret
.Lret:
    ret
    next
    mov x12, #12
    b .Lfinish
    mov x12, #20
    b .Lfinish

start br
word_label br
    br x1
    next
    mov x12, #12
    b .Lfinish
    mov x12, #20
    b .Lfinish

start blr
    adr x17, ins_blr
word_label blr
    blr x1
    next
    mov x12, #12
    b .Lfinish
    mov x12, #20
    b .Lfinish

straight ldpq, "ldp q0, q1, [x1]"
straight stpq, "stp q0, q1, [x0]"
straight stpx, "stp xzr, xzr, [x0, #16]"
straight movi, "movi v0.2d, #0"
straight nop, "nop"
straight stpx_regs, "stp x1, x2, [x0]"
straight stpx_zero, "stp xzr, xzr, [x0]"
stack_probe addsp, "add sp, sp, w1, uxtw"
stack_probe ldrb_sp, "ldrb w1, [sp], #1"
straight ldpq_pos, "ldp q0, q1, [x1, #16]"
straight stpq_neg, "stp q0, q1, [x0, #-16]"

.include "scalar_probes.S"
.include "simd_probes.S"

.section .note.GNU-stack,"",%progbits

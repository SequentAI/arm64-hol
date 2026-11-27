#include <inttypes.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#include "scalar_probes.h"
#include "simd_probes.h"

typedef void (*instruction)(void);

extern const unsigned char ins_adr[], ins_adr_back[], ins_adrp[], ins_adrp_back[], ins_br[], ins_blr[];

#define CASES(X) \
    X(cbz, -1, 0, 0, 0) X(mov, -1, 0, 0, 0) X(movz, -1, 0, 0, 0) X(addext, -1, 0, 0, 0) X(ldrb, 2, 0, 0, 0) \
    X(add, -1, 0, 0, 0) X(cmp, -1, 0, 0, 0) X(bne, -1, 0, 0, 0) X(ret, -1, 0, 0, 0) X(ldpq, 1, 0, 0, 0) \
    X(stpq, 0, 0, 0, 0) X(stpx, 0, 0, 0, 0) X(movi, -1, 0, 0, 0) X(nop, -1, 0, 0, 0) X(stpx_regs, 0, 0, 0, 0) X(stpx_zero, 0, 0, 0, 0) \
    X(addsp, -1, 0, 0, 0) X(ldrb_sp, -1, 0, 0, 0) X(ldpq_pos, 1, 0, 0, 0) X(stpq_neg, 0, 0, 0, 0) \
    SCALAR_CASES(X) SIMD_CASES(X) CCMP_FALLBACK_CASES(X) X(br, -1, 0, 0, 0) X(blr, -1, 0, 0, 0) PERMUTE_CASES(X) \
    CRC_CASES(X) CRYPTO_SIMD_CASES(X) STRUCTURE_CASES(X)
#define DECLARE(name, pointer_reg, indexed, stack, vector_base) extern void case_##name(void);
CASES(DECLARE)
#define CASE_ID(name, pointer_reg, indexed, stack, vector_base) Case_##name,
enum case_id { CASES(CASE_ID) };

typedef struct {
    uint64_t regs[4];
    uint64_t vectors[8];
    uint64_t nzcv;
    int64_t pc_delta;
    _Alignas(16) uint8_t data[64];
    uint64_t sp;
    uint64_t lr;
} state;

_Static_assert(offsetof(state, vectors) == 32, "vector offset");
_Static_assert(offsetof(state, nzcv) == 96, "NZCV offset");
_Static_assert(offsetof(state, pc_delta) == 104, "PC offset");
_Static_assert(offsetof(state, sp) == 176, "SP offset");

extern void native_step(state *, instruction, int64_t link_delta, int vector_base);

static uint64_t random_word(void)
{
    static uint64_t seed = UINT64_C(0xcd48ae560d3b6b97);
    seed ^= seed << 13;
    seed ^= seed >> 7;
    seed ^= seed << 17;
    return seed;
}

static void emit(const state *s)
{
    printf("%" PRId64 " %016" PRIx64 " %01" PRIx64, s->pc_delta, s->sp, s->nzcv >> 28);
    for (size_t i = 0; i < 4; ++i)
        printf(" %016" PRIx64, s->regs[i]);
    for (size_t i = 0; i < 8; ++i)
        printf(" %016" PRIx64, s->vectors[i]);
    printf(" %016" PRIx64 " ", s->lr);
    for (size_t i = 0; i < sizeof(s->data); ++i)
        printf("%02x", (unsigned)s->data[i]);
    putchar('\n');
}

/* FIPS 197 (2001), Appendix C.1. Vector byte 0 is the low byte. */
static void set_aes_example(state *s, enum case_id id)
{
    switch (id) {
    case Case_aese:
        s->vectors[0] = UINT64_C(0x7766554433221100);
        s->vectors[1] = UINT64_C(0xffeeddccbbaa9988);
        s->vectors[2] = UINT64_C(0x0706050403020100);
        s->vectors[3] = UINT64_C(0x0f0e0d0c0b0a0908);
        break;
    case Case_aesd:
        s->vectors[0] = UINT64_C(0x30047b6ad8e0c469);
        s->vectors[1] = UINT64_C(0x5ac5b47080b7cdd8);
        s->vectors[2] = UINT64_C(0x174a94e37f1d1113);
        s->vectors[3] = UINT64_C(0xc5302b4d8ba707f3);
        break;
    case Case_aesmc:
        s->vectors[0] = UINT64_C(0x04e160098ce05363);
        s->vectors[1] = UINT64_C(0xe7d0caba51b770cd);
        break;
    case Case_aesimc:
        s->vectors[2] = UINT64_C(0x92bcf5571564725f);
        s->vectors[3] = UINT64_C(0x1af9b91d293bbef7);
        break;
    default:
        break;
    }
}

static void run_case(const char *name, instruction code, enum case_id id,
                     int pointer_reg, int indexed, int stack, int vector_base)
{
    const uint64_t edges[] = {0, 0x100000000, 0xffffffff,
                              0x7fffffff, 0x80000000, UINT64_MAX};
    for (size_t n = 0; n < 8; ++n) {
        state s = {0};
        for (size_t i = 0; i < 4; ++i)
            s.regs[i] = n < 6 ? edges[(n + i + 5) % 6] : random_word();
        for (size_t i = 0; i < 8; ++i)
            s.vectors[i] = random_word();
        for (size_t i = 0; i < sizeof(s.data); ++i)
            s.data[i] = (uint8_t)random_word();
        s.nzcv = (random_word() & 15) << 28;
        if (n == 0)
            set_aes_example(&s, id);
        if ((id == Case_tbl || id == Case_tbx) && n == 0) {
            s.vectors[0] = UINT64_C(0x1817161514131211);
            s.vectors[1] = UINT64_C(0x201f1e1d1c1b1a19);
            s.vectors[2] = UINT64_C(0xff10fe0f09080700);
            s.vectors[3] = UINT64_C(0x01800520f002100e);
        }
        if ((id == Case_shl_4s || id == Case_ushr_4s) && n == 0) {
            s.vectors[0] = UINT64_C(0x0000000180000000);
            s.vectors[1] = UINT64_C(0x7fffffff00000001);
            s.vectors[2] = s.vectors[0];
            s.vectors[3] = s.vectors[1];
        }
        if (id == Case_cmeq_16b && n == 0)
            s.vectors[3] = s.vectors[1];
        if (id == Case_cmeq_zero && n == 0)
            s.vectors[1] &= UINT64_C(0xff00ffff00ffffff);
        if ((id == Case_tst_byte || id == Case_tst_half) && n == 0)
            s.regs[1] = 0x100;
        if (id == Case_bne)
            s.nzcv = (s.nzcv & ~(UINT64_C(1) << 30)) | ((n & 1) << 30);
        if (id == Case_tbnz_back)
            s.regs[1] = (n & 1) ? UINT64_C(1) << 5 : UINT64_C(1) << 31;
        if (id == Case_cmp && n == 0)
            s.regs[2] = s.regs[3];
        if (id == Case_cmp && n == 1) {
            s.regs[2] = INT64_MAX;
            s.regs[3] = UINT64_MAX;
        }
        if (id == Case_cmp && n == 2) {
            s.regs[2] = UINT64_MAX;
            s.regs[3] = INT64_MAX;
        }
        if (id == Case_ccmp_x || id == Case_ccmp_n ||
            id == Case_ccmp_z || id == Case_ccmp_v)
            s.nzcv = n & 1 ? (UINT64_C(1) << 29) : (UINT64_C(1) << 30);
        if (id == Case_ccmp_z && n == 0)
            s.nzcv = 0; /* HI is false and fallback must set Z. */
        if (id == Case_ccmp_w)
            s.nzcv = n & 1 ? (UINT64_C(1) << 30) : (UINT64_C(1) << 29);
        if (id == Case_adcs_x && n == 0) {
            s.regs[1] = INT64_MAX;
            s.regs[2] = 0;
            s.nzcv |= UINT64_C(1) << 29;
        }
        if (id == Case_sbcs_x && n == 0) {
            s.regs[1] = (uint64_t)INT64_MIN;
            s.regs[2] = 0;
            s.nzcv &= ~(UINT64_C(1) << 29);
        }
        if ((id == Case_lslv_x || id == Case_lsrv_w || id == Case_asrv_x) && n == 0) {
            s.regs[1] = UINT64_C(0x80000000f0000000);
            s.regs[2] = 68;
        }
        if ((id == Case_add_uxtb || id == Case_add_uxth ||
             id == Case_add_sxtb || id == Case_add_sxth) && n < 2) {
            // Byte and halfword sign bits disagree, and the upper bits are nonzero.
            s.regs[2] = n == 0 ? UINT64_C(0x1122334455667a80)
                               : UINT64_C(0x1122334455668a7f);
        }
        if (id == Case_udiv_x || id == Case_udiv_w ||
            id == Case_sdiv_x || id == Case_sdiv_w) {
            if (n == 0)
                s.regs[2] = 0;
            if (n == 1) {
                s.regs[1] = id == Case_sdiv_w ? UINT32_C(0x80000000) : (uint64_t)INT64_MIN;
                s.regs[2] = UINT64_MAX;
            }
        }
        // Audit both target paths and distinguish a fall-through at PC+4.
        const int64_t branch_delta = (n & 1) ? 20 : 12;
        const int64_t link_delta = id == Case_ret ? branch_delta : 0;
        const int signed_index = id == Case_ldrh_sxtw || id == Case_ldr_sxtx;
        const int interior_base = signed_index || id == Case_stpq_neg ||
                                  id == Case_ldr_pre_neg || id == Case_stur_w_neg;
        // A 64-byte structure transfer fills the whole data window.
        const size_t offset = WIDE_CASE(id) ? 0 : n + (interior_base ? 16 : 0);
        const int uses_sp = stack || id == Case_addsp || id == Case_ldrb_sp;
        const size_t sp_offset = stack ? 16 + (n % 2) * 16 : (n % 4) * 16;
        s.sp = uses_sp ? 0x1000 + sp_offset : 0x2000;
        if (pointer_reg >= 0)
            s.regs[pointer_reg] = 0x1000 + offset;
        if (signed_index) {
            const uint64_t index = (uint64_t)(-1 - (int64_t)(n % 4));
            s.regs[2] = id == Case_ldrh_sxtw
                ? UINT64_C(0x1122334400000000) | (uint32_t)index
                : index;
        } else if (indexed) {
            s.regs[2] = id == Case_ldrh_reg
                ? UINT64_C(0x1122334400000000) | n
                : n;
        }
        s.lr = id == Case_ret ? (uint64_t)(256 + link_delta) : UINT64_C(0x12345678);
        if (id == Case_br || id == Case_blr)
            s.regs[1] = (uint64_t)(256 + branch_delta);
        printf("%s\n", name);
        emit(&s);
        if (pointer_reg >= 0)
            s.regs[pointer_reg] = (uintptr_t)(s.data + offset);
        if (uses_sp)
            s.sp = (uintptr_t)(s.data + sp_offset);
        const uintptr_t branch = (uintptr_t)(id == Case_blr ? ins_blr : ins_br);
        if (id == Case_br || id == Case_blr)
            s.regs[1] += branch - 256;
        native_step(&s, code, link_delta, vector_base);
        if (id == Case_br || id == Case_blr)
            s.regs[1] += 256 - branch;
        if (pointer_reg >= 0)
            s.regs[pointer_reg] = 0x1000 + (s.regs[pointer_reg] - (uintptr_t)s.data);
        if (uses_sp)
            s.sp = 0x1000 + (s.sp - (uintptr_t)s.data);
        if (id == Case_adr || id == Case_adr_back) {
            const uintptr_t pc = (uintptr_t)(id == Case_adr ? ins_adr : ins_adr_back);
            s.regs[0] += 256 - pc;
        }
        if (id == Case_adrp || id == Case_adrp_back) {
            const uintptr_t pc = (uintptr_t)(id == Case_adrp ? ins_adrp : ins_adrp_back);
            s.regs[0] -= pc & ~(uintptr_t)4095;
        }
        emit(&s);
    }
}

static void report_access_fault(int signal, siginfo_t *info, void *context)
{
    (void)signal;
    (void)context;
    _exit(info->si_code == SEGV_ACCERR ? 0 : 1);
}

static int access_is_denied(void *page, int fetch)
{
    pid_t child = fork();
    if (child == 0) {
        struct sigaction action = {.sa_sigaction = report_access_fault,
                                   .sa_flags = SA_SIGINFO};
        sigemptyset(&action.sa_mask);
        if (sigaction(SIGSEGV, &action, NULL) != 0)
            _exit(1);
        if (fetch)
            ((instruction)(uintptr_t)page)();
        else
            *(volatile uint32_t *)page = 0;
        _exit(1);
    }
    if (child < 0) {
        perror("fork");
        return 0;
    }
    int status;
    if (waitpid(child, &status, 0) < 0) {
        perror("waitpid");
        return 0;
    }
    if (WIFEXITED(status) && WEXITSTATUS(status) == 0)
        return 1;
    fprintf(stderr, "native R-- page did not report SEGV_ACCERR on %s\n",
            fetch ? "instruction fetch" : "store");
    return 0;
}

static int check_read_only_page(void)
{
    const long page_size = sysconf(_SC_PAGESIZE);
    if (page_size <= 0) {
        perror("sysconf(_SC_PAGESIZE)");
        return 0;
    }
    void *page = mmap(NULL, (size_t)page_size, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (page == MAP_FAILED) {
        perror("mmap");
        return 0;
    }
    const uint32_t ret = UINT32_C(0xd65f03c0);
    *(uint32_t *)page = ret;
    __builtin___clear_cache(page, (char *)page + sizeof(ret));
    int passed = 0;
    if (mprotect(page, (size_t)page_size, PROT_READ) != 0)
        perror("mprotect");
    else if (*(volatile const uint32_t *)page != ret)
        fprintf(stderr, "native R-- page lost its readable contents\n");
    else
        passed = access_is_denied(page, 0) && access_is_denied(page, 1);
    munmap(page, (size_t)page_size);
    return passed;
}

int main(void)
{
    if (!check_read_only_page())
        return 1;
#define RUN(name, pointer_reg, indexed, stack, vector_base) \
    run_case(#name, case_##name, Case_##name, pointer_reg, indexed, stack, vector_base);
    CASES(RUN)
}

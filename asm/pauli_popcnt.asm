; SPDX-License-Identifier: Apache-2.0
; Copyright (c) 2026 Alexander Stephen Donahue
;
; Bare-metal x86-64 NASM Assembly kernel for Pillar I binary Pauli symplectic
; algebra and canonical graph-state weight enumeration (`asm/pauli_popcnt.asm`).
;
; Supports BOTH Windows x64 ABI (-DWIN64 -f win64) and System V AMD64 ABI (-f elf64).
; Uses SSE4.2 hardware POPCNT and portable BSF + (x & (x-1)) bit clearing (no BMI1 required).

default rel
section .text

global qpr_asm_symp_f2
global qpr_asm_pauli_weight
global qpr_asm_graph_weight_enum

; -----------------------------------------------------------------------------
; uint32_t qpr_asm_symp_f2(uint64_t x1, uint64_t z1, uint64_t x2, uint64_t z2)
; Computes binary symplectic inner product (popcnt(x1 & z2) ^ popcnt(z1 & x2)) & 1
; -----------------------------------------------------------------------------
qpr_asm_symp_f2:
%ifdef WIN64
    ; Win64: rcx=x1, rdx=z1, r8=x2, r9=z2
    mov     rax, rcx
    and     rax, r9             ; x1 & z2
    popcnt  rax, rax
    mov     rcx, rdx
    and     rcx, r8             ; z1 & x2
    popcnt  rcx, rcx
    xor     rax, rcx
    and     eax, 1
    ret
%else
    ; SysV: rdi=x1, rsi=z1, rdx=x2, rcx=z2
    mov     rax, rdi
    and     rax, rcx            ; x1 & z2
    popcnt  rax, rax
    mov     rdi, rsi
    and     rdi, rdx            ; z1 & x2
    popcnt  rdi, rdi
    xor     rax, rdi
    and     eax, 1
    ret
%endif

; -----------------------------------------------------------------------------
; uint32_t qpr_asm_pauli_weight(uint64_t x, uint64_t z)
; Computes exact N-qubit binary Pauli weight popcnt(x | z)
; -----------------------------------------------------------------------------
qpr_asm_pauli_weight:
%ifdef WIN64
    ; Win64: rcx=x, rdx=z
    or      rcx, rdx
    popcnt  rax, rcx
    ret
%else
    ; SysV: rdi=x, rsi=z
    or      rdi, rsi
    popcnt  rax, rdi
    ret
%endif

; -----------------------------------------------------------------------------
; void qpr_asm_graph_weight_enum(uint32_t n, const uint64_t *adj, uint64_t *counts)
; Exhaustively enumerates all 2^n canonical Z_2 graph stabilizer elements
; (n <= 24) and accumulates exact weight histogram counts[0..n].
; Bounds-guarded: ignores n > 24 and masks adjacency bits to [0..n-1].
; -----------------------------------------------------------------------------
qpr_asm_graph_weight_enum:
    push    rbx
    push    r12
    push    r13
    push    r14
    push    r15
%ifdef WIN64
    ; Win64: ecx=n, rdx=adj, r8=counts
    mov     r12d, ecx           ; n
    mov     r13, rdx            ; adj
    mov     r14, r8             ; counts
%else
    ; SysV: edi=n, rsi=adj, rdx=counts
    mov     r12d, edi           ; n
    mov     r13, rsi            ; adj
    mov     r14, rdx            ; counts
%endif
    ; Guard: require n <= 24 so 1ULL << n and counts[0..n] stay strictly bounded
    cmp     r12d, 24
    ja      .done

    ; Zero counts[0..n] (unsigned loop)
    xor     eax, eax
.zero_loop:
    mov     qword [r14 + rax*8], 0
    inc     eax
    cmp     eax, r12d
    jbe     .zero_loop

    ; limit = 1ULL << n; bitmask = limit - 1 in r10
    mov     ecx, r12d
    mov     r15, 1
    shl     r15, cl             ; r15 = 2^n
    lea     r10, [r15 - 1]      ; r10 = (1ULL << n) - 1

    xor     rbx, rbx            ; mask = 0
.mask_loop:
    xor     rax, rax            ; zmask = 0
    mov     rdx, rbx            ; remaining set bits of mask
.bit_loop:
    test    rdx, rdx
    jz      .bit_done
    bsf     rcx, rdx            ; lowest set bit index i (portable x86-64)
    xor     rax, qword [r13 + rcx*8]
    lea     r9, [rdx - 1]       ; clear lowest set bit without BMI1
    and     rdx, r9
    jmp     .bit_loop
.bit_done:
    and     rax, r10            ; mask zmask to lower n qubits
    or      rax, rbx            ; support = mask | zmask (at most n bits set)
    popcnt  rax, rax            ; exact Pauli weight w in [0..n]
    inc     qword [r14 + rax*8]
    inc     rbx
    cmp     rbx, r15
    jb      .mask_loop

.done:
    pop     r15
    pop     r14
    pop     r13
    pop     r12
    pop     rbx
    ret

%ifndef WIN64
section .note.GNU-stack noalloc noexec nowrite progbits
%endif

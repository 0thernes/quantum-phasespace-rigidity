# ADR 0002: Separating Cyclic Ring $\mathbb{Z}_d$ from Galois Field $\mathbb{F}_q$ Phase Spaces

- **Status:** Accepted (2026-11-26)
- **Context:** In composite prime-power dimensions $d = p^e$ ($e \ge 2$), quantum information literature uses two distinct Heisenberg–Weyl groups: the cyclic ring $\mathbb{Z}_{p^e}$ (used in canonical $\mathbb{Z}_d$ graph states, e.g., Wójcik et al. `2603.18193v3`) and the Galois field $\mathbb{F}_{p^e}$ (additive group $\mathbb{Z}_p^e$, used in MDS stabilizer codes such as $\mathrm{AME}(4,4)$ and in Ball–Simoens `2607.12933v2` $t$-MOQLS).
- **Decision:** Keep the cyclic-ring and Galois-field formalizations strictly separated at the type level in Lean (`CyclicStabilizer` over `ZMod d` vs. `GaloisF4Stabilizer` over `F4`), and explicitly prove the **Ring-vs-Field Separation Theorem** at $(N, d) = (4, 4)$.
- **Consequences:** Eliminates the most common category error in composite-dimension stabilizer literature while highlighting the exact algebraic source of rigidity.

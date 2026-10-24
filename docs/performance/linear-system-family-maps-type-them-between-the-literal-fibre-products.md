> [Case index](README.md) · [Methods](../PERFORMANCE.md#conversion-boundaries).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Linear-system family maps: type them between the literal fibre products

Measured on 2026-10-24 at Lean 4.34.1, Mathlib `d13f23b`, remote profile `aglib-picard-f15lemmas`,
profiler threshold 2 s (200 ms for the probes). The probe module `Aglib/Scratch/ProbeF15b.lean`
was not retained.

1. The first complete `Picard/LinearSystem/Representability` built in 109 s
   (`remote-2129f79b21d04d7fa352dfba8360237d`). Under the profiler it took 103 s, of which 86.3 s
   was type checking of `subbundleDivisor_comap` (`remote-a3e5ef4c84004c5a98cfa309695b2d04`).
   Split into a section base change and an assembly, the two declarations took 49.5 s and 49.8 s
   of type checking (module 110 s, `remote-91dd1cf19fa3478587ba3b1d8e842d70`). With the section
   base change proved at variable data (`pullback_map_comp_evaluation_of_square`, below the
   threshold), its concrete instantiation still took 56.3 s and the assembly 53.3 s (module
   123 s, `remote-d190cffac4a84ed2b957b58e7fddd733`).
2. Kernel unfolding counters (`diagnostics`) for the instantiated lemma: `WalkingPair.casesOn`
   434,668, `Over.left` 434,660, `pullback.fst` 144,888, `TopologicalSpace.Opens.carrier` 71,532
   and `Set.preimage` 69,654 in the probe `remote-d4006c74011647ceaf91f137fded4c33`; 467,716,
   467,708, 155,904, 76,990 and 75,000 in the module copy `remote-ae17eca5fee34a109b6afd783984d775`.
3. Probes. The object conversions `(familyScheme p).obj T = pullback p T.hom` and
   `(pullback (X := (familyScheme p).obj T) f).obj M = (pullback f).obj M` by `rfl` stayed below
   200 ms (`remote-2b623eb2ae6a4f9c8b8dfb1baeda950c`). Matching the instantiated conclusion against
   the declared statement took 44.0 s, 44.7 s and 48.4 s of type checking across the term,
   `rw`-unfolded and `have`/`exact` forms; the same run records 51.8 s of elaboration, with
   `diagnostics` on, for the first declaration and 7.4 s and 5.5 s of `exact` for the other two,
   and 0.26 s of elaboration for the `have` alone (`remote-d4006c74011647ceaf91f137fded4c33`).
   Converting `pullback_map_evaluationMap` from its statement over `(familyScheme p).map t` to the
   same statement over `familyMap' p t : pullback p T'.hom ⟶ pullback p T.hom` took 65.7 s of type
   checking and 8.7 s of elaboration; the instantiation over `familyMap'` throughout took 0.21 s
   of elaboration, with type checking below the threshold (`remote-b84bd99e097846e6a99aec98aee52ee5`).
4. Change: `familyMap p t := (familyScheme p).map t`, typed with the literal fibre products as
   source and target, in every statement (functor map, divisor base change, evaluation-map base
   change). `Representability` then built in 11 s (`remote-5628056b66a94c74aafc6f2b87a66262`;
   12 s profiled in `remote-eaa6fb1e04074ea69a48bed4cf12e56f`, largest declaration 5.66 s of type
   checking, the variable-data pairing lemma). `Evaluation` went from 78 s
   (`remote-4f1f94b2a5df409baab79123758e4537`) to 23 s (`remote-eaa6fb1e04074ea69a48bed4cf12e56f`),
   with no declaration above 2 s.

Candidate mechanism, not verified: conversions between morphisms typed over
`(familyScheme p).obj T` and module sheaves typed over `Limits.pullback p T.hom` make the kernel
reduce the cospan and limit structure of `pullback.fst` and preimages of opens instead of matching
arguments. The counters in item 2 are consistent with this; no conversion pair was isolated.

Rule: when a functor's values are literal fibre products, give its maps a named definition typed
between those literal objects and state every lemma through it.

### Follow-up: isomorphisms obtained from a `familyScheme`-typed square

Measured on 2026-10-24, remote profile `aglib-picard-relation`, module
`Picard/LinearSystem/AbelClass`. With the transport isomorphism
`X ×_S U ≅ X_V ×_V U` taken as `IsPullback.isoPullback` of
`RelativePicard.isPullback_familyScheme_map p g` (a square typed over `(familyScheme p).obj U`), the
first build (`remote-a831fc8bf01c49aeb6a67862ab1058de`, 38 s, exit 1) failed at every `rw` through
the isomorphism ("The target expression is not type-correct under the `implicit` transparency
level", with `pullback.snd p V.hom` expected at `(familyScheme p).obj V ⟶ V.left`) and had one
`whnf` heartbeat timeout. With the same square typed between the literal fibre products
(`LinearSystem.isPullback_familyMap p g`, definitionally equal) the module built in 4.7 s
(`remote-a6f8608c144a4f4fad5cb3094c08b848`). Candidate mechanism, not measured: the same
representation mismatch as above, here surfacing as rewrite-motive failures rather than kernel
cost. The rule above covers it: `IsPullback.isoPullback` of a `familyScheme`-typed square inherits
the `familyScheme` types, so take the isomorphism from the literal-typed square.

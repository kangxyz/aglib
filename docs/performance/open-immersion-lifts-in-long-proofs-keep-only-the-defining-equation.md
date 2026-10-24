> [Case index](README.md) · [Methods](../PERFORMANCE.md#shared-constructions-and-equations).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Open-immersion lifts in long proofs: keep only the defining equation

Measured on 2026-10-24 at Lean 4.34.1, Mathlib `d13f23b`, Aglib base `7da8e088`, remote profile
`aglib-picard-hfin2` (8 frontends × 4 threads). Declaration:
`AlgebraicGeometry.ProjectiveSpace.eq_of_comap_sigmaImmersedHilbertFamily_eq`
(`HilbertScheme/Coproduct/Representability`).

1. The first version was one tactic proof. It introduced the component lifts with
   `let a' := IsOpenImmersion.lift (Sigma.ι _ Φ) (flatteningStratumι … ≫ a) _` (and `b'`), then
   used `refine eq_of_comap_homEquiv_id_eq … a' b' …` and two `refine ((…).symm.trans ?_).trans …`
   steps.
   - Run `remote-fc11132dcebb498d9b06e5432f8f582b` (module source sha256 `a580aae7…`): a
     deterministic timeout at `whnf` at 200000 heartbeats at the declaration.
   - Run `remote-2ea4ee76e18f4a88b53634d6b4d51b19` (source `a48f2b2b…`, `maxHeartbeats 2000000`,
     profiler threshold 200 ms): "tactic execution of Lean.Parser.Tactic.refine took 341s", still
     a timeout at `whnf`; cumulative tactic execution 341 s, elaboration 5.89 s, typeclass
     inference 294 ms; the module failed after 353 s.
   - Neither failing source was retained.
2. The repair made three changes together:
   - the lifts were introduced with `obtain ⟨a', ha'⟩ : ∃ a', a' ≫ Sigma.ι _ Φ = s ≫ a :=
     ⟨IsOpenImmersion.lift _ _ hsa, IsOpenImmersion.lift_fac _ _ _⟩`;
   - the per-component step was split into
     `range_comp_subset_range_sigmaι_of_fiberHilbertPolynomialAt_eq` and
     `comp_eq_comp_of_comap_sigmaImmersedHilbertFamily_eq`;
   - the rewriting chain became named `have`s composed by `Eq.trans`.

   The module then built in 8.1 s (`remote-1e9a9dad623c4ee0a09e7cb477d03744`, unprofiled,
   source `f20ccf64…`). The landed module, source `e3365b52…` with the concrete layer added,
   built in 21 s (`remote-d1128f17014c4d0db53875001421e756`).
3. These are separate observations, not a matched comparison: the failing runs were profiled or
   cut off by the heartbeat limit and used other sources. No single change was isolated.

Candidate mechanism, not verified: unification during `refine` unfolds the `let`-bound
`IsOpenImmersion.lift` values (`whnf`); with `obtain`, only the defining equation is in context.

Rule, from this single combined repair: when a long proof needs only the defining equation of a
large constructed value, such as a lift through an open immersion, introduce it with
`obtain ⟨x, hx⟩ : ∃ x, … := ⟨…, …⟩`, and split per-component steps into lemmas. When a consumer
needs the value's formula, a local `let` remains the right tool
([What the measurements establish](what-the-measurements-establish.md)).

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Separated

/-!
# Representability of the fppf Picard functor

Let `A` be a Noetherian ring, `i : X ⟶ P^N_A = ProjectiveSpace A ι` a closed immersion with
`ι ≃ Fin (N + 1)`, such that `p = i ≫ toSpec A ι` is flat with geometrically integral fibres
(`p` is then proper). Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8, pp. 27–28,
states: `Pic_{X/S}` exists, is separated and locally of finite type over `S`, and is a disjoint
union of open subschemes, each an increasing union of open quasi-projective `S`-schemes. This file
collects the fppf form on locally Noetherian test schemes
(`exists_representableBy_fppfPicardSheaf_of_fineStrata`)
from [Glue](Scheme/Glue.lean), [Stratification](Scheme/Stratification.lean) and
[Separated](Scheme/Separated.lean), under two premises:

* `Strata.FineStrataRepresentableByHQuasiProjective i N e`: each fine stratum
  `Pic^{φ₀,ψ,k+1}_0` is represented on locally Noetherian test schemes by an H-quasi-projective
  scheme (Kleiman, proof of Thm 4.8, p. 30, the representation of `P^{φ₀}_0`, refined by the base
  polynomial `ψ` and the rank `k + 1`);
* `Strata.FiniteFineStrataRanks i N e`: for fixed `(φ₀, ψ)` only finitely many ranks occur on the
  fine strata at level `0`; it is used only for the H-quasi-projectivity of the levels `Pic^φ_m`.

The conclusion: a locally Noetherian scheme `P` over `Spec A` representing the underlying presheaf
of sets of `Pic_{X/S,(fppf)}` on locally Noetherian test schemes, separated and locally of finite
type over `Spec A`, with opens `Pic^φ` (open and closed, pairwise disjoint, covering `P`) and
`Pic^φ_m` (increasing in `m` with union `Pic^φ`, each H-quasi-projective over `Spec A`), such that
a morphism `a : T ⟶ P` factors through `Pic^φ`, respectively `Pic^φ_m`, exactly when its section of
`Pic_{X/S,(fppf)}` lies in the subsheaf `Pic^φ`, respectively `Pic^φ_m`. The witnesses are
`picardScheme h`, `picardSchemeRepresentableBy h`, `picardStratumOpens h` and `picardLevelOpens h`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard

open Strata

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}

/-- **Representability of `Pic_{X/S,(fppf)}`** (Kleiman, arXiv:math/0504020v1, Thm 4.8,
pp. 27–31, for a Noetherian affine base and the fppf topology, on locally Noetherian test schemes):
under the representability of the fine strata at level `0` and the finiteness of their ranks, the
fppf Picard functor is represented by a locally Noetherian scheme over `Spec A` that is separated
and locally of finite type, with open and closed strata `Pic^φ` covering it, each the increasing
union of the H-quasi-projective opens `Pic^φ_m`, which are the loci of the subsheaves `Pic^φ` and
`Pic^φ_m`. -/
theorem exists_representableBy_fppfPicardSheaf_of_fineStrata [IsNoetherianRing A]
    (h : FineStrataRepresentableByHQuasiProjective i N e) (hrank : FiniteFineStrataRanks i N e) :
    ∃ (P : Scheme.LocallyNoetherianOver (Spec (.of A)))
      (R : ((Scheme.locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (stratum : Polynomial ℚ → P.obj.left.Opens) (level : Polynomial ℚ → ℤ → P.obj.left.Opens),
      IsSeparated P.obj.hom ∧ LocallyOfFiniteType P.obj.hom ∧
        (∀ φ, IsClopen (stratum φ : Set P.obj.left)) ∧ Pairwise (Function.onFun Disjoint stratum) ∧
        ⨆ φ, stratum φ = ⊤ ∧ (∀ φ, Monotone (level φ)) ∧ (∀ φ, ⨆ m, level φ m = stratum φ) ∧
        (∀ φ m, IsHQuasiProjective ((level φ m).ι ≫ P.obj.hom)) ∧
        ∀ {T : Scheme.LocallyNoetherianOver (Spec (.of A))} (a : T ⟶ P) (φ : Polynomial ℚ),
          (R.homEquiv a ∈ (eulerCondition i N e φ).subfunctor.obj (op T.obj) ↔
            a.hom.left ⁻¹ᵁ stratum φ = ⊤) ∧
          ∀ m, (R.homEquiv a ∈ (coarseCondition i N e φ m).subfunctor.obj (op T.obj) ↔
            a.hom.left ⁻¹ᵁ level φ m = ⊤) :=
  ⟨picardScheme h, picardSchemeRepresentableBy h, picardStratumOpens h, picardLevelOpens h,
    inferInstance, inferInstance, isClopen_picardStratumOpens h,
    pairwise_disjoint_picardStratumOpens h, iSup_picardStratumOpens h, monotone_picardLevelOpens h,
    iSup_picardLevelOpens h,
    fun φ m => isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks h hrank φ m,
    fun a φ => ⟨picardSchemeRepresentableBy_homEquiv_mem_eulerCondition_iff h φ a,
      fun m => picardSchemeRepresentableBy_homEquiv_mem_coarseCondition_iff h φ m a⟩⟩

end AlgebraicGeometry.Scheme.RelativePicard

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Galois.SylowFactorization
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Restriction
public import Aglib.AlgebraicGeometry.FundamentalGroup.PointedPower

/-! # Prime-to-p restriction of actual finite-etale monodromy

The Sylow fixed field is an actual intermediate field of the same ambient
Galois extension. The original pointed fibre map identifies its monodromy
with restriction of scalars, and the actual pullback-fibre equivalence
transfers the p-power order statement to the original base-changed cover.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory
open Scheme.FiniteEtale Scheme.EtaleFundamentalGroups
open Scheme.FiniteEtale.FieldGalois.OverRing
open Scheme.FiniteEtale.GroupBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- A genuine finite prime-to-p field extension makes every original fibre
monodromy operator on the actual base-changed finite-etale cover have
p-power order. -/
theorem exists_primeTo_field_pPower_monodromy
    (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω] [IsGalois E Ω]
    (Y : Scheme.FiniteEtale (Spec (.of E))) {p : ℕ} [Fact p.Prime] :
    ∃ M : IntermediateField E Ω, FiniteDimensional E M ∧
      (Module.finrank E M).Coprime p ∧
      ∀ γ : FiberAutGroup (basePoint M Ω), ∃ n : ℕ,
        (PreGaloisCategory.autEmbedding (fiberToFinite (basePoint M Ω)) γ
          ((baseChange (Spec.algebraMap E M)).obj Y)) ^ p ^ n = 1 := by
  let F := fiberToFinite (basePoint E Ω)
  let ev : Aut F →* Aut (F.obj Y) :=
    (Pi.evalMonoidHom _ Y).comp (PreGaloisCategory.autEmbedding F)
  let eG := FieldGalois.Arbitrary.fundamentalGroupContinuousEquiv E Ω
  let ρ : (Ω ≃ₐ[E] Ω) →* Aut (F.obj Y) := ev.comp eG.toMulEquiv.toMonoidHom
  have hρ : Continuous ρ :=
    (continuous_apply Y).comp (continuous_induced_dom.comp eG.continuous)
  obtain ⟨M, hfin, hdegree, hM⟩ :=
    InfiniteGalois.exists_primeTo_intermediateField_isPGroup_image (p := p) ρ hρ
  let := hfin
  refine ⟨M, hfin, hdegree, ?_⟩
  intro γ
  obtain ⟨σ, rfl⟩ := FieldGalois.Arbitrary.galoisToFibre_surjective M Ω γ
  let τ : M.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv M).symm σ
  obtain ⟨n, hn⟩ := hM ((ρ.comp M.fixingSubgroup.subtype).rangeRestrict τ)
  have hn' : ρ (σ.restrictScalars E) ^ p ^ n = 1 := congrArg Subtype.val hn
  refine ⟨n, ?_⟩
  let f : Under.mk (basePoint M Ω) ⟶ Under.mk (basePoint E Ω) :=
    Under.homMk (Spec.algebraMap E M) (basePoint_comp_algebraMap E M Ω)
  let β := galoisToFibre M M Ω σ
  have ht : (ev.comp (pointedMap f)) β = ρ (σ.restrictScalars E) :=
    congrArg (fun a => a.app Y) (inducedGroupHomPointed_galoisToFibre E M Ω σ)
  have hp : ev (pointedMap f β) ^ p ^ n = 1 :=
    (congrArg (fun z => z ^ p ^ n) ht).trans hn'
  exact component_pow_eq_one_of_pointedMap f β Y (p ^ n) hp

end AlgebraicGeometry.Scheme.EtaleCohomology

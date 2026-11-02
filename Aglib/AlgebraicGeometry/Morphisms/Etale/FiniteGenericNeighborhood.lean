/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteStalkNeighborhood
public import Mathlib.AlgebraicGeometry.FunctionField

/-! # Finite etale neighborhoods from the actual fraction-field base change

The arbitrary supplied fraction field is compared to the actual generic stalk by
the canonical localization equivalence. The existing finite-stalk neighborhood
theorem then produces the open; no second etale-locus construction is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Etaleness over a supplied fraction field spreads to an actual affine open
containing the generic point. Finite presentation is explicit, so the base
domain need not be Noetherian. -/
theorem exists_affine_etale_neighborhood_of_fractionField_baseChange
    (R : CommRingCat.{u}) [IsDomain R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec R) [IsFinite f] [LocallyOfFinitePresentation f]
    (het : Etale (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ∃ U : (Spec R).Opens, IsAffineOpen U ∧ genericPoint (Spec R) ∈ U ∧ Etale (f ∣_ U) := by
  let : Algebra R (Spec R).functionField :=
    StructureSheaf.stalkAlgebra R (genericPoint (Spec R))
  have : IsFractionRing R (Spec R).functionField :=
    @functionField_isFractionRing_of_affine R ‹IsDomain R›
  let e : (Spec R).functionField ≃ₐ[R] K :=
    IsLocalization.algEquiv R⁰ (Spec R).functionField K
  let E : Spec (.of K) ≅ Spec (Spec R).functionField :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let η := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let η₀ := (Spec R).fromSpecStalk (genericPoint (Spec R))
  have hη : E.hom ≫ η₀ = η := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (Spec R).fromSpecStalk (genericPoint (Spec R)) = η
    have he : StructureSheaf.toStalk R (genericPoint (Spec R)) ≫
        CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom (algebraMap R K) := by
      apply CommRingCat.hom_ext
      exact e.toAlgHom.comp_algebraMap
    have he' := congrArg Spec.map he
    rw [Spec.map_comp] at he'
    rw [Spec.fromSpecStalk_eq']
    exact he'
  have H : IsPullback (pullback.fst f η) (pullback.snd f η ≫ E.hom) f η₀ :=
    (IsPullback.of_hasPullback f η).of_iso (Iso.refl _) (Iso.refl _) E (Iso.refl _)
      (by simp) (by simp) (by simp) (by simpa using hη.symm)
  have : Etale (pullback.snd f η) := het
  have : Etale (pullback.snd f η ≫ E.hom) := inferInstance
  have hs : Etale (pullback.snd f η₀) := by
    have : Etale (H.isoPullback.inv ≫ (pullback.snd f η ≫ E.hom)) := inferInstance
    simpa only [IsPullback.isoPullback_inv_snd] using this
  obtain ⟨U, hUa, hU, hle, he⟩ :=
    f.exists_affine_etale_target_neighborhood_of_finite (genericPoint (Spec R)) hs ⊤ trivial
  exact ⟨U, hUa, hU, he⟩

end AlgebraicGeometry.Scheme

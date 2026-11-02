/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.ParameterBaseChange

/-! # The original boundary point after genuine parameter base change

The comparison is constructed internally by the genuine etale base-change
supplier. A given local-source lift to the ordinary pullback is transported
through its inverse, preserving both projections and the specified original
normalization point. No final comparison is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

/-- Transport the actual local root-stage lift through the constructed genuine
normalization comparison, retaining the original point and all three comparison
triangles. The local source is arbitrary and is not asserted finitely presented. -/
theorem exists_parameterNormalizedPointLift
    (R B T : Type u) [CommRing R] [IsDomain R] [IsRegularRing R]
    [CommRing B] [IsDomain B] [IsRegularRing B] [Algebra R B] [Algebra.Etale R B]
    [CommRing T] [IsLocalRing T] (f : R) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) :
    letI : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
    letI : IsDomain (Localization.Away (algebraMap R B f)) :=
      Localization.Away.isDomain (parameter_etale_algebraMap_ne_zero R B f hf)
    let j := Spec.algebraMap R (Localization.Away f)
    let jB := Spec.algebraMap B (Localization.Away (algebraMap R B f))
    let b := Spec.algebraMap R B
    let g := Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))
    letI : IsDominant g := Scheme.Kummer.parameterComplementBaseChange_dominant R B f hf
    let q₀ := genericMap j Y.obj.hom
    let qB := genericMap jB ((baseChange g).obj Y).obj.hom
    letI : ∀ x : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk x) :=
      fun x => @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_spec R x)
    letI : ∀ x : Spec (.of B), IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk x) :=
      fun x => @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_spec B x)
    ∀ (d : Spec (.of T) ⟶ pullback q₀.fromNormalization b)
      (r : Spec (.of T) ⟶ Spec (.of B)), d ≫ pullback.snd _ _ = r →
      ∀ x : q₀.normalization,
      pullback.fst q₀.fromNormalization b (d (IsLocalRing.closedPoint T)) = x →
      ∃ (e : qB.normalization ≅ pullback q₀.fromNormalization b)
        (a : Spec (.of T) ⟶ qB.normalization),
        e.hom ≫ pullback.snd _ _ = qB.fromNormalization ∧
        qB.toNormalization ≫ e.hom ≫ pullback.fst _ _ =
          genericPullbackMap g Y.obj.hom ≫ q₀.toNormalization ∧
        inclusion jB ((baseChange g).obj Y).obj.hom ≫ e.hom ≫ pullback.fst _ _ =
          pullback.fst Y.obj.hom g ≫ inclusion j Y.obj.hom ∧
        a ≫ e.hom = d ∧ a ≫ qB.fromNormalization = r ∧
        (e.hom ≫ pullback.fst _ _) (a (IsLocalRing.closedPoint T)) = x := by
  let : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
  let : IsDomain (Localization.Away (algebraMap R B f)) :=
    Localization.Away.isDomain (parameter_etale_algebraMap_ne_zero R B f hf)
  let j := Spec.algebraMap R (Localization.Away f)
  let jB := Spec.algebraMap B (Localization.Away (algebraMap R B f))
  let b := Spec.algebraMap R B
  let g := Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))
  let : IsDominant g := Scheme.Kummer.parameterComplementBaseChange_dominant R B f hf
  let q₀ := genericMap j Y.obj.hom
  let qB := genericMap jB ((baseChange g).obj Y).obj.hom
  dsimp only
  intro d r hd x hx
  obtain ⟨e, heB, heG, heE⟩ := exists_parameterNormalizationBaseChangeIso R B f hf Y
  let a := d ≫ e.inv
  have ha : a ≫ e.hom = d := by simp only [a, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  refine ⟨e, a, heB, heG, heE, ha, ?_, ?_⟩
  · rw [← heB, ← Category.assoc, ha]
    exact hd
  · have h := congrArg (fun k : Spec (.of T) ⟶ pullback q₀.fromNormalization b =>
      pullback.fst q₀.fromNormalization b (k (IsLocalRing.closedPoint T))) ha
    exact h.trans hx

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

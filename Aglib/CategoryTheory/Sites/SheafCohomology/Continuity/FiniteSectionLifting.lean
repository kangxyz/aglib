/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteLocalLifts
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.SectionLifting

/-! # Section lifting from finite-family Čech exactness

Only finite representable families are needed when covering sieves admit finite
refinements. The proof uses the native augmented Čech resolution and the actual
short exact sequence; it does not assume that the quotient is sectionwise epic.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Functor Opposite
open scoped Simplicial

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  (H : J.OneHypercoverFamily.{max u v}) [H.IsGenerating]
  (hfin : ∀ ⦃X : C⦄ (E : J.OneHypercover.{max u v} X), H E → Finite E.I₀)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include H hfin in
/-- Finite-family degree-one exactness suffices to lift sections of every
original short exact sequence on a finite-cover-generated site. -/
theorem sections_surjective_of_finite_family_h1
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hex : ∀ (W : C) (ι : Type (max u v)) [Finite ι] (U : ι → Over W),
      (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U) S.X₁.obj).ExactAt 1)
    (W : C) : Function.Surjective (S.g.hom.app (op W)) := by
  intro s
  let : Epi S.g := hS.epi_g
  let : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr inferInstance
  obtain ⟨ι, hι, U, hU, hlift⟩ := exists_finite_localLiftFamily J H hfin S.g.hom s
  let : Finite ι := hι
  let f := Presheaf.Cech.familyMap U
  let : Presheaf.IsLocallySurjective J f := familyMap_locallySurjective_of_covering U J hU
  let : QuasiIso (Presheaf.Cech.sheafAugmentation f J) :=
    Presheaf.Cech.sheafAugmentation_quasiIso f J
  let e := freeSheafAdjunction J
  let h := (e.homEquiv _ S.X₃).symm (representedSection s)
  let c := tupleSourceZero f ≫ familyLocalLiftSections S.g.hom s U hlift
  let b := (e.homEquiv _ S.X₂).symm c
  have hb : b ≫ S.g = (Presheaf.Cech.sheafAugmentation f J).f 0 ≫ h := by
    rw [sheafAugmentation_zero]
    apply (e.homEquiv _ S.X₃).injective
    rw [e.homEquiv_naturality_right, e.homEquiv_naturality_left]
    dsimp only [b, h]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change c ≫ whiskerRight S.g.hom (forget AddCommGrpCat) =
      tupleTargetZero f ≫ representedSection s
    dsimp only [c]
    rw [Category.assoc, familyLocalLiftSections_comp, ← Category.assoc, tupleSourceZero_comp]
  let D := ShortComplex.mk ((Presheaf.Cech.sheafComplex f J).d 1 0)
    ((Presheaf.Cech.sheafAugmentation f J).f 0)
    (augmentation_d_comp (Presheaf.Cech.sheafAugmentation f J))
  let : Epi D.g := augmentation_epi (Presheaf.Cech.sheafAugmentation f J)
  have hprim : ∀ z : D.X₁ ⟶ S.X₁,
      (Presheaf.Cech.sheafComplex f J).d 2 1 ≫ z = 0 →
      ∃ a : D.X₂ ⟶ S.X₁, D.f ≫ a = z := by
    intro z hz
    exact exists_primitive_of_adjoint_exact (sheafificationAdjunction J AddCommGrpCat)
      (Presheaf.Cech.freeComplex f) S.X₁ (hex W _ U) z hz
  obtain ⟨a, ha⟩ := exists_lift_of_degreeOne_primitive S D hS
    (augmentation_exact (Presheaf.Cech.sheafAugmentation f J))
    ((Presheaf.Cech.sheafComplex f J).d 2 1)
    ((Presheaf.Cech.sheafComplex f J).d_comp_d 2 1 0) hprim h b hb
  refine ⟨(e.homEquiv _ S.X₂ a).app (op W) ⟨𝟙 W⟩, ?_⟩
  have hh : e.homEquiv _ S.X₃ h = representedSection s := Equiv.apply_symm_apply _ _
  have H := congrArg
    (fun q => (e.homEquiv (uliftYoneda.{max u v}.obj W) S.X₃ q).app (op W) ⟨𝟙 W⟩) ha
  rw [e.homEquiv_naturality_right, hh] at H
  simpa [representedSection] using H

end CategoryTheory.Sheaf.ModuleCoefficients

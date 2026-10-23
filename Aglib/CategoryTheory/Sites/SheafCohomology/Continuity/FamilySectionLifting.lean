/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteSectionLifting

/-! # Correction of lifts on a specified covering family

This local form of the augmented-resolution argument needs one actual covering
family and its degree-one exactness. No global finite-cover generation assumption
is imposed on the site. It is suited to the qcqs objects of a larger site.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Functor Opposite
open scoped Simplicial

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Degree-one exactness corrects specified local lifts into an actual global lift. -/
theorem exists_section_lift_of_family_exact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    {W : C} (s : S.X₃.obj.obj (op W)) {ι : Type (max u v)} (U : ι → Over W)
    (hU : Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈ J W)
    (hlift : ∀ i, Presheaf.imageSieve S.g.hom s (U i).hom)
    (hex : (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U)
      S.X₁.obj).ExactAt 1) : ∃ t, S.g.hom.app (op W) t = s := by
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
      (Presheaf.Cech.freeComplex f) S.X₁ hex z hz
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

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.LocalLiftFamily
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.AdjointPrimitive
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.AugmentationExact
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.LiftCorrection
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechComparison
public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Actual section lifting from degree-one family Čech exactness -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]

/-- The actual composite free-abelian and sheafification adjunction. -/
abbrev freeSheafAdjunction :=
  (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).comp
    (sheafificationAdjunction J AddCommGrpCat.{max u v})

variable {T V : Cᵒᵖ ⥤ Type (max u v)} (f : T ⟶ V)

/-- The zero-simplex remembers its unique original source section. -/
def tupleSourceZero : Presheaf.Cech.tuplePresheaf f 0 ⟶ T where
  app _ := ↾fun a => (a.2 0).1
  naturality _ _ _ := rfl

/-- The zero-simplex augmentation retains the original target section. -/
def tupleTargetZero : Presheaf.Cech.tuplePresheaf f 0 ⟶ V where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

lemma tupleSourceZero_comp : tupleSourceZero f ≫ f = tupleTargetZero f := by
  ext X a
  exact (a.2 0).2

/-- The native augmentation in degree zero is the composite left adjoint
applied to the original map of zero-simplices. -/
lemma sheafAugmentation_zero :
    (Presheaf.Cech.sheafAugmentation f J).f 0 =
      (Presheaf.Cech.freeFunctor ⋙ presheafToSheaf J AddCommGrpCat).map
        (tupleTargetZero f) := by
  simp [Presheaf.Cech.sheafAugmentation, Presheaf.Cech.freeAugmentation,
    Presheaf.Cech.augmentedNerve, tupleTargetZero,
    AlgebraicTopology.AlternatingFaceMapComplex.ε,
    ChainComplex.toSingle₀Equiv]

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]

/-- Vanishing of degree-one cohomology for actual representable covering
families makes the original quotient map surjective on sections. -/
theorem sections_surjective_of_family_h1
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hex : ∀ (W : C) (ι : Type (max u v)) (U : ι → Over W),
      (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U) S.X₁.obj).ExactAt 1)
    (W : C) : Function.Surjective (S.g.hom.app (op W)) := by
  intro s
  let : Epi S.g := hS.epi_g
  let : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr inferInstance
  let U := localLiftFamily S.g.hom s
  let f := Presheaf.Cech.familyMap U
  let : Presheaf.IsLocallySurjective J f := localLiftFamily_locallySurjective S.g.hom s J
  let : QuasiIso (Presheaf.Cech.sheafAugmentation f J) :=
    Presheaf.Cech.sheafAugmentation_quasiIso f J
  let e := freeSheafAdjunction J
  let h := (e.homEquiv _ S.X₃).symm (representedSection s)
  let c := tupleSourceZero f ≫ localLiftSections S.g.hom s
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
    rw [Category.assoc, localLiftSections_comp, ← Category.assoc, tupleSourceZero_comp]
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

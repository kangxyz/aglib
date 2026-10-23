/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.Covers
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CoverAugmentation
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.AdjointPrimitive
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.AugmentationExact
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.LiftCorrection
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechComparison
public import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Section lifting from cofinal basis Čech exactness -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial

namespace CategoryTheory.Sheaf.BasisAcyclicity

open ModuleCoefficients

universe c h w

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max w h}]

/-- The actual free-abelian/sheafification adjunction at the specified size. -/
abbrev freeSheafAdjunction :=
  (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).comp
    (sheafificationAdjunction J AddCommGrpCat.{max w h})

variable {T V : Cᵒᵖ ⥤ Type (max w h)} (f : T ⟶ V)

/-- Projection of a zero-simplex to its source. -/
def tupleSourceZero : Presheaf.Cech.tuplePresheaf f 0 ⟶ T where
  app _ := ↾fun a => (a.2 0).1
  naturality _ _ _ := rfl

/-- Projection of a zero-simplex to its target. -/
def tupleTargetZero : Presheaf.Cech.tuplePresheaf f 0 ⟶ V where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

lemma tupleSourceZero_comp : tupleSourceZero f ≫ f = tupleTargetZero f := by
  ext X a
  exact (a.2 0).2

lemma sheafAugmentation_zero :
    (Presheaf.Cech.sheafAugmentation f J).f 0 =
      (Presheaf.Cech.freeFunctor ⋙ presheafToSheaf J AddCommGrpCat).map
        (tupleTargetZero f) := by
  simp [Presheaf.Cech.sheafAugmentation, Presheaf.Cech.freeAugmentation,
    Presheaf.Cech.augmentedNerve, tupleTargetZero,
    AlgebraicTopology.AlternatingFaceMapComplex.ε,
    ChainComplex.toSingle₀Equiv]

variable {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max w h}} (g : F ⟶ G)
  {W : C} {ι : Type w} (U : ι → Over W) (s : G.obj (op W))

/-- Restriction of the original target section along the represented base. -/
def representedSection : uliftYoneda.{w}.obj W ⟶ G ⋙ forget AddCommGrpCat where
  app X := ↾fun a => G.map a.down.op s
  naturality X Y f := by
    ext a
    change G.map (f.unop ≫ a.down).op s = G.map f (G.map a.down.op s)
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Local lifts indexed by a selected refinement, extended by restriction. -/
def familyLiftSections (hs : ∀ i, Presheaf.imageSieve g s (U i).hom) :
    Presheaf.Cech.familyPresheaf (fun i => (U i).left) ⟶ F ⋙ forget AddCommGrpCat where
  app X := ↾fun a => F.map a.2.op
    (Presheaf.localPreimage g s (U a.1).hom (hs a.1))
  naturality X Y f := by
    ext a
    change F.map (f.unop ≫ a.2).op _ = F.map f (F.map a.2.op _)
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl

lemma familyLiftSections_comp (hs : ∀ i, Presheaf.imageSieve g s (U i).hom) :
    familyLiftSections g U s hs ≫ whiskerRight g (forget AddCommGrpCat) =
      Presheaf.Cech.familyMap U ≫ representedSection s := by
  ext X a
  change g.app X (F.map a.2.op _) = G.map (a.2 ≫ (U a.1).hom).op s
  rw [NatTrans.naturality_apply, Presheaf.app_localPreimage]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

variable [J.WEqualsLocallyBijective (Type (max w h))]
  [J.PreservesSheafification AddCommGrpCat.free.{max w h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w h}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max w h})]
  [∀ W : C, HasFiniteProducts (Over W)]

/-- Čech H¹ vanishing on a cofinal supply of covers suffices for section
lifting on the basis. No vanishing is assumed for arbitrary noncovering families. -/
theorem sections_surjective_of_cech_h1 (B : CoverBasis.{c, h, w} J)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max w h})) (hS : S.ShortExact)
    (hex : ∀ (W : C) (ι : Type w) (U : ι → Over W), B.selected W ι U →
      (Presheaf.Cech.additiveHomComplex (Presheaf.Cech.familyMap U) S.X₁.obj).ExactAt 1)
    (W : C) (hW : B.objects W) : Function.Surjective (S.g.hom.app (op W)) := by
  intro s
  let : Epi S.g := hS.epi_g
  let : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr inferInstance
  obtain ⟨ι, U, hU, hs⟩ := B.cofinal W hW (Presheaf.imageSieve S.g.hom s)
    (Presheaf.imageSieve_mem J S.g.hom s)
  let f := Presheaf.Cech.familyMap U
  let : Presheaf.IsLocallySurjective J f := familyMap_locallySurjective U (B.covering hU)
  let : QuasiIso (Presheaf.Cech.sheafAugmentation f J) :=
    Presheaf.Cech.sheafAugmentation_quasiIso_of_sizes f J
  let e := freeSheafAdjunction (J := J)
  let h := (e.homEquiv _ S.X₃).symm (representedSection s)
  let c := tupleSourceZero f ≫ familyLiftSections S.g.hom U s hs
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
    rw [Category.assoc, familyLiftSections_comp, ← Category.assoc, tupleSourceZero_comp]
  let D := ShortComplex.mk ((Presheaf.Cech.sheafComplex f J).d 1 0)
    ((Presheaf.Cech.sheafAugmentation f J).f 0)
    (augmentation_d_comp (Presheaf.Cech.sheafAugmentation f J))
  let : Epi D.g := augmentation_epi (Presheaf.Cech.sheafAugmentation f J)
  have hprim : ∀ z : D.X₁ ⟶ S.X₁,
      (Presheaf.Cech.sheafComplex f J).d 2 1 ≫ z = 0 →
      ∃ a : D.X₂ ⟶ S.X₁, D.f ≫ a = z := by
    intro z hz
    exact exists_primitive_of_adjoint_exact (sheafificationAdjunction J AddCommGrpCat)
      (Presheaf.Cech.freeComplex f) S.X₁ (hex W ι U hU) z hz
  obtain ⟨a, ha⟩ := exists_lift_of_degreeOne_primitive S D hS
    (augmentation_exact (Presheaf.Cech.sheafAugmentation f J))
    ((Presheaf.Cech.sheafComplex f J).d 2 1)
    ((Presheaf.Cech.sheafComplex f J).d_comp_d 2 1 0) hprim h b hb
  refine ⟨(e.homEquiv _ S.X₂ a).app (op W) ⟨𝟙 W⟩, ?_⟩
  have hh : e.homEquiv _ S.X₃ h = representedSection s := Equiv.apply_symm_apply _ _
  have H := congrArg
    (fun q => (e.homEquiv (uliftYoneda.{w}.obj W) S.X₃ q).app (op W) ⟨𝟙 W⟩) ha
  rw [e.homEquiv_naturality_right, hh] at H
  simpa [representedSection] using H

end CategoryTheory.Sheaf.BasisAcyclicity

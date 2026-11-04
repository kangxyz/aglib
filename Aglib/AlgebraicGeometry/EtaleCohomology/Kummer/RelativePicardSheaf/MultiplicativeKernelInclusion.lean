/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.MultiplicativeInclusion
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.OriginalPresheafCoefficients

/-! # Original roots descent and actual normalized kernel inclusion -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {F : C} {H N : D} (e : L.obj F ≅ H) (q : F ⟶ R.obj H)
  (hq : adj.unit.app F ≫ R.map e.hom = q)

include hq

/-- The original sheafification unit detects whole maps after its actual comparison iso. -/
private theorem hom_ext_of_iso_unit (a b : H ⟶ N)
    (h : q ≫ R.map a = q ≫ R.map b) : a = b := by
  apply (cancel_epi e.hom).mp
  apply (adj.homEquiv F N).injective
  change adj.unit.app F ≫ R.map (e.hom ≫ a) =
    adj.unit.app F ≫ R.map (e.hom ≫ b)
  calc
    _ = q ≫ R.map a := by
      rw [Functor.map_comp, ← Category.assoc, hq]
    _ = q ≫ R.map b := h
    _ = _ := by rw [Functor.map_comp, ← Category.assoc, hq]

/-- An adjoint descent through the original comparison retains the original unit value. -/
private theorem unit_desc_through_iso (a : F ⟶ R.obj N) :
    q ≫ R.map (e.inv ≫ (adj.homEquiv F N).symm a) = a := by
  have hc : q ≫ R.map e.inv = adj.unit.app F := by
    rw [← hq, Category.assoc, ← Functor.map_comp, e.hom_inv_id, Functor.map_id]
    exact Category.comp_id _
  calc
    q ≫ R.map (e.inv ≫ (adj.homEquiv F N).symm a) =
        (q ≫ R.map e.inv) ≫ R.map ((adj.homEquiv F N).symm a) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = adj.unit.app F ≫ R.map ((adj.homEquiv F N).symm a) := by rw [hc]
    _ = a := (adj.homEquiv F N).apply_symm_apply a

end CategoryTheory.Adjunction

namespace CategoryTheory.Limits

/-- The original inverse kernel comparison retains the original kernel-lift arrow. -/
private theorem kernel_lift_inv_comparison_ι
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (R : C ⥤ D) [Functor.PreservesZeroMorphisms R]
    {A B : C} (f : A ⟶ B) [HasKernel f] [HasKernel (R.map f)]
    [IsIso (kernelComparison f R)] {P : D}
    (a : P ⟶ R.obj A) (ha : a ≫ R.map f = 0) :
    kernel.lift (R.map f) a ha ≫ inv (kernelComparison f R) ≫
      R.map (kernel.ι f) = a := by
  rw [← kernelComparison_comp_ι f R, IsIso.inv_hom_id_assoc, kernel.lift_ι]

end CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty.FullSubcategory

/-- The native full-subcategory group structure preserves literal natural-number scaling. -/
private theorem hom_nsmul {C : Type*} [Category* C] [Preadditive C]
    (P : ObjectProperty C) {X Y : P.FullSubcategory} (n : ℕ) (f : X ⟶ Y) :
    (n • f).hom = n • f.hom := rfl

end CategoryTheory.ObjectProperty.FullSubcategory

namespace CategoryTheory

universe r a b uI vI

/-- Evaluate the existing resized comparison before exposing any represented cohomology model. -/
private theorem resizeAdditiveDiagramIsoOfAddEquiv_hom_comp_apply
    {I : Type uI} [Category.{vI} I]
    {F : I ⥤ AddCommGrpCat.{a}} {G : I ⥤ AddCommGrpCat.{b}}
    [∀ i, Small.{r} (F.obj i)] [∀ i, Small.{r} (G.obj i)]
    (α : ∀ i, F.obj i ≃+ G.obj i)
    (naturality : ∀ {i j : I} (a : i ⟶ j) (x : F.obj i),
      α j (F.map a x) = G.map a (α i x))
    {H : I ⥤ AddCommGrpCat.{r}} (q : resizeAdditiveDiagram.{r} G ⟶ H)
    (i : I) (x : (resizeAdditiveDiagram.{r} F).obj i) :
    ((resizeAdditiveDiagramIsoOfAddEquiv α naturality).hom ≫ q).app i x =
      q.app i (Shrink.addEquiv.symm (α i (Shrink.addEquiv x))) := rfl

end CategoryTheory

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]

/-- The existing fibre-product unit has its literal original represented-cohomology value. -/
theorem fibreProductCohomologyToHigherDirectImage_apply_resize
    (U : S.Etale) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (c : (smallFibreProductCohomologyPresheaf.{u, w, s, e} p F q).obj (op U)) :
    (fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p F q).app (op U) c =
      (originalCohomologyToHigherDirectImage.{u, w} p F q).app (op U)
        (Shrink.addEquiv.{u + 1, w}.symm
          ((fibreProductCohomologyEquiv.{u, w, s, e} p U F q).symm
            (fibreProductResizeEquiv.{u, w, s, e} p F q U c))) := by
  have h := CategoryTheory.resizeAdditiveDiagramIsoOfAddEquiv_hom_comp_apply
    (F := Stalk.originalFibreProductCohomologyPresheaf.{u, w, s, e} p F q)
    (G := originalCohomologyPresheaf.{u, w} p F q)
    (fun V => (fibreProductCohomologyEquiv.{u, w, s, e} p V.unop F q).symm)
    (fun {V W} a x => fibreProductCohomologyRestriction_original.{u, w, s, e} p F q a.unop x)
    (originalCohomologyToHigherDirectImage.{u, w} p F q) (op U) c
  dsimp +instances only [fibreProductCohomologyToHigherDirectImage,
    smallFibreProductOriginalIso, fibreProductResizeEquiv,
    smallFibreProductCohomologyPresheaf] at h ⊢
  -- Retain the already typed original normalization proof; the native kernel checks
  -- its complete declared type, without repeating the elaborator conversion.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some decl := (← Lean.getLCtx).findFromUserName? `h
      | throwError "Missing original resized unit normalization proof"
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar decl.fvarId)

/-- Original higher-image coefficient naturality on the SAME resized chart class. -/
theorem fibreProductCohomologyToHigherDirectImage_coefficient_resize
    (U : S.Etale) {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)
    (c : (smallFibreProductCohomologyPresheaf.{u, w, s, e} p F q).obj (op U)) :
    ((higherDirectImage p q).map g).hom.app (op U)
        ((fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p F q).app (op U) c) =
      (fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p G q).app (op U)
        ((fibreProductResizeEquiv.{u, w, s, e} p G q U).symm
          (Sheaf.H.map ((inverseImage (pullback.snd U.hom p)).map g) q
            (fibreProductResizeEquiv.{u, w, s, e} p F q U c))) := by
  have h := fibreProductCohomologyToHigherDirectImage_coefficient.{u, w, s, e} p U g q
    (fibreProductResizeEquiv.{u, w, s, e} p F q U c)
  rw [fibreProductCohomologyToHigherDirectImage_apply_resize,
    fibreProductCohomologyToHigherDirectImage_apply_resize, AddEquiv.apply_symm_apply]
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology


namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.RelativePicard
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- The actual roots higher-image map retains its original presheaf kernel value. -/
theorem rootsHigherDirectImageToNormalizedPicardTorsion_unit :
    fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (mu X n) 1 ≫
      (rootsHigherDirectImageToNormalizedPicardTorsion p n hn hi o ho).hom =
        fibreProductRootsToNormalizedPicardSheafKernel p n hn hi o ho := by
  exact CategoryTheory.Adjunction.unit_desc_through_iso
    (sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (fibreProductCohomologySheafificationIso p (mu X n) 1)
    (fibreProductCohomologyToHigherDirectImage p (mu X n) 1)
    (fibreProductCohomologyToHigherDirectImage_unit p (mu X n) 1)
    (fibreProductRootsToNormalizedPicardSheafKernel p n hn hi o ho)

/-- The actual kernel comparison preserves the original normalized roots class. -/
theorem fibreProductRootsToNormalizedPicardSheafKernel_ι :
    fibreProductRootsToNormalizedPicardSheafKernel.{u, w, s, e} p n hn hi o ho ≫
      (kernel.ι (n • 𝟙 (normalizedPicardEtaleSheaf p o ho))).hom =
        fibreProductRootsNormalizedPicardNatTrans p n hn hi o ho := by
  simpa only [fibreProductRootsToNormalizedPicardSheafKernel,
    fibreProductRootsNormalizedPicardKernelMap, Category.assoc,
    ObjectProperty.ι_map, ObjectProperty.ι_obj,
    ObjectProperty.FullSubcategory.hom_nsmul, ObjectProperty.FullSubcategory.id_hom,
    normalizedPicardEtaleSheaf] using
    (kernel_lift_inv_comparison_ι
      (sheafToPresheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
      (n • 𝟙 (normalizedPicardEtaleSheaf p o ho))
      (fibreProductRootsNormalizedPicardNatTrans p n hn hi o ho)
      (fibreProductRootsNormalizedPicardNatTrans_nsmul p n hn hi o ho))

/-- The whole original roots/kernel composite has the unchanged chart unit. -/
theorem rootsHigherDirectImageToNormalizedPicardTorsion_unit_ι :
    fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (mu X n) 1 ≫
      (rootsHigherDirectImageToNormalizedPicardTorsion p n hn hi o ho ≫
        kernel.ι (n • 𝟙 (normalizedPicardEtaleSheaf p o ho))).hom =
      fibreProductRootsNormalizedPicardNatTrans p n hn hi o ho := by
  change fibreProductCohomologyToHigherDirectImage p (mu X n) 1 ≫
    (rootsHigherDirectImageToNormalizedPicardTorsion p n hn hi o ho).hom ≫
      (kernel.ι (n • 𝟙 (normalizedPicardEtaleSheaf p o ho))).hom = _
  rw [← Category.assoc, rootsHigherDirectImageToNormalizedPicardTorsion_unit,
    fibreProductRootsToNormalizedPicardSheafKernel_ι]

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

namespace AddCommGrpCat

universe v

/-- Compose three actual comparison values while their original group objects stay fixed. -/
private theorem eq_of_three_comparisons {A B C : AddCommGrpCat.{v}}
    (f : A ⟶ C) (g : B ⟶ C) {a a' : A} {b b' : B}
    (h₁ : a = a') (h₂ : f a' = g b) (h₃ : b = b') : f a = g b' :=
  (congrArg f h₁).trans (h₂.trans (congrArg g h₃))

end AddCommGrpCat

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

open Scheme.RelativePicard Scheme.EtaleCohomology.Kummer
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- Original roots inclusion and the Gm comparison retain the same chart unit. -/
theorem gmHigherDirectImageNormalizedPicardIso_inclusion_unit :
    fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (mu X n) 1 ≫
      ((higherDirectImage p 1).map (inclusion X n) ≫
        (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom).hom =
      fibreProductRootsNormalizedPicardNatTrans p n hn hi o ho := by
  apply NatTrans.ext
  funext U
  obtain ⟨U, rfl⟩ := Opposite.op_surjective U
  apply AddCommGrpCat.hom_ext
  ext c
  let d : (smallFibreProductCohomologyPresheaf.{u, w, s, e} p (gm X) 1).obj (op U) :=
    (fibreProductResizeEquiv.{u, w, s, e} p (gm X) 1 U).symm
      (Sheaf.H.map ((inverseImage (pullback.snd U.hom p)).map (inclusion X n)) 1
        (fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U c))
  have hc := fibreProductCohomologyToHigherDirectImage_coefficient_resize.{u, w, s, e}
    p U (inclusion X n) 1 c
  change ((higherDirectImage p 1).map (inclusion X n)).hom.app (op U)
      ((fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (mu X n) 1).app (op U) c) =
    (fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (gm X) 1).app (op U) d at hc
  have hg := ConcreteCategory.congr_hom
    (NatTrans.congr_app (gmHigherDirectImageNormalizedPicardIso_unit.{u, w, s, e} p o ho) (op U)) d
  have hp : (fibreProductGmPicardNatTrans.{u, w, s, e} p).app (op U) d =
      (fibreProductRootsPicardNatTrans.{u, w, s, e} p n hn hi).app (op U) c := by
    change fibreProductGmPicardEquiv p U
        (fibreProductResizeEquiv.{u, w, s, e} p (gm X) 1 U d) =
      fibreProductRootsPicardMap p n hn hi U
        (fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U c)
    exact (congrArg (fibreProductGmPicardEquiv p U)
      ((fibreProductResizeEquiv.{u, w, s, e} p (gm X) 1 U).apply_symm_apply _)).trans
        (fibreProductGmPicardEquiv_inclusion p U n hn hi
          (fibreProductResizeEquiv.{u, w, s, e} p (mu X n) 1 U c))
  change (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom.hom.app (op U)
      ((fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (gm X) 1).app (op U) d) =
    (etaleFamilyNormalization p o ho).app (op U)
      ((fibreProductGmPicardNatTrans.{u, w, s, e} p).app (op U) d) at hg
  have hfull := AddCommGrpCat.eq_of_three_comparisons
    ((gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom.hom.app (op U))
    ((etaleFamilyNormalization p o ho).app (op U))
    (a := ((higherDirectImage p 1).map (inclusion X n)).hom.app (op U)
      ((fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (mu X n) 1).app (op U) c))
    (a' := (fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (gm X) 1).app (op U) d)
    (b := (fibreProductGmPicardNatTrans.{u, w, s, e} p).app (op U) d)
    (b' := (fibreProductRootsPicardNatTrans.{u, w, s, e} p n hn hi).app (op U) c)
    hc hg hp
  change (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom.hom.app (op U)
      (((higherDirectImage p 1).map (inclusion X n)).hom.app (op U)
        ((fibreProductCohomologyToHigherDirectImage.{u, w, s, e} p (mu X n) 1).app (op U) c)) =
    (etaleFamilyNormalization p o ho).app (op U)
      ((fibreProductRootsPicardNatTrans.{u, w, s, e} p n hn hi).app (op U) c)
  exact hfull

/-- The original higher-image inclusion is the original normalized kernel inclusion. -/
theorem gmHigherDirectImageNormalizedPicardIso_inclusion :
    (higherDirectImage p 1).map (inclusion X n) ≫
        (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom =
      rootsHigherDirectImageToNormalizedPicardTorsion p n hn hi o ho ≫
        kernel.ι (n • 𝟙 (normalizedPicardEtaleSheaf p o ho)) := by
  apply CategoryTheory.Adjunction.hom_ext_of_iso_unit
    (sheafificationAdjunction (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1})
    (fibreProductCohomologySheafificationIso p (mu X n) 1)
    (fibreProductCohomologyToHigherDirectImage p (mu X n) 1)
    (fibreProductCohomologyToHigherDirectImage_unit p (mu X n) 1)
  exact (gmHigherDirectImageNormalizedPicardIso_inclusion_unit p n hn hi o ho).trans
    (rootsHigherDirectImageToNormalizedPicardTorsion_unit_ι p n hn hi o ho).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard

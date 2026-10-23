/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StageSupport.FiniteFamilies
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsProducts
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SupportedFamilyAcyclic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Actual stage models of original finite tuple products

Base change preserves finite limits in the original small étale categories.
Its functor on slices, followed by the target model's isomorphism, therefore
preserves the literal finite products used by the supported-family interface.
The comparisons below retain every projection and the original map to the target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

namespace StageSupport

variable {I : Type u} [Category.{u} I]
  {X : I ⥤ Scheme.{u}ᵒᵖ} {c : Cocone X} {i : I}
  {W : c.pt.unop.Etale} {J : Type v} {U : J → Over W}
  (M : FamilyModel (X := X) (c := c) i U)

/-- Actual site base change on the original slices, with the specified target
isomorphism. No replacement site or replacement product is introduced. -/
def FamilyModel.sliceFunctor : Over M.target.obj ⥤ Over W :=
  Over.post (siteBaseChange (c.ι.app i).unop) ⋙ Over.map M.target.iso.hom

instance FamilyModel.sliceFunctor_preservesFiniteLimits :
    PreservesFiniteLimits M.sliceFunctor := by
  dsimp only [FamilyModel.sliceFunctor]
  infer_instance

/-- Each source comparison is an isomorphism over the original target. -/
def FamilyModel.familyIso (j : J) : M.sliceFunctor.obj (M.family j) ≅ U j :=
  Over.isoMk (M.source j).iso (M.comm j).symm

/-- The canonical product comparison in the original slice. It applies to
all finite tuple lengths, including zero, and uses the same common stage. -/
def FamilyModel.productIso {K : Type w} [Finite K] (a : K → J) :
    M.sliceFunctor.obj (∏ᶜ fun k => M.family (a k)) ≅ ∏ᶜ fun k => U (a k) :=
  PreservesProduct.iso M.sliceFunctor (fun k => M.family (a k)) ≪≫
    Pi.mapIso (fun k => M.familyIso (a k))

/-- The product comparison retains the literal projections in the slice. -/
@[reassoc]
theorem FamilyModel.productIso_hom_π {K : Type w} [Finite K] (a : K → J) (k : K) :
    (M.productIso a).hom ≫ Pi.π (fun k => U (a k)) k =
      M.sliceFunctor.map (Pi.π (fun k => M.family (a k)) k) ≫
        (M.familyIso (a k)).hom := by
  simp only [FamilyModel.productIso, Iso.trans_hom, Category.assoc,
    Pi.mapIso_hom_π, PreservesProduct.iso_hom, piComparison_comp_π_assoc]

/-- The product comparison as an actual small-site isomorphism. -/
def FamilyModel.tupleIso {K : Type w} [Finite K] (a : K → J) :
    (siteBaseChange (c.ι.app i).unop).obj (∏ᶜ fun k => M.family (a k)).left ≅
      (∏ᶜ fun k => U (a k)).left :=
  (Over.forget W).mapIso (M.productIso a)

/-- Every actual tuple projection commutes with the stage comparison. -/
@[reassoc]
theorem FamilyModel.tupleIso_hom_π {K : Type w} [Finite K] (a : K → J) (k : K) :
    (M.tupleIso a).hom ≫ (Pi.π (fun k => U (a k)) k).left =
      (siteBaseChange (c.ι.app i).unop).map
        (Pi.π (fun k => M.family (a k)) k).left ≫ (M.source (a k)).iso.hom := by
  exact congrArg (fun f => f.left) (M.productIso_hom_π a k)

/-- The tuple isomorphism is over the original target with its specified
model isomorphism, not merely an isomorphism of underlying schemes. -/
@[reassoc]
theorem FamilyModel.tupleIso_hom_hom {K : Type w} [Finite K] (a : K → J) :
    (M.tupleIso a).hom ≫ (∏ᶜ fun k => U (a k)).hom =
      (siteBaseChange (c.ι.app i).unop).map (∏ᶜ fun k => M.family (a k)).hom ≫
        M.target.iso.hom :=
  Over.w (M.productIso a).hom

/-- A qcqs model of each original finite tuple, obtained from the actual
finite product of the descended family at its common stage. -/
def FamilyModel.tupleModel {K : Type w} [Finite K] (a : K → J) :
    Model X c i (∏ᶜ fun k => U (a k)).left where
  obj := (∏ᶜ fun k => M.family (a k)).left
  compactSpace := (qcqs_product M.target.obj
    ⟨M.target.compactSpace, M.target.quasiSeparatedSpace⟩
    (fun k => M.family (a k))
    (fun k => ⟨(M.source (a k)).compactSpace, (M.source (a k)).quasiSeparatedSpace⟩)).1
  quasiSeparatedSpace := (qcqs_product M.target.obj
    ⟨M.target.compactSpace, M.target.quasiSeparatedSpace⟩
    (fun k => M.family (a k))
    (fun k => ⟨(M.source (a k)).compactSpace, (M.source (a k)).quasiSeparatedSpace⟩)).2
  iso := M.tupleIso a

end StageSupport

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]

include hc

/-- Native finite products of arbitrary supported families remain supported,
including noncovering families and the empty product. -/
theorem stageDescendedQcqsObjects_product {W : c.pt.unop.Etale}
    (hW : stageDescendedQcqsObjects X c W) {J : Type v} [Finite J]
    (U : J → Over W) (hU : ∀ j, stageDescendedQcqsObjects X c (U j).left) :
    stageDescendedQcqsObjects X c (∏ᶜ U).left := by
  obtain ⟨i, ⟨M⟩⟩ := StageSupport.exists_familyModel hc hW U hU
  exact ⟨i, ⟨M.tupleModel id⟩⟩

/-- The exact all-finite-family tuple condition used by the original
supported Čech-acyclicity theorem, with no covering hypothesis added. -/
theorem stageDescendedQcqsObjects_tupleProducts :
    CategoryTheory.Sheaf.ModuleCoefficients.SupportedTupleProducts
      (stageDescendedQcqsObjects X c) := by
  intro W hW J _ U hU n a
  exact stageDescendedQcqsObjects_product X c hc hW (fun k => U (a k))
    (fun k => hU (a k))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

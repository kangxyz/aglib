/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The original section basis of a finite free module sheaf

Evaluation preserves the original finite coproduct defining a free module
sheaf. Its native coproduct/direct-sum comparison gives the finite free
section module, with every basis vector equal to the original `freeSection`.
The basis respects every original restriction map. The ringed site is
arbitrary and the coefficient rings need not be commutative.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

local instance freeSectionsEvaluationAdditive (X : Cᵒᵖ) : (evaluation R X).Additive where
  map_add := by intros; rfl

/-- Actual sections of the original finite free sheaf are the original finite free module. -/
def freeSectionsIso (I : Type u) [Finite I] (X : Cᵒᵖ) :
    (evaluation R X).obj (free (R := R) I) ≅
      ModuleCat.of (R.obj.obj X) (I →₀ R.obj.obj X) := by
  classical
  exact PreservesCoproduct.iso (evaluation R X) (fun _ : I => unit R) ≪≫
    ModuleCat.coprodIsoDirectSum (fun _ : I => ModuleCat.of (R.obj.obj X) (R.obj.obj X)) ≪≫
      (finsuppLEquivDirectSum (R.obj.obj X) (R.obj.obj X) I).symm.toModuleIso

/-- The original free inclusion has exactly the original singleton coordinate map. -/
@[reassoc]
theorem freeSectionsIso_ι (I : Type u) [Finite I] (X : Cᵒᵖ) (i : I) :
    (ιFree (R := R) i).val.app X ≫ (freeSectionsIso R I X).hom =
      ModuleCat.ofHom (Finsupp.lsingle i) := by
  classical
  have H : (evaluation R X).map (ιFree (R := R) i) ≫
        (PreservesCoproduct.iso (evaluation R X) (fun _ : I => unit R)).hom =
      Sigma.ι (fun _ : I => (evaluation R X).obj (unit R)) i := by
    apply (Iso.eq_comp_inv _).mp
    simp only [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ιFree]
  change (evaluation R X).map (ιFree i) ≫ _ = _
  dsimp only [freeSectionsIso, Iso.trans_hom]
  rw [← Category.assoc, H, ← Category.assoc]
  change (Sigma.ι (fun _ : I => ModuleCat.of (R.obj.obj X) (R.obj.obj X)) i ≫ _) ≫ _ = _
  rw [ModuleCat.ι_coprodIsoDirectSum_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact finsuppLEquivDirectSum_symm_lof (R.obj.obj X) (R.obj.obj X) I i r

/-- The original global free generator evaluates to the original singleton coefficient. -/
@[simp]
theorem freeSectionsIso_freeSection (I : Type u) [Finite I] (X : Cᵒᵖ) (i : I) :
    (freeSectionsIso R I X).hom ((freeSection (R := R) i).val X) = Finsupp.single i 1 :=
  ConcreteCategory.congr_hom (freeSectionsIso_ι R I X i) (1 : R.obj.obj X)

/-- The actual native basis of the section module of the original finite free sheaf. -/
def freeSectionsBasis (I : Type u) [Finite I] (X : Cᵒᵖ) :
    Module.Basis I (R.obj.obj X) ((free (R := R) I).val.obj X) :=
  Finsupp.basisSingleOne.map (freeSectionsIso R I X).toLinearEquiv.symm

/-- Its basis vectors are exactly the original free sections at the displayed object. -/
@[simp]
theorem freeSectionsBasis_apply (I : Type u) [Finite I] (X : Cᵒᵖ) (i : I) :
    freeSectionsBasis R I X i = (freeSection (R := R) i).val X := by
  apply (freeSectionsIso R I X).toLinearEquiv.injective
  change (freeSectionsIso R I X).toLinearEquiv
      ((freeSectionsIso R I X).toLinearEquiv.symm (Finsupp.single i 1)) = _
  exact ((freeSectionsIso R I X).toLinearEquiv.apply_symm_apply _).trans
    (freeSectionsIso_freeSection R I X i).symm

/-- Every original restriction carries the original section basis to the same section basis. -/
theorem freeSectionsBasis_restrict (I : Type u) [Finite I]
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : I) :
    (free (R := R) I).val.map f (freeSectionsBasis R I X i) = freeSectionsBasis R I Y i := by
  rw [freeSectionsBasis_apply, freeSectionsBasis_apply]
  exact PresheafOfModules.sections_property (freeSection (R := R) i) f

end SheafOfModules

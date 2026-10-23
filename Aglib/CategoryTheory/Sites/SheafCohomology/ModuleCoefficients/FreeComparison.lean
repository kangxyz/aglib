/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Free
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Free module and free abelian cochains

The adjunction comparison remembers the additive structure and precomposition.
It is used to identify module-linear Cech cochains with their original additive
cochains, rather than declaring a new cohomology theory.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace PresheafOfModules

universe r c h m

variable {C : Type c} [Category.{h} C] (R : Cᵒᵖ ⥤ RingCat.{r})
    (F : Cᵒᵖ ⥤ Type (max r m)) (I : PresheafOfModules.{max r m} R)

/-- The comparison of free module and free abelian Hom sets. -/
def freeAbelianHomEquiv :
    ((freeWide.{r, m, c, h} R).obj F ⟶ I) ≃ (F ⋙ AddCommGrpCat.free ⟶ I.presheaf) :=
  ((freeWideAdjunction.{r, m, c, h} R).homEquiv F I).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv F I.presheaf).symm)

/-- The original comparison agrees on each free generator. -/
lemma freeAbelianHomEquiv_apply_of (a : (freeWide.{r, m, c, h} R).obj F ⟶ I)
    (U : Cᵒᵖ) (x : F.obj U) :
    (freeAbelianHomEquiv.{r, c, h, m} R F I a).app U (FreeAbelianGroup.of x) =
      a.app U (Finsupp.single x 1) := by
  have h := congrArg (fun t : F ⟶ I.presheaf ⋙ forget AddCommGrpCat => t.app U x)
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv F I.presheaf).apply_symm_apply
      ((freeWideAdjunction.{r, m, c, h} R).homEquiv F I a))
  exact h

/-- Additivity of the original free adjunction comparison. -/
def freeAbelianHomAddEquiv :
    ((freeWide.{r, m, c, h} R).obj F ⟶ I) ≃+ (F ⋙ AddCommGrpCat.free ⟶ I.presheaf) where
  toEquiv := freeAbelianHomEquiv.{r, c, h, m} R F I
  map_add' a b := by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    change (freeAbelianHomEquiv.{r, c, h, m} R F I (a + b)).app U (FreeAbelianGroup.of x) =
      (freeAbelianHomEquiv.{r, c, h, m} R F I a).app U (FreeAbelianGroup.of x) +
        (freeAbelianHomEquiv.{r, c, h, m} R F I b).app U (FreeAbelianGroup.of x)
    simp only [freeAbelianHomEquiv_apply_of]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The comparison commutes with precomposition by maps of generators. -/
lemma freeAbelianHomEquiv_naturality {F' : Cᵒᵖ ⥤ Type (max r m)}
    (f : F' ⟶ F) (a : (freeWide.{r, m, c, h} R).obj F ⟶ I) :
    freeAbelianHomEquiv.{r, c, h, m} R F' I ((freeWide.{r, m, c, h} R).map f ≫ a) =
      Functor.whiskerRight f AddCommGrpCat.free ≫ freeAbelianHomEquiv.{r, c, h, m} R F I a := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  change (freeAbelianHomEquiv.{r, c, h, m} R F' I ((freeWide.{r, m, c, h} R).map f ≫ a)).app U
    (FreeAbelianGroup.of x) =
      (freeAbelianHomEquiv.{r, c, h, m} R F I a).app U (FreeAbelianGroup.of (f.app U x))
  simp only [freeAbelianHomEquiv_apply_of]
  change a.app U (ModuleCat.freeWideDesc (R := R.obj U)
    (M := ModuleCat.freeWide (R.obj U) (F.obj U))
    (fun x ↦ Finsupp.single (f.app U x) 1) (Finsupp.single x 1)) = _
  rw [ModuleCat.freeWideDesc_single]

end PresheafOfModules

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Coordinates

/-!
# The differential in one-element tensor coordinates

The old-complex column carries the old differential; the new column contributes
scalar multiplication horizontally and the negative old differential vertically.
These identities hold for every nonnegative complex of modules.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] (a : R) (K : ChainComplex (ModuleCat.{u} R) ℕ)

@[reassoc]
theorem singleTensor_ι_d (i j n m : ℕ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj (singleComplex R a) K i j n h ≫
      (HomologicalComplex.tensorObj (singleComplex R a) K).d n m =
    HomologicalComplex.mapBifunctor.d₁ (singleComplex R a) K
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i j m +
      HomologicalComplex.mapBifunctor.d₂ (singleComplex R a) K
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i j m := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]

@[reassoc]
theorem singleTensor_ι_zero_d (n : ℕ) :
    HomologicalComplex.ιTensorObj (singleComplex R a) K 0 (n + 1) (n + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n =
    ((ModuleCat.of R R) ◁ K.d (n + 1) n) ≫
      HomologicalComplex.ιTensorObj (singleComplex R a) K 0 n n (by omega) := by
  rw [singleTensor_ι_d,
    HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp), zero_add,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0 (show
      (ComplexShape.down ℕ).Rel (n + 1) n from rfl) n (by simp)]
  exact one_smul ℤˣ _

@[reassoc]
theorem singleTensor_ι_one_d (n : ℕ) :
    HomologicalComplex.ιTensorObj (singleComplex R a) K 1 (n + 1) (n + 2) (by omega) ≫
      (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 2) (n + 1) =
    (ModuleCat.ofHom (LinearMap.lsmul R R a) ▷ K.X (n + 1)) ≫
        HomologicalComplex.ιTensorObj (singleComplex R a) K 0 (n + 1) (n + 1) (by omega) -
      ((ModuleCat.of R R) ◁ K.d (n + 1) n) ≫
        HomologicalComplex.ιTensorObj (singleComplex R a) K 1 n (n + 1) (by omega) := by
  rw [singleTensor_ι_d,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (n + 1) (n + 1) (by simp),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 1
      (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) (n + 1) (by simp [Nat.add_comm])]
  change (1 : ℤˣ) • _ + (-1 : ℤˣ) • _ = _
  simp only [one_smul, Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul,
    sub_eq_add_neg]
  rfl

@[reassoc]
theorem singleTensor_ι_one_zero_d :
    HomologicalComplex.ιTensorObj (singleComplex R a) K 1 0 1 rfl ≫
      (HomologicalComplex.tensorObj (singleComplex R a) K).d 1 0 =
    (ModuleCat.ofHom (LinearMap.lsmul R R a) ▷ K.X 0) ≫
      HomologicalComplex.ιTensorObj (singleComplex R a) K 0 0 0 rfl := by
  rw [singleTensor_ι_d,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl) 0 0 rfl,
    HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp), add_zero]
  exact one_smul ℤˣ _

set_option backward.isDefEq.respectTransparency false in
/-- Moving scalar multiplication through the left unit identifies its tensor action. -/
@[reassoc]
theorem singleTensor_scalar_unitor (X : ModuleCat.{u} R) :
    (λ_ X).inv ≫ (ModuleCat.ofHom (LinearMap.lsmul R R a) ▷ X) =
      ModuleCat.ofHom (LinearMap.lsmul R X a) ≫ (λ_ X).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change TensorProduct.tmul R (a * 1) x = TensorProduct.tmul R 1 (a • x)
  exact TensorProduct.smul_tmul a (1 : R) x

set_option backward.isDefEq.respectTransparency false in
/-- The old-complex column has the original differential. -/
@[reassoc]
theorem singleTensorιZero_d (n : ℕ) :
    singleTensorιZero a K (n + 1) ≫
      (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n =
      K.d (n + 1) n ≫ singleTensorιZero a K n := by
  unfold singleTensorιZero
  erw [Category.assoc, singleTensor_ι_zero_d, ← Category.assoc,
    ← leftUnitor_inv_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- The shifted column has scalar multiplication minus the old differential. -/
@[reassoc]
theorem singleTensorιOne_d (n : ℕ) :
    singleTensorιOne a K (n + 1) ≫
      (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 2) (n + 1) =
      ModuleCat.ofHom (LinearMap.lsmul R (K.X (n + 1)) a) ≫
          singleTensorιZero a K (n + 1) -
        K.d (n + 1) n ≫ singleTensorιOne a K n := by
  simp only [singleTensorιOne, singleTensorιZero, Category.assoc, singleTensor_ι_one_d,
    Preadditive.comp_sub]
  erw [← Category.assoc, singleTensor_scalar_unitor, Category.assoc,
    ← Category.assoc ((λ_ (K.X (n + 1))).inv), ← leftUnitor_inv_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- In degree one the shifted column contributes scalar multiplication alone. -/
@[reassoc]
theorem singleTensorιOne_zero_d :
    singleTensorιOne a K 0 ≫
      (HomologicalComplex.tensorObj (singleComplex R a) K).d 1 0 =
      ModuleCat.ofHom (LinearMap.lsmul R (K.X 0) a) ≫ singleTensorιZero a K 0 := by
  unfold singleTensorιOne singleTensorιZero
  erw [Category.assoc, singleTensor_ι_one_zero_d, ← Category.assoc,
    singleTensor_scalar_unitor, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
/-- The old-column component of the total differential. -/
@[reassoc]
theorem singleTensor_d_πZero (n : ℕ) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n ≫
        singleTensorπZero a K n =
      singleTensorπZero a K (n + 1) ≫ K.d (n + 1) n +
        singleTensorπOne a K n ≫ ModuleCat.ofHom (LinearMap.lsmul R (K.X n) a) := by
  apply singleTensor_hom_ext a K n
  · simp only [← Category.assoc, singleTensorιZero_d, Preadditive.comp_add]
    simp [Category.assoc]
  · cases n with
    | zero =>
      erw [singleTensorιOne_zero_d_assoc]
      simp [Preadditive.comp_add]
    | succ n =>
      simp only [← Category.assoc, singleTensorιOne_d, Preadditive.comp_add, Preadditive.sub_comp]
      simp [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The shifted-column component of the total differential carries a minus sign. -/
@[reassoc]
theorem singleTensor_d_πOne (n : ℕ) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 2) (n + 1) ≫
        singleTensorπOne a K n =
      -(singleTensorπOne a K (n + 1) ≫ K.d (n + 1) n) := by
  apply singleTensor_hom_ext a K (n + 1)
  · simp only [← Category.assoc, singleTensorιZero_d]
    simp [Category.assoc]
  · simp only [← Category.assoc, singleTensorιOne_d, Preadditive.sub_comp]
    simp [Category.assoc]

end ChainComplex.Koszul

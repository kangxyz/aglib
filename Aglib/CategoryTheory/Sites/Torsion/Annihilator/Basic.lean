/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian

/-! # Native annihilator subsheaves

The annihilator of a natural number is the actual categorical kernel of
multiplication by that number. Divisibility and coefficient maps act through
the native kernel universal property and retain its original inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- The native kernel subsheaf of sections annihilated by `n`. -/
abbrev annihilator (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{w} :=
  kernel (n • 𝟙 F)

/-- The original native kernel inclusion of the annihilator subsheaf. -/
abbrev annihilatorι (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) : annihilator F n ⟶ F :=
  kernel.ι (n • 𝟙 F)

/-- The original inclusion is a monomorphism. -/
instance annihilatorι_mono (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    Mono (annihilatorι F n) := inferInstanceAs (Mono (kernel.ι (n • 𝟙 F)))

/-- The original inclusion is killed by multiplication by `n`. -/
@[reassoc]
theorem annihilatorι_comp_nsmul (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    annihilatorι F n ≫ (n • 𝟙 F) = 0 := kernel.condition _

/-- The inclusion itself is annihilated by `n`. -/
@[simp]
theorem nsmul_annihilatorι (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    n • annihilatorι F n = 0 := by
  simpa only [Preadditive.comp_nsmul, Category.comp_id] using
    annihilatorι_comp_nsmul F n

/-- Multiplication by `n` is zero on its native annihilator subsheaf. -/
@[simp]
theorem nsmul_id_annihilator (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    n • 𝟙 (annihilator F n) = 0 := by
  apply (cancel_mono (annihilatorι F n)).1
  simp only [Preadditive.nsmul_comp, Category.id_comp, nsmul_annihilatorι,
    zero_comp]

/-- Divisibility gives the canonical native kernel lift between annihilator subsheaves. -/
def annihilatorMap (F : Sheaf J AddCommGrpCat.{w}) {n m : ℕ} (h : n ∣ m) :
    annihilator F n ⟶ annihilator F m :=
  kernel.lift (m • 𝟙 F) (annihilatorι F n) (by
    rw [Preadditive.comp_nsmul, Category.comp_id]
    obtain ⟨k, rfl⟩ := h
    rw [Nat.mul_comm n k, mul_smul, nsmul_annihilatorι, nsmul_zero])

/-- The divisibility map factors the literal original inclusion. -/
@[reassoc (attr := simp)]
theorem annihilatorMap_ι (F : Sheaf J AddCommGrpCat.{w}) {n m : ℕ} (h : n ∣ m) :
    annihilatorMap F h ≫ annihilatorι F m = annihilatorι F n :=
  kernel.lift_ι _ _ _

/-- Divisibility maps are monomorphisms because their composites are original inclusions. -/
instance annihilatorMap_mono (F : Sheaf J AddCommGrpCat.{w}) {n m : ℕ} (h : n ∣ m) :
    Mono (annihilatorMap F h) := by
  dsimp [annihilatorMap]
  infer_instance

/-- The map for reflexive divisibility is the identity. -/
@[simp]
theorem annihilatorMap_refl (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    annihilatorMap F (dvd_refl n) = 𝟙 _ := by
  apply (cancel_mono (annihilatorι F n)).1
  simp only [annihilatorMap_ι, Category.id_comp]

/-- The native kernel lifts preserve composition of divisibility relations. -/
@[reassoc (attr := simp)]
theorem annihilatorMap_comp (F : Sheaf J AddCommGrpCat.{w}) {n m k : ℕ}
    (h : n ∣ m) (h' : m ∣ k) :
    annihilatorMap F h ≫ annihilatorMap F h' = annihilatorMap F (dvd_trans h h') := by
  apply (cancel_mono (annihilatorι F k)).1
  simp only [Category.assoc, annihilatorMap_ι]

/-- Every coefficient map induces its canonical map on the native annihilator subsheaves. -/
def annihilatorCoefficientMap {F G : Sheaf J AddCommGrpCat.{w}} (q : F ⟶ G) (n : ℕ) :
    annihilator F n ⟶ annihilator G n :=
  kernel.lift (n • 𝟙 G) (annihilatorι F n ≫ q) (by
    rw [Preadditive.comp_nsmul, Category.comp_id, ← Preadditive.nsmul_comp,
      nsmul_annihilatorι, zero_comp])

/-- The coefficient-induced map retains the actual original coefficient map and inclusions. -/
@[reassoc (attr := simp)]
theorem annihilatorCoefficientMap_ι {F G : Sheaf J AddCommGrpCat.{w}}
    (q : F ⟶ G) (n : ℕ) :
    annihilatorCoefficientMap q n ≫ annihilatorι G n = annihilatorι F n ≫ q :=
  kernel.lift_ι _ _ _

/-- Annihilator coefficient maps preserve identities. -/
@[simp]
theorem annihilatorCoefficientMap_id (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    annihilatorCoefficientMap (𝟙 F) n = 𝟙 _ := by
  apply (cancel_mono (annihilatorι F n)).1
  simp only [annihilatorCoefficientMap_ι, Category.comp_id, Category.id_comp]

/-- Annihilator coefficient maps preserve the original coefficient composition. -/
@[simp, reassoc]
theorem annihilatorCoefficientMap_comp {F G H : Sheaf J AddCommGrpCat.{w}}
    (q : F ⟶ G) (r : G ⟶ H) (n : ℕ) :
    annihilatorCoefficientMap (q ≫ r) n =
      annihilatorCoefficientMap q n ≫ annihilatorCoefficientMap r n := by
  apply (cancel_mono (annihilatorι H n)).1
  simp only [Category.assoc, annihilatorCoefficientMap_ι,
    annihilatorCoefficientMap_ι_assoc]

/-- Divisibility maps are natural for every actual additive coefficient map. -/
@[reassoc]
theorem annihilatorMap_coefficient_naturality {F G : Sheaf J AddCommGrpCat.{w}}
    (q : F ⟶ G) {n m : ℕ} (h : n ∣ m) :
    annihilatorMap F h ≫ annihilatorCoefficientMap q m =
      annihilatorCoefficientMap q n ≫ annihilatorMap G h := by
  apply (cancel_mono (annihilatorι G m)).1
  simp only [Category.assoc, annihilatorCoefficientMap_ι,
    annihilatorMap_ι, annihilatorMap_ι_assoc]

end CategoryTheory.Sheaf

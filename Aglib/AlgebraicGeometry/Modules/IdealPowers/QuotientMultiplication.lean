/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Multiplication
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Functor

/-!
# Original scalar maps between different ideal quotients

A scalar carrying `J` into `K` induces multiplication from `F/JF` to `F/KF`.
The construction uses the actual ideal-image square and its native cokernel
map, retaining the quotient-arrow equation, multiplication and addition laws.
No flatness or coherence is required. These maps allow graded actions to be
constructed from finite levels of a formal system without algebraizing it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (α : A →+* Γ(X, ⊤)) (F : X.Modules)

/-- Multiplication by a scalar between the actual quotients by two ideals. -/
def idealQuotientMul {J K : Ideal A} (a : A) (ha : ∀ b ∈ J, a * b ∈ K) :
    idealQuotient X α F J ⟶ idealQuotient X α F K :=
  cokernel.map (idealMultipleι X α F J) (idealMultipleι X α F K)
    (idealMultipleMul X α F a ha) (globalScalarEndomorphism X F (α a))
    (idealMultipleMul_ι X α F a ha).symm

/-- The induced map is the original scalar map after the original quotient arrow. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_mul {J K : Ideal A} (a : A) (ha : ∀ b ∈ J, a * b ∈ K) :
    idealQuotientπ X α F J ≫ idealQuotientMul X α F a ha =
      globalScalarEndomorphism X F (α a) ≫ idealQuotientπ X α F K :=
  cokernel.π_desc _ _ _

/-- Composition retains the product of the original scalars. -/
theorem idealQuotientMul_comp {J K L : Ideal A} (a b : A)
    (ha : ∀ x ∈ J, a * x ∈ K) (hb : ∀ x ∈ K, b * x ∈ L) :
    idealQuotientMul X α F a ha ≫ idealQuotientMul X α F b hb =
      idealQuotientMul X α F (b * a)
        (fun x hx => by rw [mul_assoc]; exact hb _ (ha x hx)) := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp only [idealQuotientπ_mul_assoc, idealQuotientπ_mul]
  simp only [globalScalarEndomorphism, map_mul, CatCenter.mul_app', Category.assoc]

/-- The unit scalar gives the identity on the original quotient. -/
@[simp]
theorem idealQuotientMul_one (J : Ideal A) :
    idealQuotientMul X α F 1 (fun x hx => by simpa using hx : ∀ x ∈ J, 1 * x ∈ J) =
      𝟙 (idealQuotient X α F J) := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp [globalScalarEndomorphism]

/-- The zero scalar gives zero, for arbitrary source and target ideals. -/
@[simp]
theorem idealQuotientMul_zero (J K : Ideal A) :
    idealQuotientMul X α F 0 (fun x _ => by simp : ∀ x ∈ J, 0 * x ∈ K) = 0 := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp [globalScalarEndomorphism]

/-- Addition is computed on the original scalar multiplication maps. -/
theorem idealQuotientMul_add {J K : Ideal A} (a b : A)
    (ha : ∀ x ∈ J, a * x ∈ K) (hb : ∀ x ∈ J, b * x ∈ K) :
    idealQuotientMul X α F (a + b)
        (fun x hx => by rw [add_mul]; exact K.add_mem (ha x hx) (hb x hx)) =
      idealQuotientMul X α F a ha + idealQuotientMul X α F b hb := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp only [Preadditive.comp_add, idealQuotientπ_mul]
  simp only [globalScalarEndomorphism, map_add, CatCenter.app_add, Preadditive.add_comp]

/-- Scalar-induced quotient maps commute with every original coefficient morphism. -/
@[reassoc]
theorem idealQuotientMul_naturality {G : X.Modules} (f : F ⟶ G)
    {J K : Ideal A} (a : A) (ha : ∀ b ∈ J, a * b ∈ K) :
    idealQuotientHom X α J f ≫ idealQuotientMul X α G a ha =
      idealQuotientMul X α F a ha ≫ idealQuotientHom X α K f := by
  apply (cancel_epi (idealQuotientπ X α F J)).mp
  simp only [idealQuotientπ_hom_assoc, idealQuotientπ_mul_assoc,
    idealQuotientπ_mul, idealQuotientπ_hom]
  have hn : f ≫ globalScalarEndomorphism X G (α a) =
      globalScalarEndomorphism X F (α a) ≫ f :=
    (globalScalarCenter X (α a)).naturality f
  rw [← Category.assoc, hn, Category.assoc]

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Basic

/-!
# The signed two-column differential of a finite Koszul complex

On the degree-zero column of the new multiplication factor, the differential
is the old Koszul differential. On its degree-one column it is multiplication
by the new scalar minus the old differential. Thus the recursive total complex
has the usual Koszul sign, checked against the actual categorical tensor API.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The old-complex column has its old differential, with positive sign. -/
@[reassoc]
theorem ιCons_zero_d (a : R) (s : List R) (n : ℕ) :
    ιCons a s 0 (n + 1) (n + 1) (by omega) ≫ (chainComplex (a :: s)).d (n + 1) n =
      ((ModuleCat.of R R) ◁ (chainComplex s).d (n + 1) n) ≫
        ιCons a s 0 n n (by omega) := by
  rw [ιCons_d,
    HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp), zero_add,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0 (show
      (ComplexShape.down ℕ).Rel (n + 1) n from rfl) n (by simp)]
  change (1 : ℤˣ) • (((ModuleCat.of R R) ◁ (chainComplex s).d (n + 1) n) ≫
    ιCons a s 0 n n (by omega)) = _
  exact one_smul ℤˣ _

/-- The new-factor column contributes multiplication minus the old differential. -/
@[reassoc]
theorem ιCons_one_d (a : R) (s : List R) (n : ℕ) :
    ιCons a s 1 (n + 1) (n + 2) (by omega) ≫
      (chainComplex (a :: s)).d (n + 2) (n + 1) =
    (ModuleCat.ofHom (LinearMap.lsmul R R a) ▷ (chainComplex s).X (n + 1)) ≫
        ιCons a s 0 (n + 1) (n + 1) (by omega) -
      ((ModuleCat.of R R) ◁ (chainComplex s).d (n + 1) n) ≫
        ιCons a s 1 n (n + 1) (by omega) := by
  rw [ιCons_d,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (n + 1) (n + 1) (by simp),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 1
      (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) (n + 1) (by simp [Nat.add_comm])]
  change (1 : ℤˣ) • _ + (-1 : ℤˣ) • _ = _
  simp only [one_smul, Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul,
    sub_eq_add_neg]
  rfl

/-- In degree one the new scalar is the horizontal differential. -/
@[reassoc]
theorem ιCons_one_zero_d (a : R) (s : List R) :
    ιCons a s 1 0 1 rfl ≫ (chainComplex (a :: s)).d 1 0 =
      (ModuleCat.ofHom (LinearMap.lsmul R R a) ▷ (chainComplex s).X 0) ≫
        ιCons a s 0 0 0 rfl := by
  rw [ιCons_d,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl) 0 0 rfl,
    HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp), add_zero]
  change (1 : ℤˣ) • ((ModuleCat.ofHom (LinearMap.lsmul R R a) ▷ (chainComplex s).X 0) ≫
    ιCons a s 0 0 0 rfl) = _
  exact one_smul ℤˣ _

end ChainComplex.Koszul

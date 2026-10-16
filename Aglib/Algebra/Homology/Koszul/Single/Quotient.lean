/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Basic

/-!
# Scalar quotients of nonnegative complexes

For an arbitrary complex of modules, quotienting each term by multiplication by
one scalar gives an actual complex and a natural degreewise surjective map.
This is the target of the augmentation from its one-element Koszul tensor.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] (a : R) (K : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The image of scalar multiplication in a term of a complex. -/
def scalarRange (n : ℕ) : Submodule R (K.X n) :=
  LinearMap.range (LinearMap.lsmul R (K.X n) a)

/-- Differentials preserve scalar multiples. -/
theorem scalarRange_le_comap (i j : ℕ) :
    scalarRange a K i ≤ (scalarRange a K j).comap (K.d i j).hom := by
  rintro x ⟨y, rfl⟩
  exact ⟨K.d i j y, (map_smul (K.d i j).hom a y).symm⟩

/-- The differential on the literal degreewise scalar quotient. -/
def quotientD (i j : ℕ) :
    ModuleCat.of R (K.X i ⧸ scalarRange a K i) ⟶
      ModuleCat.of R (K.X j ⧸ scalarRange a K j) :=
  ModuleCat.ofHom ((scalarRange a K i).mapQ (scalarRange a K j) (K.d i j).hom
    (scalarRange_le_comap a K i j))

/-- The actual degreewise cokernel of multiplication by a scalar. -/
def quotientComplex : ChainComplex (ModuleCat.{u} R) ℕ where
  X n := ModuleCat.of R (K.X n ⧸ scalarRange a K n)
  d := quotientD a K
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (K.d i j x) = 0
      rw [K.shape i j h]
      rfl
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (K.d j k (K.d i j x)) = 0
      have hx : K.d j k (K.d i j x) = 0 :=
        ConcreteCategory.congr_hom (K.d_comp_d i j k) x
      rw [hx]
      rfl

/-- The quotient projection, as a chain map. -/
def quotientProjection : K ⟶ quotientComplex a K where
  f n := ModuleCat.ofHom (scalarRange a K n).mkQ
  comm' i j _ := by
    rfl

@[simp]
theorem quotientProjection_f_apply (n : ℕ) (x : K.X n) :
    (quotientProjection a K).f n x = Submodule.Quotient.mk x := rfl

@[simp]
theorem quotientD_mk (i j : ℕ) (x : K.X i) :
    (quotientComplex a K).d i j (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.d i j x) := rfl

instance quotientProjection_epi (n : ℕ) : Epi ((quotientProjection a K).f n) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- A class vanishes exactly when its representative is a scalar multiple. -/
theorem quotientProjection_eq_zero_iff (n : ℕ) (x : K.X n) :
    (quotientProjection a K).f n x = 0 ↔ ∃ y : K.X n, a • y = x := by
  exact Submodule.Quotient.mk_eq_zero _

end ChainComplex.Koszul

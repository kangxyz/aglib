/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.Ring

/-!
# The actual extension of a derivation to a fraction field

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.Theta`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 52–145.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
namespace Derivation.FractionRing
universe u v w
variable {k : Type u} {A : Type v} {K : Type w}
variable [CommRing k] [CommRing A] [IsDomain A] [Field K]
variable [Algebra k A] [Algebra A K] [Algebra k K] [IsScalarTower k A K] [IsFractionRing A K]

/-- A derivation encoded as an actual first-order ring homomorphism. -/
def tangent (D : Derivation k A A) : A →+* TrivSqZeroExt K K where
  toFun a := ⟨algebraMap A K a, algebraMap A K (D a)⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap A K (a + b) = algebraMap A K a + algebraMap A K b
      simp
    · change algebraMap A K (D (a + b)) = algebraMap A K (D a) + algebraMap A K (D b)
      simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap A K (a * b) = algebraMap A K a * algebraMap A K b
      simp
    · change algebraMap A K (D (a * b)) = _
      change algebraMap A K (D (a * b)) =
        algebraMap A K a * algebraMap A K (D b) + algebraMap A K (D a) * algebraMap A K b
      simp [Derivation.leibniz, smul_eq_mul, mul_comm]

-- Retain the original domain and compatible scalar-tower inputs explicitly.
omit [IsDomain A] [Algebra k K] [IsScalarTower k A K] in
@[nolint unusedArguments]
theorem tangent_isUnit [IsDomain A] [Algebra k K] [IsScalarTower k A K]
    (D : Derivation k A A) (a : nonZeroDivisors A) :
    IsUnit (tangent (K := K) D a) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  change IsUnit (algebraMap A K a)
  exact IsLocalization.map_units K a

/-- Localization lifts the first-order map without a choice of fraction representation. -/
def liftTangent (D : Derivation k A A) : K →+* TrivSqZeroExt K K :=
  IsLocalization.lift (tangent_isUnit (K := K) D)

@[simp] theorem liftTangent_algebraMap (D : Derivation k A A) (a : A) :
    liftTangent (K := K) D (algebraMap A K a) = tangent D a :=
  IsLocalization.lift_eq _ _

@[simp] theorem fst_liftTangent (D : Derivation k A A) (x : K) :
    (liftTangent D x).fst = x := by
  have hh : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (liftTangent D) = RingHom.id K := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext a
    simp only [RingHom.comp_apply, RingHom.id_apply, liftTangent_algebraMap]
    rfl
  exact RingHom.congr_fun hh x

@[simp] theorem liftTangent_scalar (D : Derivation k A A) (a : k) :
    liftTangent (K := K) D (algebraMap k K a) = ⟨algebraMap k K a, 0⟩ := by
  rw [IsScalarTower.algebraMap_apply k A K, liftTangent_algebraMap]
  change (⟨algebraMap A K (algebraMap k A a), algebraMap A K (D (algebraMap k A a))⟩ :
    TrivSqZeroExt K K) = _
  ext
  · rfl
  · simp

/-- The canonical fraction-field extension of an actual derivation. -/
def extend (D : Derivation k A A) : Derivation k K K where
  toFun x := (liftTangent D x).snd
  map_add' x y := by simp
  map_smul' a x := by
    rw [Algebra.smul_def, map_mul, liftTangent_scalar]
    change (algebraMap k K a) * (liftTangent D x).snd + 0 * (liftTangent D x).fst = _
    simp [Algebra.smul_def]
  map_one_eq_zero' := by simp
  leibniz' x y := by
    simp [TrivSqZeroExt.snd_mul, smul_eq_mul, mul_comm, add_comm]

@[simp] theorem extend_algebraMap (D : Derivation k A A) (a : A) :
    extend (K := K) D (algebraMap A K a) = algebraMap A K (D a) := by
  change (liftTangent D (algebraMap A K a)).snd = _
  rw [liftTangent_algebraMap]
  rfl
/-- The usual quotient rule is a theorem of the constructed extension. -/
theorem extend_div (D : Derivation k A A) (a b : A) :
    extend (K := K) D (algebraMap A K a / algebraMap A K b) =
      (algebraMap A K b * algebraMap A K (D a) -
        algebraMap A K a * algebraMap A K (D b)) / (algebraMap A K b) ^ 2 := by
  simp only [Derivation.leibniz_div, extend_algebraMap, smul_eq_mul]
  ring

/-- The extension is uniquely determined by the actual original derivation. -/
theorem extend_unique (D : Derivation k A A) (E : Derivation k K K)
    (h : ∀ a : A, E (algebraMap A K a) = algebraMap A K (D a)) : extend D = E := by
  apply Derivation.ext
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  simp only [Derivation.leibniz_div, extend_algebraMap, h]

end Derivation.FractionRing

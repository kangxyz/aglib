/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.FiniteIntegralCapture
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Actual localized finite-subalgebra coefficient capture

The original finite subalgebra is localized at the common base denominator.
Its actual localization map into the extension field is injective and contains
the original unscaled coefficients in its range. This is the coefficient
producer for restricting a split quotient and its chosen preimages; it does
not assume that tensoring an arbitrary algebra preserves this injection.
-/

@[expose] public noncomputable section

namespace IsFractionRing

universe u v w

section AwayMap

variable {R : Type u} [CommRing R] {L : Type v} [Field L] [Algebra R L]

/-- The original localization of a subalgebra maps into its ambient field. -/
def finiteSubalgebraAwayMap (B : Subalgebra R L) (r : R)
    (hr : algebraMap R L r ≠ 0) :
    Localization.Away (algebraMap R B r) →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom (f := B.val) (algebraMap R B r)
    (show IsUnit (B.val (algebraMap R B r)) from isUnit_iff_ne_zero.mpr hr)

/-- The localized embedding retains the original subalgebra inclusion. -/
@[simp] theorem finiteSubalgebraAwayMap_algebraMap (B : Subalgebra R L) (r : R)
    (hr : algebraMap R L r ≠ 0) (b : B) :
    finiteSubalgebraAwayMap B r hr
      (algebraMap B (Localization.Away (algebraMap R B r)) b) = (b : L) := by
  simp [finiteSubalgebraAwayMap]

/-- The actual localized subalgebra map is injective. This assertion concerns
only the coefficient rings, not a tensor product with an arbitrary algebra. -/
theorem finiteSubalgebraAwayMap_injective (B : Subalgebra R L) (r : R)
    (hr : algebraMap R L r ≠ 0) : Function.Injective (finiteSubalgebraAwayMap B r hr) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (algebraMap R B r)) (finiteSubalgebraAwayMap B r hr).toRingHom).mpr
  intro x y
  constructor
  · exact congrArg (finiteSubalgebraAwayMap B r hr)
  · intro h
    change finiteSubalgebraAwayMap B r hr (algebraMap B _ x) =
      finiteSubalgebraAwayMap B r hr (algebraMap B _ y) at h
    rw [finiteSubalgebraAwayMap_algebraMap, finiteSubalgebraAwayMap_algebraMap] at h
    exact congrArg (algebraMap B (Localization.Away (algebraMap R B r)))
      (Subtype.val_injective h)

/-- Dividing an actual captured integral multiple by the original denominator
gives a preimage of the unscaled coefficient in the original localization. -/
theorem mem_range_finiteSubalgebraAwayMap (B : Subalgebra R L) (r : R)
    (hr : algebraMap R L r ≠ 0) (x : L) (hx : r • x ∈ B) :
    x ∈ (finiteSubalgebraAwayMap B r hr).range := by
  let C := Localization.Away (algebraMap R B r)
  let d : Submonoid.powers (algebraMap R B r) :=
    ⟨algebraMap R B r, ⟨1, pow_one _⟩⟩
  let y : C := IsLocalization.mk' C (⟨r • x, hx⟩ : B) d
  refine ⟨y, ?_⟩
  apply mul_right_cancel₀ hr
  have hy := congrArg (finiteSubalgebraAwayMap B r hr)
    (IsLocalization.mk'_spec C (⟨r • x, hx⟩ : B) d)
  dsimp only [C, d] at hy
  simp only [map_mul, finiteSubalgebraAwayMap_algebraMap] at hy
  change finiteSubalgebraAwayMap B r hr y * algebraMap R L r = r • x at hy
  exact hy.trans (by rw [Algebra.smul_def, mul_comm])

end AwayMap

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  {L : Type w} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Module.Finite K L]

include K in
/-- Finite coefficients actually lift to a localized module-finite subalgebra.
The original ambient-field embedding and its injectivity are retained. -/
theorem exists_finiteSubalgebra_away_capture (s : Finset L) :
    ∃ r : R, r ≠ 0 ∧ ∃ hr : algebraMap R L r ≠ 0,
      ∃ B : Subalgebra R L, Module.Finite R B ∧
        Function.Injective (finiteSubalgebraAwayMap B r hr) ∧
        ∀ x ∈ s, x ∈ (finiteSubalgebraAwayMap B r hr).range := by
  obtain ⟨r, hr, B, hB, hcapture⟩ := exists_finiteSubalgebra_common_multiple R K s
  have hrL : algebraMap R L r ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K L]
    have hrK : algebraMap R K r ≠ 0 := fun h =>
      hr ((IsFractionRing.injective R K) (h.trans (map_zero _).symm))
    exact fun h => hrK ((algebraMap K L).injective (h.trans (map_zero _).symm))
  exact ⟨r, hr, hrL, B, hB, finiteSubalgebraAwayMap_injective B r hrL,
    fun x hx => mem_range_finiteSubalgebraAwayMap B r hrL x (hcapture x hx)⟩

end IsFractionRing

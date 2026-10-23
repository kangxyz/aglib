/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Powers
public import Aglib.RingTheory.Smooth.Field
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.MixedCharZero
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Coefficient sections from a formally smooth residue field

For a complete local algebra over a specified field, formal smoothness of
the actual residue field constructs a coefficient section preserving that
field action. The construction reuses the native formally smooth lift into
the actual adic completion. Its finite-order projections are compatible,
and the resulting section has exactly those quotient maps.

For equal-characteristic local rings, the prime-field action gives formal
smoothness without any restriction on the residue field. In residue
characteristic zero the rational action is derived from the local ring
itself. No Noetherianity, domain, finite-type, or finite transcendence-degree
assumption is used. Mixed-characteristic Cohen coefficient existence remains
separate.
-/

@[expose] public noncomputable section

namespace IsLocalRing

section FormallySmooth

variable (F R : Type*) [Field F] [CommRing R] [IsLocalRing R] [Algebra F R]
  [Algebra.FormallySmooth F (ResidueField R)]

/-- The native formally smooth lift of the identity of the actual residue
field into the literal maximal-ideal completion. -/
def residueCompletionSection :
    ResidueField R →ₐ[F] AdicCompletion (maximalIdeal R) R :=
  (Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq
    (I := maximalIdeal R) (AlgHom.id F (ResidueField R))).choose

/-- The first projection of the completion lift is the original residue
identity, as an algebra map over the specified coefficient field. -/
theorem evalOne_comp_residueCompletionSection :
    ((AdicCompletion.evalOneₐ (maximalIdeal R)).restrictScalars F).comp
      (residueCompletionSection F R) = AlgHom.id F (ResidueField R) :=
  (Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq
    (I := maximalIdeal R) (AlgHom.id F (ResidueField R))).choose_spec

/-- The actual finite-order quotient maps of the chosen completion lift. -/
def coefficientSectionMod (n : ℕ) :
    ResidueField R →ₐ[F] R ⧸ maximalIdeal R ^ n :=
  ((AdicCompletion.evalₐ (maximalIdeal R) n).restrictScalars F).comp
    (residueCompletionSection F R)

/-- Compatibility uses the original ideal-power quotient transition maps. -/
theorem coefficientSectionMod_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ F (Ideal.pow_le_pow_right h)).comp
      (coefficientSectionMod F R n) = coefficientSectionMod F R m := by
  ext x
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
      (AdicCompletion.evalₐ (maximalIdeal R) n (residueCompletionSection F R x)) =
    AdicCompletion.evalₐ (maximalIdeal R) m (residueCompletionSection F R x)
  exact AdicCompletion.factor_evalₐ (maximalIdeal R) h (residueCompletionSection F R x)

variable [IsAdicComplete (maximalIdeal R) R]

/-- The coefficient section obtained by the native inverse of the actual
completion map. -/
def coefficientSection : ResidueField R →ₐ[F] R :=
  ((AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm.toAlgHom.restrictScalars F).comp
    (residueCompletionSection F R)

/-- Every quotient of the coefficient section is the prescribed compatible
finite-order map. -/
theorem mk_comp_coefficientSection (n : ℕ) :
    (Ideal.Quotient.mkₐ F (maximalIdeal R ^ n)).comp (coefficientSection F R) =
      coefficientSectionMod F R n := by
  ext x
  exact AdicCompletion.mk_ofAlgEquiv_symm (maximalIdeal R) n
    (residueCompletionSection F R x)

/-- The coefficient section is a section of the literal residue map. -/
@[simp]
theorem residue_coefficientSection (x : ResidueField R) :
    residue R (coefficientSection F R x) = x := by
  change Ideal.Quotient.mk (maximalIdeal R)
    ((AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm
      (residueCompletionSection F R x)) = x
  rw [AdicCompletion.mk_ofAlgEquiv_symm_eq_evalOneₐ]
  exact AlgHom.congr_fun (evalOne_comp_residueCompletionSection F R) x

/-- The original residue identity is retained as an equality of actual
coefficient-algebra homomorphisms. -/
theorem residue_comp_coefficientSection :
    (IsScalarTower.toAlgHom F R (ResidueField R)).comp (coefficientSection F R) =
      AlgHom.id F (ResidueField R) := by
  ext x
  exact residue_coefficientSection F R x

/-- The chosen section preserves the specified coefficient field action. -/
theorem coefficientSection_algebraMap (a : F) :
    coefficientSection F R (algebraMap F (ResidueField R) a) = algebraMap F R a :=
  (coefficientSection F R).commutes a

/-- The actual coefficient section is injective. -/
theorem coefficientSection_injective : Function.Injective (coefficientSection F R) :=
  (show Function.LeftInverse (residue R) (coefficientSection F R) from
    residue_coefficientSection F R).injective

/-- Formal smoothness of the actual residue field produces a coefficient
section over the original coefficient field, with no supplied section. -/
theorem exists_coefficientSection_of_formallySmooth :
    ∃ s : ResidueField R →ₐ[F] R,
      (IsScalarTower.toAlgHom F R (ResidueField R)).comp s = AlgHom.id F (ResidueField R) :=
  ⟨coefficientSection F R, residue_comp_coefficientSection F R⟩

end FormallySmooth

section CharacteristicZero

variable (R : Type*) [CommRing R] [IsLocalRing R] [CharZero (ResidueField R)]

/-- The actual local ring admits a rational coefficient action when its
residue field has characteristic zero. The action is derived from that
condition, rather than assumed as coefficient data. -/
@[instance_reducible]
def ratAlgebraOfResidueCharZero : Algebra ℚ R := by
  apply Classical.choice
  apply (EqualCharZero.nonempty_algebraRat_iff R).mpr
  intro I hI
  let f : R ⧸ I →+* ResidueField R := Ideal.Quotient.factor (le_maximalIdeal hI)
  constructor
  intro a b hab
  apply Nat.cast_injective (R := ResidueField R)
  simpa only [map_natCast] using congrArg f hab

variable [IsAdicComplete (maximalIdeal R) R]

/-- An actual coefficient-field section in residue characteristic zero,
with no finite-type condition on the residue field. -/
def coefficientSectionOfResidueCharZero : ResidueField R →+* R := by
  let : Algebra ℚ R := ratAlgebraOfResidueCharZero R
  let : Algebra ℚ (ResidueField R) := ResidueField.algebra R
  let : Algebra.FormallySmooth ℚ (ResidueField R) :=
    Algebra.FormallySmooth.field_of_perfectField (F := ℚ) (K := ResidueField R)
  exact (coefficientSection ℚ R).toRingHom

/-- The characteristic-zero coefficient section fixes every actual residue
class after the original residue map. -/
@[simp]
theorem residue_coefficientSectionOfResidueCharZero (x : ResidueField R) :
    residue R (coefficientSectionOfResidueCharZero R x) = x := by
  let : Algebra ℚ R := ratAlgebraOfResidueCharZero R
  let : Algebra ℚ (ResidueField R) := ResidueField.algebra R
  let : Algebra.FormallySmooth ℚ (ResidueField R) :=
    Algebra.FormallySmooth.field_of_perfectField (F := ℚ) (K := ResidueField R)
  exact residue_coefficientSection ℚ R x

/-- Every complete local ring whose actual residue field has characteristic
zero has a section of its actual residue map. -/
theorem exists_coefficientSection_of_residue_charZero :
    ∃ s : ResidueField R →+* R, (residue R).comp s = RingHom.id (ResidueField R) := by
  refine ⟨coefficientSectionOfResidueCharZero R, ?_⟩
  ext x
  exact residue_coefficientSectionOfResidueCharZero R x

end CharacteristicZero

section PositiveCharacteristic

variable (R : Type*) [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- A coefficient section in positive equal characteristic, including
imperfect residue fields of arbitrary p-rank. -/
def coefficientSectionOfCharP : ResidueField R →+* R := by
  let : Algebra (ZMod p) R := ZMod.algebra R p
  let : Algebra (ZMod p) (ResidueField R) := ResidueField.algebra R
  let : Algebra.FormallySmooth (ZMod p) (ResidueField R) :=
    Algebra.FormallySmooth.field_of_perfectField (F := ZMod p) (K := ResidueField R)
  exact (coefficientSection (ZMod p) R).toRingHom

/-- The positive-characteristic coefficient section is a right inverse
of the original residue map. -/
@[simp]
theorem residue_coefficientSectionOfCharP (x : ResidueField R) :
    residue R (coefficientSectionOfCharP R p x) = x := by
  let : Algebra (ZMod p) R := ZMod.algebra R p
  let : Algebra (ZMod p) (ResidueField R) := ResidueField.algebra R
  let : Algebra.FormallySmooth (ZMod p) (ResidueField R) :=
    Algebra.FormallySmooth.field_of_perfectField (F := ZMod p) (K := ResidueField R)
  exact residue_coefficientSection (ZMod p) R x

include p in
/-- Every complete local ring of prime characteristic has a section of
its actual residue map, without a perfect-residue hypothesis. -/
theorem exists_coefficientSection_of_charP :
    ∃ s : ResidueField R →+* R, (residue R).comp s = RingHom.id (ResidueField R) := by
  refine ⟨coefficientSectionOfCharP R p, ?_⟩
  ext x
  exact residue_coefficientSectionOfCharP R p x

end PositiveCharacteristic

end IsLocalRing

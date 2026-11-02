/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Polynomial
public import Aglib.RingTheory.Nagata.Finite
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.FiniteType

/-! # Japanese domains of finite type over a field

Noether normalization supplies one finite injective polynomial algebra map.
Japanese ascent uses that same map and retains the original extension field
and integral closure. The coefficient field is arbitrary: neither perfection
nor separability of the tested finite field extension is assumed.

All rings lie in one ambient universe and the Japanese predicate uses auxiliary
universe zero. This does not assert finite-type stability over an arithmetic
base or construct a mixed-characteristic normal model.
-/

@[expose] public noncomputable section

universe u

namespace IsJapaneseRing

/-- A field is Japanese, including for inseparable finite extensions. -/
theorem of_field (k : Type u) [Field k] : IsJapaneseRing.{u, 0} k := by
  intro L hL hFL hKL hT hfin
  let e := IsLocalization.algEquiv (R := k) (nonZeroDivisors k) (FractionRing k) k
  let : Module.Finite k (FractionRing k) := Module.Finite.equiv e.symm.toLinearEquiv
  let : Module.Finite k L := Module.Finite.trans (FractionRing k) L
  exact Module.Finite.of_injective (integralClosure k L).val.toLinearMap
    Subtype.val_injective

/-- Iterated polynomial Japanese ascent, using the native finite-variable
polynomial equivalences and no change to the coefficient ring. -/
theorem mvPolynomial_fin {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (hR : IsJapaneseRing.{u, 0} R) (n : ℕ) :
    IsJapaneseRing.{u, 0} (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact hR.of_ringEquiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
  | succ n ih =>
    exact ih.polynomial.of_ringEquiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv

/-- Every domain of finite type over an arbitrary field is Japanese. -/
theorem of_finiteType_field (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] : IsJapaneseRing.{u, 0} R := by
  obtain ⟨n, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k R
  let : Algebra (MvPolynomial (Fin n) k) R := g.toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial (Fin n) k) R := hfinite
  exact (mvPolynomial_fin (of_field k) n).of_finite (by exact hg)

/-- The original integral closure in any supplied finite extension of a
fraction field of a finite-type field domain is finite over the original ring. -/
theorem finite_integralClosure_of_finiteType_field
    (k R K L : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] : Module.Finite R (integralClosure R L) :=
  (of_finiteType_field k R).finite_integralClosure_of_isFractionRing K L

end IsJapaneseRing

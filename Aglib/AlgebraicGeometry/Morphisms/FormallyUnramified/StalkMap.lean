/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.RingHom.Unramified

/-!
# Unramified coordinate primes and actual stalk maps

For arbitrary affine charts of a scheme morphism, unramifiedness at the
coordinate prime is equivalent to formal unramifiedness of the original
stalk map. The comparison uses the canonical arrow isomorphism and introduces
no finiteness, reducedness, normality, or nonempty-chart hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Unramifiedness at the actual coordinate prime of a point is equivalent to
formal unramifiedness of the original local-ring map. The coordinate algebra
is the literal map on the specified affine charts. -/
theorem isUnramifiedAt_iff_stalkMap_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (x : V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    Algebra.IsUnramifiedAt Γ(Y, U) (hV.primeIdealOf x).asIdeal ↔
      (f.stalkMap x).hom.FormallyUnramified := by
  let A := Γ(Y, U)
  let B := Γ(X, V)
  let φ := f.appLE U V hVU
  let p := (hU.primeIdealOf ⟨f x, hVU x.property⟩).asIdeal
  let q := (hV.primeIdealOf x).asIdeal
  have : p.IsPrime := (hU.primeIdealOf ⟨f x, hVU x.property⟩).isPrime
  have : q.IsPrime := (hV.primeIdealOf x).isPrime
  have hpq : p = q.comap φ.hom :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU x.property).symm
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q φ.hom hpq).toAlgebra
  have : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun a => (Localization.localRingHom_to_map p q φ.hom hpq a).symm
  have hl : (f.stalkMap x).hom.FormallyUnramified ↔
      (Localization.localRingHom p q φ.hom hpq).FormallyUnramified :=
    RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU x.property)
  change Algebra.FormallyUnramified A (Localization.AtPrime q) ↔ _
  rw [hl]
  change Algebra.FormallyUnramified A (Localization.AtPrime q) ↔
    Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  constructor
  · intro h
    let := h
    exact Algebra.FormallyUnramified.of_restrictScalars A _ _
  · intro h
    let := h
    let : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
      Algebra.FormallyUnramified.of_isLocalization p.primeCompl
    exact Algebra.FormallyUnramified.comp A (Localization.AtPrime p) (Localization.AtPrime q)

end AlgebraicGeometry.Scheme.Hom

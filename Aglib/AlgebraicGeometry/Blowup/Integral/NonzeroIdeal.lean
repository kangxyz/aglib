/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Support
public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Charts


/-!
# Integrality of the same original affine-ideal blowup

An actual nonzero element of the original ideal excludes the original generic
point from its centre. The existing native integral-blowup theorem then applies
to the same canonical blowup, without a replacement model or regularity premise.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme.Blowup.RegularPoint

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- An original nonzero ideal element makes the actual constructed blowup integral. -/
theorem idealBlowup_isIntegral_of_mem_ne_zero {R : Type u} [CommRing R] [IsDomain R]
    (I : Ideal R) (a : R) (ha : a ∈ I) (hne : a ≠ 0) : IsIntegral (canonicalBlowup I) := by
  apply Blowup.blowup_isIntegral (Blowup.affineCenter R I)
  rw [Blowup.support_affineCenter, genericPoint_eq_bot_of_affine]
  intro h
  apply hne
  exact (show a ∈ (⊥ : Ideal R) from h ha)

end AlgebraicGeometry.Scheme.Blowup

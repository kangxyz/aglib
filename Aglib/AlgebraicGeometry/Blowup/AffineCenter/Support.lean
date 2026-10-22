/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineCenter

/-!
# Support of an affine blowup centre

The general support comparison, relocated unchanged from the surface
principalization consumer. No surface or regularity hypothesis is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Blowup

theorem support_affineCenter {A : Type u} [CommRing A] (J : Ideal A) :
    ((affineCenter A J).support : Set (Spec (.of A))) = PrimeSpectrum.zeroLocus (J : Set A) := by
  rw [affineCenter, Scheme.Hom.support_ker]
  change closure (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))) = _
  rw [_root_.range_comap_of_surjective (A ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  exact (PrimeSpectrum.isClosed_zeroLocus _).closure_eq

end AlgebraicGeometry.Scheme.Blowup

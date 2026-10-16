/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Charts
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Cartesian coefficient-change squares on the original projective charts

The original homogeneous chart-ring maps form a pushout, by the native
polynomial tensor-product pushout and the original coordinate equivalences.
Their spectrum square and the original open-chart square are both Cartesian.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original chart-ring coefficient square is a native pushout for every ring map. -/
theorem coordinateRingMap_isPushout (f : R →+* S) (ι : Type u) (i : ι) :
    IsPushout (CommRingCat.ofHom (coordinateRingCoefficient R ι i)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (coordinateRingMap f ι i))
      (CommRingCat.ofHom (coordinateRingCoefficient S ι i)) := by
  let : Algebra R S := f.toAlgebra
  have hp : IsPushout
      (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial {j : ι // j ≠ i} R))
      (CommRingCat.ofHom f)
      (CommRingCat.ofHom (MvPolynomial.map f))
      (CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial {j : ι // j ≠ i} S)) := by
    simpa only [MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_def,
      RingHom.algebraMap_toAlgebra, MvPolynomial.map] using
      (CommRingCat.isPushout_of_isPushout R (MvPolynomial {j : ι // j ≠ i} R) S
        (MvPolynomial {j : ι // j ≠ i} S))
  refine hp.of_iso (Iso.refl _) (coordinateRingEquivPolynomial R ι i).symm.toCommRingCatIso
    (Iso.refl _) (coordinateRingEquivPolynomial S ι i).symm.toCommRingCatIso ?_ ?_ ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact polynomialToCoordinateRing_C R ι i r
  · simp
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact (RingHom.congr_fun (coordinateRingMap_comp_polynomialToCoordinateRing f ι i) p).symm
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    exact polynomialToCoordinateRing_C S ι i s

/-- The actual spectra of the original homogeneous chart rings form a Cartesian square. -/
theorem coordinateRingMap_isPullback (f : R →+* S) (ι : Type u) (i : ι) :
    IsPullback (Spec.map (CommRingCat.ofHom (coordinateRingMap f ι i)))
      (Spec.map (CommRingCat.ofHom (coordinateRingCoefficient S ι i)))
      (Spec.map (CommRingCat.ofHom (coordinateRingCoefficient R ι i)))
      (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (coordinateRingMap_isPushout f ι i)

/-- The actual homogeneous chart above a standard chart is its original open pullback. -/
theorem coordinateRingMap_awayι_isPullback (f : R →+* S) (ι : Type u) (i : ι) :
    IsPullback (Spec.map (CommRingCat.ofHom (coordinateRingMap f ι i)))
      (Proj.awayι (MvPolynomial.homogeneousSubmodule ι S) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X S i) Nat.zero_lt_one)
      (Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one)
      (map f ι) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (coordinateRingMap_awayι f ι i)
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  exact map_preimage_coordinateOpen f ι i

end AlgebraicGeometry.ProjectiveSpace

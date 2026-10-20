/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UniversalProperty
public import Aglib.RingTheory.ReesAlgebra.Away
public import Aglib.RingTheory.Blowup.PowerNode.Overlaps

/-!
# Original objects and forward maps in the blowup/node ring interfaces

The genuine Rees comparison lands in the literal migrated saturated algebra,
and its ratio element is the original geometric-interface ratio. Power-node
chart algebra retains its original UFD/nonzero-scalar scope.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
universe u
namespace AglibTest.BlowupNodeAlgebra

/-- The new homogeneous localization uses the same actual chart carrier. -/
def saturatedCarrier {A : Type u} [CommRing A] (I : Ideal A) (a : I) :
    reesAlgebra.homogeneousAway I a ≃ₐ[A] Scheme.Blowup.affineBlowupAlgebra A I a :=
  reesAlgebra.awayEquiv I a

/-- Its original b/a is exactly the ratio used by the migrated scheme interface. -/
theorem ratio_forward {A : Type u} [CommRing A] (I : Ideal A) (a b : I) :
    saturatedCarrier I a
        (HomogeneousLocalization.Away.mk (reesAlgebra.grading I)
          (reesAlgebra.degreeOne_mem I a) 1 (reesAlgebra.degreeOne I b)
          (by simpa only [one_smul] using reesAlgebra.degreeOne_mem I b)) =
      Scheme.Blowup.ratio A I a b := by
  apply Subtype.ext
  exact reesAlgebra.awayEquiv_ratio I a b

/-- The middle exponent drops by two over any domain UFD and nonzero scalar. -/
def middleCarrier {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (π : R) (hπ : π ≠ 0) (m : ℕ) :
    PlaneNode.Ring (π ^ m) ≃ₐ[R] PowerNode.Rees.middleChart π m :=
  PowerNode.Rees.middleReesEquiv π hπ m

end AglibTest.BlowupNodeAlgebra

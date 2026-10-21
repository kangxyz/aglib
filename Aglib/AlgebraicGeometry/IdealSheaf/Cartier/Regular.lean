/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Interfaces
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Factorial
public import Aglib.RingTheory.RegularLocalRing.Factorial

/-!
# Height-one integral closed subschemes of regular schemes

Regularity of the actual ambient stalks supplies domainness and unique
factorization in every dimension. The factorial-stalk theorem then proves
local rank one of the actual closed-immersion kernel ideal module.

The universal theorem inhabits the existing `RegularCodimOneIdealInvertible`
proposition under its original hypotheses. The height-one condition on the
actual stalk-map kernels is retained; no dimension or factoriality premise is
added to the regular-scheme result.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Hom

variable {C X : Scheme.{u}}

/-- Height-one integral closed subschemes of locally Noetherian schemes with
regular actual stalks have locally rank-one actual kernel ideal modules,
without a dimension bound or a supplied factoriality hypothesis. -/
theorem idealModule_isLocallyRankOne_of_regularStalks
    [IsLocallyNoetherian X] [IsIntegral C] (i : C ⟶ X) [IsClosedImmersion i]
    (hregular : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hheight : ∀ c : C, (RingHom.ker (i.stalkMap c).hom).height = 1) :
    IsLocallyRankOne X (idealModule i) := by
  refine idealModule_isLocallyRankOne_of_factorialStalks i ?_ ?_ hheight
  · intro x
    have : IsRegularLocalRing (X.presheaf.stalk x) := hregular x
    exact IsRegularLocalRing.isDomain_of_regularLocal (X.presheaf.stalk x)
  · intro x
    have : IsRegularLocalRing (X.presheaf.stalk x) := hregular x
    exact IsRegularLocalRing.uniqueFactorizationMonoid_of_regularLocal (X.presheaf.stalk x)

namespace Cartier

/-- The original universal codimension-one Cartier ideal proposition is
inhabited, with its original objects, maps, universes, and hypotheses. -/
theorem regularCodimOneIdealInvertible : RegularCodimOneIdealInvertible.{u} := by
  intro X C _ _ i hi hregular hheight
  have : IsClosedImmersion i := hi
  exact idealModule_isLocallyRankOne_of_regularStalks i hregular hheight

end Cartier

end AlgebraicGeometry.Scheme.Hom

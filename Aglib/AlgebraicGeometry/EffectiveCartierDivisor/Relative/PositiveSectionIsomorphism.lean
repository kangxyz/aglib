/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.PositiveSection
public import Aglib.AlgebraicGeometry.Modules.Invertible.FibrewiseIsomorphism

/-!
# Isomorphism of the positive-divisor adjunction map

The canonical adjunction map is detected on the actual pulled line bundles.
The original base remains locally Noetherian, as required by the rank-one
cohomology and canonical base-change supplier. All algebraically closed
field-valued points of that base are used. The actual fibre Cartier map and
the geometric cohomology profile remain explicit hypotheses.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules.Invertible
open Scheme.Cohomology
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {X S D : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X)
variable (hI : IsLocallyRankOne X (idealModule i))
variable (hbase : RelativeCartierIdealBaseChange.{u})
variable [IsClosedImmersion i] [Flat (i ≫ p)]
variable [IsProper p] [LocallyOfFinitePresentation p] [Flat p] [IsLocallyNoetherian S]
variable (hL : FibreCohomologyConcentrated p (dualLineBundle X ⟨idealModule i, hI⟩).val 1)

include hbase hL in
/-- The original positive-divisor adjoint is invertible from its rank-one geometric profile.
The proof uses the proved rank-one criterion on the actual module map. -/
theorem divisorPositiveAdjoint_isIso_of_geometricProfile
    (hcurves : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      IsIntegral (pullback p t)) : IsIso (divisorPositiveAdjoint p i hI) := by
  let L := dualLineBundle X ⟨idealModule i, hI⟩
  let P := Scheme.Cohomology.directImageLineBundle p L hL
  apply lineBundleMap_isIso_of_geometricPullback_isIso (structureLineBundle S) P
    (divisorPositiveAdjoint p i hI)
  intro K _ _ t
  let := hcurves K t
  exact Scheme.Modules.Invertible.fieldLineBundleMap_isIso_of_ne_zero K
    (pullbackLineBundle t (structureLineBundle S)) (pullbackLineBundle t P)
    ((Scheme.Modules.pullback t).map (divisorPositiveAdjoint p i hI))
    (divisorPositiveAdjoint_fibre_ne_zero p i hI hbase K t)

end AlgebraicGeometry.Scheme.Hom

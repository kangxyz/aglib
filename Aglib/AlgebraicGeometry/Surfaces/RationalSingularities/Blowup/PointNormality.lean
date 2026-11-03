/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Normality
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.AlgebraicGeometry.Descent.LocalModification

/-!
# Normality of the original blowup at a rational surface point

The actual localized maximal-ideal blowup is normal by rationality. The existing
original localization square and unchanged complement transport that normality
to the whole original point blowup, not only to globally closed child stalks.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities

/-- Blowing up an actual closed rational surface point preserves normality of
all original stalks. No global integrality, Noetherianity or properness is needed. -/
theorem normalStalks_pointBlowup_of_rational_stalk
    (X : Scheme.{u}) (hX : NormalStalks X) (x : X)
    (hx : IsClosed ({x} : Set X))
    (hNagata : IsNagataRing.{u, 0} (X.presheaf.stalk x))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2)
    (hRat : letI : IsDomain (X.presheaf.stalk x) := (hX x).1;
      NormalModificationH1Vanishing (X.presheaf.stalk x)) :
    NormalStalks (blowupDatum (X.fromSpecResidueField x).ker).Y := by
  let : IsDomain (X.presheaf.stalk x) := (hX x).1
  let : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  let : IsNoetherianRing (X.presheaf.stalk x) := hNagata.isNoetherianRing
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let D := blowupDatum (affineCenter (X.presheaf.stalk x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))
  have hD : NormalStalks D.Y :=
    MaximalIdealBlowup.ordinary_normalStalks (X.presheaf.stalk x) hd hNagata hRat
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hdisjoint : Disjoint (LocalModification.pointComplement x hx : Set X)
      ((X.fromSpecResidueField x).ker.support : Set X) := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
    apply Set.disjoint_left.mpr
    intro y hy hyx
    exact (show y ∉ ({x} : Set X) from hy) hyx
  have haway : IsIso (B.map ∣_ LocalModification.pointComplement x hx) :=
    B.restrict_isIso_of_disjoint _ hdisjoint
  exact LocalModification.normalStalks_of_local_replacement x hx hX hD
    (RegularPoint.stalkBlowupComparison X x hx) D.map B.map
    (RegularPoint.stalkBlowupComparison_isPullback X x hx) haway

end AlgebraicGeometry.Scheme.RationalSingularities

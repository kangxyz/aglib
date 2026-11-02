/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.SmoothCurve
public import Aglib.AlgebraicGeometry.IdealSheaf.ClosedImmersionStalk
public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Aglib.RingTheory.DiscreteValuationRing.SameUniformizerValuation
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Original local orders at cartesian rational sections

The actual rational-point ideal has maximal stalk ideal. Cartesian pullback
of that ideal therefore extends the original maximal ideal to the target
maximal ideal. For DVR stalks this preserves a uniformizer, and the compatible
original function-field map preserves local order, including zero. Neither
finiteness of the ambient morphism nor separability of the field extension is
assumed. A cartesian section square is geometric input, not an assumed order
comparison or Picard-class equality.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RationalPoint

variable {k K : Type u} [Field k] [Field K] {X Y : Scheme.{u}}

/-- The original ideal of a rational section has the actual maximal stalk
ideal at its rational point. -/
theorem ker_stalkIdeal_eq_maximalIdeal (r : RationalPoint k X) :
    r.sectionMap.ker.stalkIdeal r.point = IsLocalRing.maximalIdeal r.localRing := by
  let : IsClosedImmersion r.sectionMap := r.section_isClosedImmersion
  have he : Function.Surjective r.evaluation :=
    fun a => ⟨r.constants a, r.evaluation_constants a⟩
  have hk : RingHom.ker (r.sectionMap.stalkMap (IsLocalRing.closedPoint k)).hom =
      RingHom.ker r.evaluation := by
    ext a
    change r.sectionMap.stalkMap (IsLocalRing.closedPoint k) a = 0 ↔
      (stalkClosedPointIso (.of k)).hom
        (r.sectionMap.stalkMap (IsLocalRing.closedPoint k) a) = 0
    constructor
    · intro h
      exact (congrArg (fun z => (stalkClosedPointIso (.of k)).hom z) h).trans
        (map_zero _)
    · intro h
      exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of k)).hom).injective
        (h.trans (map_zero _).symm)
  exact (r.sectionMap.ker_stalkIdeal_eq_ker_stalkMap (IsLocalRing.closedPoint k)).trans
    (hk.trans (IsLocalRing.ker_eq_maximalIdeal r.evaluation he))

/-- The underlying rational point equality comes from the original cartesian
section square and the unique point of the source field spectrum. -/
theorem point_map_of_isPullback (r : RationalPoint k X) (s : RationalPoint K Y)
    (q : Spec (.of K) ⟶ Spec (.of k)) (b : Y ⟶ X)
    (H : IsPullback q s.sectionMap r.sectionMap b) : b s.point = r.point := by
  have h := congrArg (fun f : Spec (.of K) ⟶ X => f (IsLocalRing.closedPoint K)) H.w
  have hq : q (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint k :=
    Subsingleton.elim _ _
  change r.sectionMap (q (IsLocalRing.closedPoint K)) = b s.point at h
  exact h.symm.trans (congrArg r.sectionMap hq)

/-- Cartesian rational sections extend the actual maximal ideal along the
actual ambient stalk map, without a smoothness or separability hypothesis. -/
theorem map_maximalIdeal_of_isPullback (r : RationalPoint k X) (s : RationalPoint K Y)
    (q : Spec (.of K) ⟶ Spec (.of k)) (b : Y ⟶ X)
    (H : IsPullback q s.sectionMap r.sectionMap b) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (b s.point))).map
        (b.stalkMap s.point).hom = IsLocalRing.maximalIdeal s.localRing := by
  let : IsClosedImmersion r.sectionMap := r.section_isClosedImmersion
  have hx : r.sectionMap.ker.stalkIdeal (b s.point) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (b s.point)) := by
    rw [point_map_of_isPullback r s q b H]
    exact r.ker_stalkIdeal_eq_maximalIdeal
  have hker := Hom.ker_eq_comap_of_isPullback_of_isClosedImmersion
    r.sectionMap s.sectionMap b q H
  have hh := congrArg (fun I : Y.IdealSheafData => I.stalkIdeal s.point) hker
  rw [IdealSheafData.stalkIdeal_comap, hx, s.ker_stalkIdeal_eq_maximalIdeal] at hh
  exact hh.symm

/-- Every original uniformizer remains a uniformizer under the actual stalk
map of a cartesian rational section square. -/
theorem irreducible_stalkMap_of_isPullback (r : RationalPoint k X) (s : RationalPoint K Y)
    (q : Spec (.of K) ⟶ Spec (.of k)) (b : Y ⟶ X)
    (H : IsPullback q s.sectionMap r.sectionMap b)
    [IsDomain (X.presheaf.stalk (b s.point))]
    [IsDiscreteValuationRing (X.presheaf.stalk (b s.point))]
    [IsDomain s.localRing] [IsDiscreteValuationRing s.localRing]
    (π : X.presheaf.stalk (b s.point)) (hπ : Irreducible π) :
    Irreducible ((b.stalkMap s.point).hom π) := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  rw [← map_maximalIdeal_of_isPullback r s q b H, hπ.maximalIdeal_eq,
    Ideal.map_span, Set.image_singleton]

/-- The original function-field map preserves the normalized DVR order at
cartesian rational sections, including the zero function. -/
theorem order_functionFieldMap_of_isPullback [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y]
    (r : RationalPoint k X) (s : RationalPoint K Y)
    (q : Spec (.of K) ⟶ Spec (.of k)) (b : Y ⟶ X) [IsDominant b]
    (H : IsPullback q s.sectionMap r.sectionMap b)
    [IsDiscreteValuationRing (X.presheaf.stalk (b s.point))]
    [IsDiscreteValuationRing s.localRing] (f : X.functionField) :
    Y.ord (Scheme.functionFieldMap b f) s.point = X.ord f (b s.point) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (X.presheaf.stalk (b s.point))
  have hπ' := irreducible_stalkMap_of_isPullback r s q b H π hπ
  have hv := IsDiscreteValuationRing.valuation_map_of_map_irreducible
    (b.stalkMap s.point).hom hπ hπ' X.functionField Y.functionField
    (Scheme.functionFieldMap b) (Scheme.functionFieldMap_stalk b s.point) f
  have ho : Ring.ordFrac (Y.presheaf.stalk s.point) (Scheme.functionFieldMap b f) =
      Ring.ordFrac (X.presheaf.stalk (b s.point)) f := by
    rw [Ring.ordFrac_eq_valuation_inv, Ring.ordFrac_eq_valuation_inv, hv]
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one
      (OverField.Curve.Divisors.coheight_eq_one_of_dvr Y s.point),
    Scheme.ord_eq_ordHom_of_coheight_eq_one
      (OverField.Curve.Divisors.coheight_eq_one_of_dvr X (b s.point))]
  exact congrArg (fun v : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (v.unzeroD 1)) ho

end AlgebraicGeometry.Scheme.RationalPoint

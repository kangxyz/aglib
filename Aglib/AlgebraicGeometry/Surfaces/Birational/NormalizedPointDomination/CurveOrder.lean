/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveImage
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The actual generic curve stalk and its finite additive order

A contracted curve on a normal surface supplies its actual codimension-one
point and hence its actual DVR. Nonzero elements have finite natural order;
division by a nonzero nonunit factor strictly decreases that order. These
are arithmetic ingredients, not a supplied geometric termination oracle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

/-- The generic point of an actual contracted curve has actual stalk dimension
one. In particular the valuation ring is not an externally supplied model. -/
def contractedCurvePoint
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) (hY : NormalStalks Y)
    (hdX : topologicalKrullDim X ≤ 2) (C : IrreducibleCloseds X)
    (hC : C ∈ contractedCurves f) : CodimensionOnePoint X := by
  let c := C.isIrreducible.genericPoint
  have hc := C.isIrreducible.isGenericPoint_genericPoint C.isClosed
  have hnc : ¬ IsClosed ({c} : Set X) := by
    intro hclosed
    have hsingle : (C : Set X) = {c} := hc.def.symm.trans hclosed.closure_eq
    have hss : (C : Set X).Subsingleton := by
      rw [hsingle]
      exact Set.subsingleton_singleton
    let : Subsingleton (C : Set X) := ⟨fun a b ↦ Subtype.ext (hss a.property b.property)⟩
    have hd := topologicalKrullDim_zero_of_discreteTopology (C : Set X)
    rw [hC.1] at hd
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hd
  have hle : Order.coheight c ≤ 1 :=
    coheight_le_one_of_not_isClosed_singleton_of_dimension_le_two X hdX c hnc
  have hge : 1 ≤ Order.coheight c := by
    apply Order.one_le_iff_ne_zero.mpr
    intro hz
    have hm := Order.coheight_eq_zero.mp hz
    have hback : c ⤳ genericPoint X := hm (genericPoint_specializes c)
    have he : c = genericPoint X :=
      (Specializes.antisymm hback (genericPoint_specializes c)).eq
    exact genericPoint_not_mem_contractedCurve f hff hY C hC (he ▸ hc.mem)
  refine ⟨c, ?_⟩
  rw [ringKrullDim_stalk_eq_coheight, le_antisymm hle hge]
  rfl

end AlgebraicGeometry.Scheme.NormalizedPointDomination

namespace AlgebraicGeometry.Scheme.CodimensionOnePoint

universe u

variable {X : Scheme.{u}} (x : CodimensionOnePoint X)
  [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)]

/-- Natural additive order on the actual generic-curve DVR. Finiteness is
proved before this value is used in strict-decrease statements. -/
def finiteOrder (a : x.localRing) : ℕ := (IsDiscreteValuationRing.addVal x.localRing a).toNat

/-- A nonzero original stalk element has finite DVR valuation. -/
theorem addVal_ne_top_of_ne_zero {a : x.localRing} (ha : a ≠ 0) :
    IsDiscreteValuationRing.addVal x.localRing a ≠ ⊤ :=
  fun h ↦ ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)

/-- The actual finite order is positive on nonzero nonunits. -/
theorem finiteOrder_pos {a : x.localRing} (ha : a ≠ 0) (hu : ¬ IsUnit a) :
    0 < x.finiteOrder a :=
  ENat.toNat_pos (fun h ↦ hu (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h))
    (x.addVal_ne_top_of_ne_zero ha)

/-- Multiplicativity becomes additive equality of finite natural orders. -/
theorem finiteOrder_mul {a b : x.localRing} (ha : a ≠ 0) (hb : b ≠ 0) :
    x.finiteOrder (a * b) = x.finiteOrder a + x.finiteOrder b := by
  unfold finiteOrder
  rw [IsDiscreteValuationRing.addVal_mul,
    ENat.toNat_add (x.addVal_ne_top_of_ne_zero ha) (x.addVal_ne_top_of_ne_zero hb)]

/-- Dividing an actual nonzero stalk element by a nonunit factor strictly
lowers its finite order. The factorization equation is retained literally. -/
theorem finiteOrder_lt_of_factor
    {a a' d : x.localRing} (ha : a ≠ 0) (hd : ¬ IsUnit d) (h : a = a' * d) :
    x.finiteOrder a' < x.finiteOrder a := by
  have ha' : a' ≠ 0 := by
    intro hz
    apply ha
    rw [h, hz, zero_mul]
  have hd0 : d ≠ 0 := by
    intro hz
    apply ha
    rw [h, hz, mul_zero]
  rw [h, x.finiteOrder_mul ha' hd0]
  exact Nat.lt_add_of_pos_right (x.finiteOrder_pos hd0 hd)

/-- Strict decrease after applying the actual morphism stalk map into the
selected curve DVR. Locality retains nonunits; no substitute ring map or
valuation is used. -/
theorem finiteOrder_stalkMap_lt_of_factor
    {Y : Scheme.{u}} (f : X ⟶ Y)
    {a a' d : Y.presheaf.stalk (f x.val)}
    (ha : f.stalkMap x.val a ≠ 0) (hd : ¬ IsUnit d) (h : a = a' * d) :
    x.finiteOrder (f.stalkMap x.val a') < x.finiteOrder (f.stalkMap x.val a) := by
  apply x.finiteOrder_lt_of_factor ha
  · intro hu
    exact hd (isUnit_of_map_unit (f.stalkMap x.val).hom d hu)
  · rw [h, map_mul]

end AlgebraicGeometry.Scheme.CodimensionOnePoint

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveOrderTransport

/-!
# Simultaneous exceptional division through the original scheme square

The original stalk-map square transports the retained fraction. Division by
the actual nonunit exceptional generator preserves its equation and strictly
lowers both orders in the actual surviving curve DVR. No new fraction is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

/-- Exceptional division preserves the original retained fraction and lowers
both actual DVR orders. The only point transport is the native stalk
congruence supplied by the actual commuting scheme square. -/
theorem retained_fraction_division
    {Z Y S' S : Scheme.{u}} [IsIntegral Z] [IsIntegral Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian Y]
    [∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)]
    [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)]
    (x : CodimensionOnePoint Z) (f : Z ⟶ Y) (q : Y ⟶ S)
    (p : Z ⟶ S') (r : S' ⟶ S) (w : f ≫ q = p ≫ r)
    (hy : ringKrullDim (Y.presheaf.stalk (f x.val)) = 1)
    [IsIso (f.stalkMap x.val)]
    (u : Y.presheaf.stalk (f x.val))
    (a b : S.presheaf.stalk (q (f x.val)))
    (ha : q.stalkMap (f x.val) a ≠ 0) (hb : q.stalkMap (f x.val) b ≠ 0)
    (hfrac : u * q.stalkMap (f x.val) b = q.stalkMap (f x.val) a)
    (d a' b' : S'.presheaf.stalk (p x.val)) (hd : ¬ IsUnit d)
    (hdiva : r.stalkMap (p x.val)
      ((S.presheaf.stalkCongr (.of_eq (congrArg (fun k : Z ⟶ S ↦ k x.val) w))).hom a) =
        a' * d)
    (hdivb : r.stalkMap (p x.val)
      ((S.presheaf.stalkCongr (.of_eq (congrArg (fun k : Z ⟶ S ↦ k x.val) w))).hom b) =
        b' * d) :
    p.stalkMap x.val a' ≠ 0 ∧ p.stalkMap x.val b' ≠ 0 ∧
      f.stalkMap x.val u * p.stalkMap x.val b' = p.stalkMap x.val a' ∧
      x.finiteOrder (p.stalkMap x.val a') <
        CodimensionOnePoint.finiteOrder (X := Y) ⟨f x.val, hy⟩ (q.stalkMap (f x.val) a) ∧
      x.finiteOrder (p.stalkMap x.val b') <
        CodimensionOnePoint.finiteOrder (X := Y) ⟨f x.val, hy⟩ (q.stalkMap (f x.val) b) := by
  let τ := (S.presheaf.stalkCongr
    (.of_eq (congrArg (fun k : Z ⟶ S ↦ k x.val) w))).hom
  have hsquare : q.stalkMap (f x.val) ≫ f.stalkMap x.val =
      τ ≫ r.stalkMap (p x.val) ≫ p.stalkMap x.val := by
    rw [← Hom.stalkMap_comp, Hom.stalkMap_congr_hom _ _ w, Hom.stalkMap_comp]
  have he (c : S.presheaf.stalk (q (f x.val))) :
      f.stalkMap x.val (q.stalkMap (f x.val) c) =
        p.stalkMap x.val (r.stalkMap (p x.val) (τ c)) :=
    congrArg (fun k : S.presheaf.stalk (q (f x.val)) ⟶ Z.presheaf.stalk x.val ↦ k c)
      hsquare
  have hA : f.stalkMap x.val (q.stalkMap (f x.val) a) =
      p.stalkMap x.val a' * p.stalkMap x.val d := by
    rw [he, hdiva, map_mul]
  have hB : f.stalkMap x.val (q.stalkMap (f x.val) b) =
      p.stalkMap x.val b' * p.stalkMap x.val d := by
    rw [he, hdivb, map_mul]
  have hinj := (ConcreteCategory.bijective_of_isIso (f.stalkMap x.val)).1
  have hA0 : f.stalkMap x.val (q.stalkMap (f x.val) a) ≠ 0 :=
    (map_ne_zero_iff (f.stalkMap x.val).hom hinj).mpr ha
  have hB0 : f.stalkMap x.val (q.stalkMap (f x.val) b) ≠ 0 :=
    (map_ne_zero_iff (f.stalkMap x.val).hom hinj).mpr hb
  have hprodA : p.stalkMap x.val a' * p.stalkMap x.val d ≠ 0 := hA ▸ hA0
  have hprodB : p.stalkMap x.val b' * p.stalkMap x.val d ≠ 0 := hB ▸ hB0
  have hd0 : p.stalkMap x.val d ≠ 0 := (mul_ne_zero_iff.mp hprodA).2
  have hdu : ¬ IsUnit (p.stalkMap x.val d) :=
    fun hd' ↦ hd (isUnit_of_map_unit (p.stalkMap x.val).hom d hd')
  refine ⟨(mul_ne_zero_iff.mp hprodA).1, (mul_ne_zero_iff.mp hprodB).1, ?_, ?_, ?_⟩
  · apply mul_right_cancel₀ hd0
    have h := congrArg (fun c ↦ f.stalkMap x.val c) hfrac
    rw [map_mul, hA, hB] at h
    simpa only [mul_assoc] using h
  · rw [← x.finiteOrder_stalkMap f hy]
    exact x.finiteOrder_lt_of_factor hA0 hdu hA
  · rw [← x.finiteOrder_stalkMap f hy]
    exact x.finiteOrder_lt_of_factor hB0 hdu hB

end AlgebraicGeometry.Scheme.NormalizedPointDomination

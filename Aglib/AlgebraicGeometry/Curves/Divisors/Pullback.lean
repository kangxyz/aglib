/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.ClosedPoints
public import Aglib.AlgebraicGeometry.FunctionField.BaseChange
public import Aglib.AlgebraicGeometry.Curves.Divisors.RegularSections
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/


/-!
# Actual ramification-weighted divisor pullback

C2 functorial divisor construction, K2-018 `lem:k2018-geometric-exact-order`,
frozen basis `7f86e4a`. For an actual finite dominant morphism of integral
Noetherian schemes with closed DVR stalks, closed points map to closed
points. Ramification multiplicity is the local order of the actual generic
field-map image of a uniformizer. The DVR unit/uniformizer factorization
proves order scaling, positivity, and independence of uniformizer choice.
Finite fibres prove that pullback of a finite divisor has finite support.
Principal-divisor compatibility and descent to divisor classes are proved.

All maps use Scheme.functionFieldMap and the actual stalk maps. No ramification,
order-scaling, Picard pullback, or degree theorem is assumed. The line-bundle
pullback comparison and numerical degree scaling are separate consumers.
Source: Stacks Tag 0EXQ, Definition 15.113.1 and the DVR factorization used
throughout that section. The field-rank sum formula of Remark 15.113.6 is
not asserted or consumed in this module.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme.OverField.Curve.Divisors.Pullback
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f]

variable [hNoethX : AlgebraicGeometry.IsNoetherian X]
variable [hNoethY : AlgebraicGeometry.IsNoetherian Y]
variable [hFinite : IsFinite f]

variable [hDVRX : ∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable [hDVRY : ∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]

/-- A chosen irreducible element in the DVR stalk at the specified closed point. -/
def uniformizer (y : ClosedPoint Y) : Y.presheaf.stalk y.val :=
  (IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y.val)).choose

omit hNoethY in
-- Retain noetherianity of Y in the closed-point divisor pullback interface; choosing an
-- irreducible uniformizer only uses the specified DVR stalk.
@[nolint unusedArguments]
theorem uniformizer_irreducible [IsNoetherian Y] (y : ClosedPoint Y) :
    Irreducible (uniformizer y) :=
  (IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y.val)).choose_spec

/-- The chosen stalk uniformizer, viewed as a nonzero unit of the target function field. -/
def uniformizerUnit (y : ClosedPoint Y) : Y.functionFieldˣ :=
  Units.mk0 (algebraMap (Y.presheaf.stalk y.val) Y.functionField (uniformizer y))
    (by
      simpa using (IsFractionRing.injective (Y.presheaf.stalk y.val) Y.functionField).ne
        (uniformizer_irreducible y).ne_zero)

/-- Ramification multiplicity from the actual image of a local uniformizer. -/
def ramification (x : ClosedPoint X) : ℤ :=
  X.ord (Scheme.functionFieldUnitMap f (uniformizerUnit (closedPointMap f x)) : X.functionField)
    x.val

omit hNoethY hFinite hDVRY in
-- Retain the finite-map, target-noetherian and target-DVR conditions of divisor pullback; the
-- order-zero calculation only uses that stalk units map to stalk units.
@[nolint unusedArguments]
theorem mapped_stalk_unit_order [IsNoetherian Y] [IsFinite f]
    [∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
    (x : ClosedPoint X) (a : (Y.presheaf.stalk (f x.val))ˣ) :
    X.ord (Scheme.functionFieldMap f
      (algebraMap (Y.presheaf.stalk (f x.val)) Y.functionField a)) x.val = 0 := by
  let b := Units.map (f.stalkMap x.val).hom.toMonoidHom a
  let b' := Units.map (algebraMap (X.presheaf.stalk x.val) X.functionField).toMonoidHom b
  change X.ord _ x.val = 0
  rw [Scheme.functionFieldMap_stalk]
  exact (order_zero_iff_stalk_unit X x.val (coheight_eq_one_of_dvr X x.val) b').mpr
    ⟨b, b.isUnit, rfl⟩
theorem uniformizerUnit_order (y : ClosedPoint Y) :
    Y.ord (uniformizerUnit y : Y.functionField) y.val = 1 :=
  order_uniformizer Y y (coheight_eq_one_of_dvr Y y.val) (uniformizer y) (uniformizer_irreducible y)

theorem order_fieldMap (x : ClosedPoint X) (g : Y.functionFieldˣ) :
    X.ord (Scheme.functionFieldUnitMap f g : X.functionField) x.val =
      ramification f x * Y.ord (g : Y.functionField) (closedPointMap f x).val := by
  let y := closedPointMap f x
  obtain ⟨m, a, ha⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := Y.functionField) (uniformizer_irreducible y) g.ne_zero
  let a' := Units.map (algebraMap (Y.presheaf.stalk y.val) Y.functionField).toMonoidHom a
  have hg : g = a' * uniformizerUnit y ^ m := by
    apply Units.ext
    simpa [a', uniformizerUnit, Units.smul_def, Algebra.smul_def] using ha
  have hau : localOrder Y y (Additive.ofMul a') = 0 :=
    (order_zero_iff_stalk_unit Y y.val (coheight_eq_one_of_dvr Y y.val) a').mpr ⟨a, a.isUnit, rfl⟩
  have haf : localOrder X x (Additive.ofMul (Scheme.functionFieldUnitMap f a')) = 0 :=
    mapped_stalk_unit_order f x a
  have hpi : localOrder Y y (Additive.ofMul (uniformizerUnit y)) = 1 := uniformizerUnit_order y
  rw [hg, map_mul, map_zpow]
  change localOrder X x (Additive.ofMul (_ * _ ^ m)) =
    ramification f x * localOrder Y y (Additive.ofMul (a' * uniformizerUnit y ^ m))
  rw [ofMul_mul, ofMul_zpow, map_add, map_zsmul,
    ofMul_mul, ofMul_zpow, map_add, map_zsmul, haf, hau, hpi]
  change 0 + m * ramification f x = ramification f x * (0 + m * 1)
  ring

theorem ramification_nonneg (x : ClosedPoint X) : 0 ≤ ramification f x := by
  change 0 ≤ X.ord (Scheme.functionFieldMap f
    (algebraMap (Y.presheaf.stalk (f x.val)) Y.functionField (uniformizer (closedPointMap f x))))
      x.val
  rw [Scheme.functionFieldMap_stalk]
  exact (order_nonneg_iff_mem_stalk X x.val _).mpr ⟨f.stalkMap x.val (uniformizer (closedPointMap
    f x)), rfl⟩

omit hDVRX in
-- Retain the source-DVR condition in the ramification-weighted divisor pullback interface; the
-- support bound itself follows from finite fibres and the target divisor support.
@[nolint unusedArguments]
theorem finite_preimage_support
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] (D : Divisor Y) :
    (Function.support fun x : ClosedPoint X => ramification f x * D (closedPointMap f x)).Finite
      := by
  classical
  have hh : ((f : X → Y) ⁻¹' (Subtype.val '' (D.support : Set (ClosedPoint Y)))).Finite :=
    f.finite_preimage (D.support.finite_toSet.image Subtype.val)
  apply (hh.preimage_embedding ⟨Subtype.val, Subtype.val_injective⟩).subset
  intro x hx
  have hd : D (closedPointMap f x) ≠ 0 := fun hd => hx (by
    change ramification f x * D (closedPointMap f x) = 0
    rw [hd, mul_zero])
  exact ⟨closedPointMap f x, Finsupp.mem_support_iff.mpr hd, rfl⟩

/-- Actual ramification-weighted pullback of closed-point divisors. -/
def divisorPullback : Divisor Y →+ Divisor X where
  toFun D := Finsupp.ofSupportFinite
    (fun x => ramification f x * D (closedPointMap f x)) (finite_preimage_support f D)
  map_zero' := by ext x; exact mul_zero _
  map_add' D E := by ext x; exact mul_add _ _ _

@[simp] theorem divisorPullback_apply (D : Divisor Y) (x : ClosedPoint X) :
    divisorPullback f D x = ramification f x * D (closedPointMap f x) := rfl

/-- The actual generic field pullback and the actual divisor pullback commute. -/
theorem divisorPullback_principal (g : Y.functionFieldˣ) :
    divisorPullback f (principal Y (Additive.ofMul g)) =
      principal X (Additive.ofMul (Scheme.functionFieldUnitMap f g)) := by
  ext x
  exact (order_fieldMap f x g).symm
theorem ramification_pos (x : ClosedPoint X) : 0 < ramification f x := by
  apply lt_of_le_of_ne (ramification_nonneg f x)
  intro hz
  have ho : X.ord (Scheme.functionFieldUnitMap f (uniformizerUnit (closedPointMap f x)) :
    X.functionField) x.val = 0 := hz.symm
  obtain ⟨a, ha, hea⟩ := (order_zero_iff_stalk_unit X x.val (coheight_eq_one_of_dvr X x.val) _).mp
    ho
  have he : a = f.stalkMap x.val (uniformizer (closedPointMap f x)) := by
    apply IsFractionRing.injective (X.presheaf.stalk x.val) X.functionField
    exact hea.trans (Scheme.functionFieldMap_stalk f x.val _)
  apply (uniformizer_irreducible (closedPointMap f x)).not_isUnit
  exact isUnit_of_map_unit (f.stalkMap x.val).hom _ (he ▸ ha)

/-- The multiplicity is independent of the chosen uniformizer. -/
theorem ramification_eq_order_of_order_one (x : ClosedPoint X) (g : Y.functionFieldˣ)
    (hg : Y.ord (g : Y.functionField) (closedPointMap f x).val = 1) :
    ramification f x = X.ord (Scheme.functionFieldUnitMap f g : X.functionField) x.val := by
  rw [order_fieldMap, hg, mul_one]

/-- Descended pullback on the actual divisor-class quotient. -/
def classPullback : (Divisor Y ⧸ (principal Y).range) →+ (Divisor X ⧸ (principal X).range) :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (principal X).range).comp (divisorPullback f)) (by
    rintro D ⟨g, rfl⟩
    change QuotientAddGroup.mk (divisorPullback f (principal Y g)) = 0
    have h := divisorPullback_principal f g.toMul
    change divisorPullback f (principal Y g) = _ at h
    rw [h]
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨Additive.ofMul (Scheme.functionFieldUnitMap f
      g.toMul), rfl⟩)

@[simp] theorem classPullback_mk (D : Divisor Y) :
    classPullback f (QuotientAddGroup.mk D) = QuotientAddGroup.mk (divisorPullback f D) := rfl
end AlgebraicGeometry.Scheme.OverField.Curve.Divisors.Pullback

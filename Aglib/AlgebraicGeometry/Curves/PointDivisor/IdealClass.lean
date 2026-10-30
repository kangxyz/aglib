/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.FiniteCartierDegree
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorIndependence
public import Aglib.AlgebraicGeometry.RationalPoint.SmoothCurve
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Length

/-!
# The divisor and Picard class of a rational-point ideal

On an integral Noetherian scheme with DVR closed stalks, the ideal inclusion of a rational
point has divisor that point, in every rational trivialization. In dimension at most one,
the dual ideal therefore has the point's native divisor-to-Picard class. These are the local
length and divisor-class arguments formerly private in `PointDivisor.PoleFunctions`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.FiniteCartierDegree

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

section PointClass

variable {k : Type u} [Field k]

-- Retain the original chart conversion behavior at this declaration only.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ideal divisor of a rational point has coefficient one at the point. -/
private theorem pointMapDivisor_coefficient
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    [∀ x : Scheme.ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk x.val)]
    (r : Scheme.RationalPoint k Y)
    (hI : IsLocallyRankOne Y (Scheme.Hom.idealModule r.sectionMap))
    (U₀ : Y.Opens) [Nonempty U₀]
    (e₀ : (Scheme.Hom.idealModule r.sectionMap).over U₀ ≅
      SheafOfModules.unit (Y.ringCatSheaf.over U₀)) :
    MapDivisors.mapDivisor Y ⟨Scheme.Hom.idealModule r.sectionMap, hI⟩
      (Scheme.Hom.idealInclusion r.sectionMap) U₀ e₀ ⟨r.point, r.point_isClosed⟩ = 1 := by
  let : IsClosedImmersion r.sectionMap := r.section_isClosedImmersion
  let I : LineBundle Y := ⟨Scheme.Hom.idealModule r.sectionMap, hI⟩
  let c := Picard.RationalTrivialization.localChart Y I.val hI r.point
  let W := c.1
  let d := c.2.val
  have hx : r.point ∈ W := c.2.property
  let : Nonempty W := ⟨⟨r.point, hx⟩⟩
  let R := r.localRing
  let a : R := Y.presheaf.germ W r.point hx
    ((Scheme.Hom.idealInclusion r.sectionMap).app W (chartGenerator Y I.val W d))
  have ha : a ≠ 0 := by
    simpa only [a, map_zero] using (germ_injective_of_isIntegral Y r.point hx).ne
      (MapDivisors.generator_image_ne_zero Y I (Scheme.Hom.idealInclusion r.sectionMap) W d)
  have hspan : RingHom.ker (r.sectionMap.stalkMap (IsLocalRing.closedPoint k)).hom =
      Ideal.span {a} :=
    CartierLocal.ideal_stalkKernel_eq_span_generator Y r.sectionMap hI W d
      (IsLocalRing.closedPoint k) hx
  have hev : Function.Surjective r.evaluation := by
    intro t
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
      (stalkClosedPointIso (.of k)).hom).surjective t
    obtain ⟨b, hb⟩ := r.sectionMap.stalkMap_surjective (IsLocalRing.closedPoint k) z
    refine ⟨b, ?_⟩
    change (stalkClosedPointIso (.of k)).hom
      (r.sectionMap.stalkMap (IsLocalRing.closedPoint k) b) = t
    rw [hb, hz]
  have hker : RingHom.ker r.evaluation =
      RingHom.ker (r.sectionMap.stalkMap (IsLocalRing.closedPoint k)).hom := by
    ext b
    change (stalkClosedPointIso (.of k)).hom
        (r.sectionMap.stalkMap (IsLocalRing.closedPoint k) b) = 0 ↔
      r.sectionMap.stalkMap (IsLocalRing.closedPoint k) b = 0
    constructor
    · intro h
      exact (ConcreteCategory.bijective_of_isIso
        (stalkClosedPointIso (.of k)).hom).injective
        (h.trans (map_zero _).symm)
    · intro h
      rw [h, map_zero]
  have hm : (Ideal.span {a}).IsMaximal := by
    rw [← hspan, ← hker]
    exact RingHom.ker_isMaximal_of_surjective r.evaluation hev
  have : IsSimpleModule R (R ⧸ Ideal.span {a}) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨Ideal.span {a}, hm, ⟨LinearEquiv.refl R _⟩⟩
  have hlen : Module.length R (R ⧸ Ideal.span {a}) = 1 := Module.length_eq_one R _
  let : IsDiscreteValuationRing r.localRing :=
    inferInstanceAs (IsDiscreteValuationRing
      (Y.presheaf.stalk (⟨r.point, r.point_isClosed⟩ : Scheme.ClosedPoint Y).val))
  have hcodim := Divisors.coheight_eq_one_of_dvr Y r.point
  rw [MapDivisors.mapDivisor_coefficient Y I (Scheme.Hom.idealInclusion r.sectionMap)
    U₀ e₀ W d ⟨r.point, r.point_isClosed⟩ hx]
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField Y hx]
  change Y.ord (algebraMap R Y.functionField a) r.point = 1
  rw [Picard.Degree.ProductFormula.order_stalk_element Y r.point hcodim a ha]
  change ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℤ) = 1
  rw [hlen]
  rfl

-- Retain the original chart conversion behavior at this declaration only.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ideal divisor of a rational point is the point divisor. -/
theorem pointMapDivisor_eq_single
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    [∀ x : Scheme.ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk x.val)]
    (r : Scheme.RationalPoint k Y)
    (hI : IsLocallyRankOne Y (Scheme.Hom.idealModule r.sectionMap))
    (U₀ : Y.Opens) [Nonempty U₀]
    (e₀ : (Scheme.Hom.idealModule r.sectionMap).over U₀ ≅
      SheafOfModules.unit (Y.ringCatSheaf.over U₀)) :
    MapDivisors.mapDivisor Y ⟨Scheme.Hom.idealModule r.sectionMap, hI⟩
      (Scheme.Hom.idealInclusion r.sectionMap) U₀ e₀ =
      Finsupp.single (⟨r.point, r.point_isClosed⟩ : Scheme.ClosedPoint Y) 1 := by
  classical
  let : IsClosedImmersion r.sectionMap := r.section_isClosedImmersion
  ext x
  by_cases hx : x.val = r.point
  · have heq : x = (⟨r.point, r.point_isClosed⟩ : Scheme.ClosedPoint Y) := Subtype.ext hx
    subst x
    simpa only [Finsupp.single_eq_same] using pointMapDivisor_coefficient Y r hI U₀ e₀
  · have hnot : x.val ∉ Set.range r.sectionMap := by
      rintro ⟨y, hy⟩
      have heq : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      exact hx (hy.symm.trans (congrArg r.sectionMap heq))
    rw [CartierLocal.ideal_mapDivisor_eq_zero_of_not_mem_range Y r.sectionMap hI U₀ e₀ x hnot]
    exact (Finsupp.single_eq_of_ne (fun heq ↦ hx (congrArg Subtype.val heq))).symm

-- Retain the original chart conversion behavior at this declaration only.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On an integral Noetherian scheme of dimension at most one with discrete valuation rings at
its closed points, the dual of the ideal of a rational point has the class of its point
divisor. -/
theorem idealDual_class_eq_point
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    [∀ x : Scheme.ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk x.val)]
    (r : Scheme.RationalPoint k Y)
    (hI : IsLocallyRankOne Y (Scheme.Hom.idealModule r.sectionMap))
    (hdim : topologicalKrullDim Y ≤ 1) :
    classOf Y (dualLineBundle Y ⟨Scheme.Hom.idealModule r.sectionMap, hI⟩) =
      DivisorClass.divisorToPicard Y hdim
        (Finsupp.single (⟨r.point, r.point_isClosed⟩ : Scheme.ClosedPoint Y) 1) := by
  let I : LineBundle Y := ⟨Scheme.Hom.idealModule r.sectionMap, hI⟩
  let c := Picard.RationalTrivialization.localChart Y I.val hI (genericPoint Y)
  let U₀ := c.1
  let e₀ := c.2.val
  let : Nonempty U₀ := ⟨⟨genericPoint Y, c.2.property⟩⟩
  let DI := Picard.RationalTrivialization.divisor Y I.val U₀ e₀ hI
  have hIclass : classOf Y I = classOf Y (DivisorClass.divisorLineBundle Y hdim DI) :=
    (class_eq_iff Y I (DivisorClass.divisorLineBundle Y hdim DI)).mpr
      ⟨DivisorInverse.toDivisorIso Y I.val hI U₀ e₀ hdim⟩
  have hmap : DivisorClass.divisorToPicard Y hdim
        (MapDivisors.mapDivisor Y I (Scheme.Hom.idealInclusion r.sectionMap) U₀ e₀) =
      -classOf Y I := by
    rw [MapDivisors.mapDivisor, map_sub, DivisorClass.divisorToPicard_principal, zero_sub]
    change -classOf Y (DivisorClass.divisorLineBundle Y hdim DI) = -classOf Y I
    exact congrArg Neg.neg hIclass.symm
  calc
    _ = -classOf Y I := classOf_dual Y I
    _ = _ := hmap.symm
    _ = _ := congrArg (DivisorClass.divisorToPicard Y hdim)
      (pointMapDivisor_eq_single Y r hI U₀ e₀)

end PointClass

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

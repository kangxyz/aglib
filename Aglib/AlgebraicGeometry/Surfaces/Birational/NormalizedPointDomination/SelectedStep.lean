/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.FractionTransform
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveSurvival
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.ExceptionalGenerator
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.RetainedFraction

/-!
# The actual decreasing retained fraction at a normalized point step

For an actual surviving generic curve point, the literal normalized point
blowup produces the shared exceptional generator. Finite residue extension,
original-map transcendence transport, and exceptional division produce a new
retained fraction with strictly smaller orders. No factorization or measure
decrease is supplied as an input.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u
open Blowup

/-- A surviving selected generic curve point at a literal normalized-point
step has a retained residue-transcendental fraction whose numerator and
denominator both have smaller actual DVR order. -/
theorem exists_decreasing_fraction_at_normalizedPoint
    {Z Y S : Scheme.{u}} [IsIntegral Z] [IsIntegral Y] [IsIntegral S]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian Y]
    [∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)]
    [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)]
    (x : S) (hx : IsClosed ({x} : Set S)) (hne : x ≠ genericPoint S)
    [LocallyOfFiniteType (normalizedPointBlowupMap S x hx hne)]
    (c : CodimensionOnePoint Z) (f : Z ⟶ Y) (q : Y ⟶ S)
    (p : Z ⟶ normalizedPointBlowup S x hx hne)
    (w : f ≫ q = p ≫ normalizedPointBlowupMap S x hx hne)
    (hy : ringKrullDim (Y.presheaf.stalk (f c.val)) = 1)
    [IsIso (f.stalkMap c.val)]
    (hcenter : q (f c.val) = x) (hclosed : IsClosed ({p c.val} : Set _))
    (u : Y.presheaf.stalk (f c.val)) (a b : S.presheaf.stalk (q (f c.val)))
    (ha : q.stalkMap (f c.val) a ≠ 0) (hb : q.stalkMap (f c.val) b ≠ 0)
    (hfrac : u * q.stalkMap (f c.val) b = q.stalkMap (f c.val) a)
    (hu : letI := (q.residueFieldMap (f c.val)).hom.toAlgebra
      Transcendental (S.residueField (q (f c.val))) (Y.residue (f c.val) u)) :
    letI := (p.residueFieldMap c.val).hom.toAlgebra
    ∃ a' b' : (normalizedPointBlowup S x hx hne).presheaf.stalk (p c.val),
      a' ∈ IsLocalRing.maximalIdeal _ ∧ b' ∈ IsLocalRing.maximalIdeal _ ∧
      p.stalkMap c.val a' ≠ 0 ∧ p.stalkMap c.val b' ≠ 0 ∧
      f.stalkMap c.val u * p.stalkMap c.val b' = p.stalkMap c.val a' ∧
      Transcendental ((normalizedPointBlowup S x hx hne).residueField (p c.val))
        (Z.residue c.val (f.stalkMap c.val u)) ∧
      c.finiteOrder (p.stalkMap c.val a') <
        CodimensionOnePoint.finiteOrder (X := Y) ⟨f c.val, hy⟩ (q.stalkMap (f c.val) a) ∧
      c.finiteOrder (p.stalkMap c.val b') <
        CodimensionOnePoint.finiteOrder (X := Y) ⟨f c.val, hy⟩ (q.stalkMap (f c.val) b) := by
  let r := normalizedPointBlowupMap S x hx hne
  let : Algebra ((normalizedPointBlowup S x hx hne).residueField (p c.val))
      (Z.residueField c.val) := (p.residueFieldMap c.val).hom.toAlgebra
  have hwpoint : q (f c.val) = r (p c.val) :=
    congrArg (fun k : Z ⟶ S ↦ k c.val) w
  let τ := (S.presheaf.stalkCongr (.of_eq hwpoint)).hom
  have hmax := fraction_mem_maximalIdeal_of_transcendental_residue q (f c.val) u a b hu hfrac
  have hτ (v : S.presheaf.stalk (q (f c.val)))
      (hv : v ∈ IsLocalRing.maximalIdeal _) : τ v ∈ IsLocalRing.maximalIdeal _ := by
    let e := RingEquiv.ofBijective τ.hom (ConcreteCategory.bijective_of_isIso τ)
    change ¬ IsUnit (e v)
    exact fun he ↦ hv ((MulEquiv.isUnit_map e).mp he)
  obtain ⟨d, a', b', _, hdu, hdiva, hdivb⟩ :=
    normalizedPoint_stalk_factor_pair S x hx hne (p c.val)
      (hwpoint.symm.trans hcenter) (τ a) (τ b) (hτ a hmax.1) (hτ b hmax.2)
  obtain ⟨ha'0, hb'0, hfrac', hordA, hordB⟩ :=
    retained_fraction_division c f q p r w hy u a b ha hb hfrac d a' b' hdu hdiva hdivb
  have htransOld := transcendental_residue_stalkMap f q c.val u hu
  have htransComp :
      letI := ((p ≫ r).residueFieldMap c.val).hom.toAlgebra
      Transcendental (S.residueField ((p ≫ r) c.val))
        (Z.residue c.val (f.stalkMap c.val u)) := by
    rw [← w]
    exact htransOld
  have htransNew := transcendental_residueFieldMap_of_closedPoint p r c.val hclosed
    (Z.residue c.val (f.stalkMap c.val u)) htransComp
  have hmaxNew := fraction_mem_maximalIdeal_of_transcendental_residue p c.val
    (f.stalkMap c.val u) a' b' htransNew hfrac'
  exact ⟨a', b', hmaxNew.1, hmaxNew.2, ha'0, hb'0, hfrac', htransNew, hordA, hordB⟩

end AlgebraicGeometry.Scheme.NormalizedPointDomination

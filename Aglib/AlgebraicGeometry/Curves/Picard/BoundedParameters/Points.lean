/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.BoundedParameters
public import Aglib.AlgebraicGeometry.Curves.Picard.TorsionSections
public import Aglib.AlgebraicGeometry.Curves.Abel.PointClasses
public import Mathlib.Algebra.BigOperators.Fin

/-! # Ordered rational-point parameters for degree-zero Picard classes

An effective divisor of degree `n` over algebraically closed constants is the
sum of an actual `Fin n` tuple of closed points, with repetitions. The native
closed-point/rational-point construction then gives an ordered tuple of actual
sections of the structure morphism. Combining this with Riemann--Roch bounds
the tuple length by the coherent genus, including the empty tuple in genus zero.

The final comparison uses the actual positive point line bundles in every
genus. There is no symmetric-product or Picard-scheme representability claim.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard

open DivisorClass Degree

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An effective degree-`n` divisor is a sum of exactly `n` actual closed
points, counted with multiplicity. The zero-degree case uses the empty tuple. -/
theorem effective_divisor_eq_sum_points
    (Y : Scheme.{u}) (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (n : ℕ) (D : Divisor Y) (heff : ∀ x, 0 ≤ D x)
    (hdeg : degDiv Y p D = (n : ℤ)) :
    ∃ s : Fin n → ClosedPoint Y, D = ∑ i, Finsupp.single (s i) 1 := by
  classical
  induction n generalizing D with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simpa using TorsionSections.effective_degree_zero Y p D heff hdeg
  | succ n ih =>
    have hpos : ∃ x : ClosedPoint Y, 0 < D x := by
      by_contra! h
      have hzero : D = 0 := by
        ext x
        exact le_antisymm (h x) (heff x)
      rw [hzero, map_zero] at hdeg
      omega
    obtain ⟨x, hx⟩ := hpos
    have heff' : ∀ y : ClosedPoint Y, 0 ≤ (D - Finsupp.single x 1 : Divisor Y) y := by
      intro y
      by_cases hy : y = x
      · subst y
        simp only [Finsupp.sub_apply, Finsupp.single_eq_same]
        omega
      · simpa only [Finsupp.sub_apply, Finsupp.single_eq_of_ne hy, sub_zero] using heff y
    have hdeg' : degDiv Y p (D - Finsupp.single x 1) = (n : ℤ) := by
      rw [map_sub, hdeg, degDiv_single, weight_eq_one]
      omega
    obtain ⟨s, hs⟩ := ih (D - Finsupp.single x 1) heff' hdeg'
    refine ⟨Fin.cons x s, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hs]
    abel

variable (X : FScheme k) [IsIntegral X.left] [IsNoetherian X.left] [IsProper X.hom]
  [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]

/-- Degree-zero actual Picard classes are sums of exactly `g` actual point
class differences from a fixed point, where `g` is the coherent genus. -/
theorem exists_genus_tuple_of_picardDegree_eq_zero
    (hdim : topologicalKrullDim X.left = 1) (o : ClosedPoint X.left)
    (L : PicardGroup X.left)
    (hL : picardDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim) L = 0) :
    ∃ s : Fin (coherentGenus k X) → ClosedPoint X.left,
      L = ∑ i, (divisorToPicard X.left hdim.le (Finsupp.single (s i) 1) -
        divisorToPicard X.left hdim.le (Finsupp.single o 1)) := by
  classical
  obtain ⟨E, heff, hdeg, hE⟩ := exists_effective_degree_genus_of_picardDegree_eq_zero
    X hdim o L hL
  obtain ⟨s, hs⟩ := effective_divisor_eq_sum_points X.left X.hom
    (coherentGenus k X) E heff hdeg
  have ho : divisorToPicard X.left hdim.le (Finsupp.single o (coherentGenus k X : ℤ)) =
      coherentGenus k X • divisorToPicard X.left hdim.le (Finsupp.single o 1) := by
    rw [← map_nsmul]
    congr 1
    simp only [Finsupp.smul_single, nsmul_eq_mul, mul_one]
  refine ⟨s, ?_⟩
  rw [hE, hs, map_sub, map_sum, ho, Finset.sum_sub_distrib]
  simp

/-- The ordered bounded parameters can be chosen as actual rational sections
of the original structure morphism, not merely geometric points of a model. -/
theorem exists_rationalPoint_genus_tuple_of_picardDegree_eq_zero
    (hdim : topologicalKrullDim X.left = 1)
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (L : PicardGroup X.left)
    (hL : picardDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim) L = 0) :
    ∃ s : Fin (coherentGenus k X) → {s : Spec (.of k) ⟶ X.left // s ≫ X.hom = 𝟙 _},
      L = ∑ i, (divisorToPicard X.left hdim.le
        (PointDivisor.pointDivisor X (s i).val (s i).property 1) -
        divisorToPicard X.left hdim.le (PointDivisor.pointDivisor X o ho 1)) := by
  classical
  obtain ⟨s, hs⟩ := exists_genus_tuple_of_picardDegree_eq_zero X hdim
    (PointDivisor.closedPoint X o ho) L hL
  let t : Fin (coherentGenus k X) →
      {s : Spec (.of k) ⟶ X.left // s ≫ X.hom = 𝟙 _} := fun i =>
    ⟨pointOfClosedPoint X.hom (s i).val (s i).property,
      pointOfClosedPoint_comp X.hom (s i).val (s i).property⟩
  have ht (i : Fin (coherentGenus k X)) :
      PointDivisor.closedPoint X (t i).val (t i).property = s i := by
    apply Subtype.ext
    exact pointOfClosedPoint_apply X.hom (s i).val (s i).property _
  refine ⟨t, hs.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PointDivisor.pointDivisor, ht]

/-- On a smooth proper geometrically connected curve, the bounded tuple uses
the original positive point line bundles, with the all-genus point-class comparison. -/
theorem exists_positivePoint_genus_tuple_of_picardDegree_eq_zero
    (hX : Properties X) (hdim : topologicalKrullDim X.left = 1)
    (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (L : PicardGroup X.left)
    (hL : picardDegree X.left X.hom hdim.le
      (properCurveProductFormula k X.left X.hom hdim) L = 0) :
    ∃ s : Fin (coherentGenus k X) → {s : Spec (.of k) ⟶ X.left // s ≫ X.hom = 𝟙 _},
      L = ∑ i, (classOf X.left (PointDivisor.positiveLineBundle X hX
        (s i).val (s i).property) -
        classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) := by
  obtain ⟨s, hs⟩ := exists_rationalPoint_genus_tuple_of_picardDegree_eq_zero X hdim o ho L hL
  refine ⟨s, hs.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i hi
  rw [PointDivisor.positiveLineBundle_class_eq_pointDivisor X hX (s i).val
    (s i).property hdim.le,
    PointDivisor.positiveLineBundle_class_eq_pointDivisor X hX o ho hdim.le]

end AlgebraicGeometry.Scheme.OverField.Curve.Picard

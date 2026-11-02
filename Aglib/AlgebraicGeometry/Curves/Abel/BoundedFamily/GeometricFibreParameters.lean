/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.Parameters

/-!
# Geometric-fibre classes in the original relative bounded parameter family

Apply the original genus-length point-tuple theorem on a geometric fibre, and
project its points to the original family. The canonical graph construction
recovers exactly the original fibre points. Thus the actual relative graph
line bundle realizes every degree-zero class of that fibre. Positive torsion
has degree zero by the original degree homomorphism into the torsion-free integers.

The length is the genus of the specified fibre. This does not assert a uniform
genus on the base, a relative Picard properness theorem, or finite torsion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {S Y : Scheme.{u}} (p : Y ⟶ S) [SmoothOfRelativeDimension 1 p]
  [IsSeparated p] (o : S ⟶ Y) (ho : o ≫ p = 𝟙 S)
  {K : Type u} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S)
  (hY : Properties (Over.mk (pullback.snd p t)))

/-- A degree-zero class on the given geometric fibre is realized by a point
of the original relative parameter scheme, with the same fibre's genus as length. -/
theorem exists_parameter_over_geometricPoint_of_degree_zero
    (L : PicardGroup (pullback p t))
    (hL : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      (Over.mk (pullback.snd p t)) hY L = 0) :
    ∃ a : Spec (.of K) ⟶ (parameter p (coherentGenus K (Over.mk (pullback.snd p t)))).left,
      ∃ ha : a ≫ (parameter p (coherentGenus K (Over.mk (pullback.snd p t)))).hom = t,
        pullbackClass (Hom.familyMap p
          (parameter p (coherentGenus K (Over.mk (pullback.snd p t)))).hom t a ha)
          (classOf _ (lineBundle p o ho (coherentGenus K (Over.mk (pullback.snd p t))))) = L := by
  let C : FScheme K := Over.mk (pullback.snd p t)
  let : IsIntegral C.left := PointDivisor.isIntegral_of_properties C hY
  let : IsNoetherian C.left := curveProperties_isNoetherian hY
  let : IsProper C.hom := hY.proper
  let (x : ClosedPoint C.left) := PointDivisor.isDiscreteValuationRing_stalk C hY x
  have hd : topologicalKrullDim C.left = 1 := curveProperties_dimension smoothFieldDimension hY
  let z := Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho])
  have hz : z ≫ C.hom = 𝟙 _ := Hom.graph_snd p t _ _
  have hdeg : Picard.Degree.picardDegree C.left C.hom hd.le
      (Picard.Degree.properCurveProductFormula K C.left C.hom hd) L = 0 := hL
  obtain ⟨s, hs⟩ := Picard.exists_rationalPoint_genus_tuple_of_picardDegree_eq_zero
    C hd z hz L hdeg
  let a : Fin (coherentGenus K C) → (Spec (.of K) ⟶ Y) :=
    fun j => (s j).val ≫ pullback.fst p t
  have ha (j : Fin (coherentGenus K C)) : a j ≫ p = t := by
    dsimp only [a]
    have hsnd : (s j).val ≫ pullback.snd p t = 𝟙 _ := (s j).property
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd, Category.id_comp]
  have hg (j : Fin (coherentGenus K C)) : Hom.graph p t (a j) (ha j) = (s j).val := by
    apply pullback.hom_ext
    · exact Hom.graph_fst p t (a j) (ha j)
    · exact (Hom.graph_snd p t (a j) (ha j)).trans (s j).property.symm
  refine ⟨parameterPoint p t a ha, parameterPoint_over p t a ha, ?_⟩
  rw [lineBundle_class_at_field_tuple p o ho t a ha hY hd.le, hs]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_sub, hg]
  rfl

include hY in
/-- Positive-level torsion on the same geometric fibre has an actual parameter;
no degree-zero hypothesis is retained. -/
theorem exists_parameter_over_geometricPoint_of_torsion
    (L : PicardGroup (pullback p t)) (n : ℕ) (hn : 0 < n) (hL : n • L = 0) :
    ∃ a : Spec (.of K) ⟶ (parameter p (coherentGenus K (Over.mk (pullback.snd p t)))).left,
      ∃ ha : a ≫ (parameter p (coherentGenus K (Over.mk (pullback.snd p t)))).hom = t,
        pullbackClass (Hom.familyMap p
          (parameter p (coherentGenus K (Over.mk (pullback.snd p t)))).hom t a ha)
          (classOf _ (lineBundle p o ho (coherentGenus K (Over.mk (pullback.snd p t))))) = L := by
  apply exists_parameter_over_geometricPoint_of_degree_zero p o ho t hY L
  let d := curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
    (Over.mk (pullback.snd p t)) hY
  have h := congrArg d hL
  rw [map_nsmul, map_zero] at h
  exact (nsmul_right_injective (ne_of_gt hn)) h

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

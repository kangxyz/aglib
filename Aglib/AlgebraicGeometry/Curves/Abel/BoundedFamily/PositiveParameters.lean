/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.PositivePoints
public import Aglib.AlgebraicGeometry.Curves.Picard.BoundedParameters.Points

/-!
# Actual positive parameters for effective divisors on geometric fibres

An effective divisor on the native field fibre decomposes into actual
rational points. Compose these with the original first projection, take
the existing ordered parameter lift, and recover precisely those points
as its original graphs. The whole positive-family specialization then
has the original divisor class. The base scheme and field structural map
are retained, and no new Picard representative is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

open Divisors Picard Picard.DivisorClass Picard.Degree

variable {S X : Scheme.{u}} (p : X ⟶ S)
  [SmoothOfRelativeDimension 1 p] [IsSeparated p]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every effective degree-n divisor on an algebraically closed field
fibre is realized by an actual parameter of the original positive family. -/
theorem exists_parameter_positive_class_of_effective_divisor
    {K : Type u} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S)
    (hY : Properties (Over.mk (pullback.snd p t)))
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) p t) ≤ 1)
    (n : ℕ) (D : Divisor (pullback p t)) (heff : ∀ x, 0 ≤ D x)
    (hdeg : degDiv (pullback p t) (pullback.snd p t) D = (n : ℤ)) :
    let Y : FScheme K := Over.mk (pullback.snd p t)
    letI := PointDivisor.isIntegral_of_properties Y hY
    letI := curveProperties_isNoetherian hY
    letI (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
    ∃ (a : Spec (.of K) ⟶ (parameter p n).left) (ha : a ≫ (parameter p n).hom = t),
      pullbackClass (Hom.familyMap p (parameter p n).hom t a ha)
        (classOf _ (positiveFamilyLineBundle p n)) = divisorToPicard Y.left hdim D := by
  classical
  let Y : FScheme K := Over.mk (pullback.snd p t)
  let := hY.proper
  let := PointDivisor.isIntegral_of_properties Y hY
  let := curveProperties_isNoetherian hY
  let (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
  obtain ⟨s, hs⟩ := effective_divisor_eq_sum_points Y.left Y.hom n D heff hdeg
  let q : Fin n → {q : Spec (.of K) ⟶ Y.left // q ≫ Y.hom = 𝟙 _} := fun i =>
    ⟨pointOfClosedPoint Y.hom (s i).val (s i).property,
      pointOfClosedPoint_comp Y.hom (s i).val (s i).property⟩
  let r : Fin n → (Spec (.of K) ⟶ X) := fun i => (q i).val ≫ pullback.fst p t
  have hr (i : Fin n) : r i ≫ p = t := by
    have hqi : (q i).val ≫ pullback.snd p t = 𝟙 _ := (q i).property
    dsimp only [r]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hqi, Category.id_comp]
  have hgraph (i : Fin n) : Hom.graph p t (r i) (hr i) = (q i).val := by
    apply pullback.hom_ext
    · exact Hom.graph_fst p t (r i) (hr i)
    · exact (Hom.graph_snd p t (r i) (hr i)).trans (q i).property.symm
  have hclosed (i : Fin n) : PointDivisor.closedPoint Y
      (Hom.graph p t (r i) (hr i)) (Hom.graph_snd p t (r i) (hr i)) = s i := by
    apply Subtype.ext
    change Hom.graph p t (r i) (hr i) (IsLocalRing.closedPoint K) = (s i).val
    rw [hgraph]
    exact pointOfClosedPoint_apply Y.hom (s i).val (s i).property _
  let a := parameterPoint p t r hr
  refine ⟨a, parameterPoint_over p t r hr, ?_⟩
  refine (positiveFamilyLineBundle_class_at_field_tuple p t r hr hY hdim).trans ?_
  rw [hs, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (divisorToPicard Y.left hdim)
    (congrArg (fun x : ClosedPoint Y.left => Finsupp.single x (1 : ℤ)) (hclosed i))

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

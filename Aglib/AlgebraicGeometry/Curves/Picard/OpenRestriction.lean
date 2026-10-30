/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Group.Subgroup.KerSurjective
public import Aglib.AlgebraicGeometry.Curves.Picard.PointDegree
public import Aglib.AlgebraicGeometry.Curves.PointDivisor.IdealClass
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenRestriction
public import Aglib.AlgebraicGeometry.Stalk.OpenSmoothCurveDVR
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Picard restriction to an open curve

The original Picard pullback is surjective for every open immersion into a smooth proper
geometrically connected curve over an algebraically closed field. If the open misses a closed
point, degree-zero classes already surject. The proof is divisor restriction followed by
generic degree correction
(Milne, Lectures on Étale Cohomology v2.21, Proposition 14.12, p. 97; Stacks, Tag 03RR).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

section Complement

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]

include hX j in
/-- An open subscheme of the curve is Noetherian. -/
theorem isNoetherian_of_isOpenImmersion : IsNoetherian U := by
  have := curveProperties_isNoetherian hX
  have : NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  exact { toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion j
          toCompactSpace := inferInstance }

include hX in
/-- An open subscheme of the curve is smooth of relative dimension one over `k`. -/
theorem smoothOfRelativeDimension_one_of_isOpenImmersion :
    SmoothOfRelativeDimension 1 (j ≫ X.hom) := by
  have := hX.smooth
  have h := smoothOfRelativeDimension_comp 0 1 j X.hom
  simpa only [Nat.zero_add] using h

include hX j in
/-- An open subscheme of the curve has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_isOpenImmersion : topologicalKrullDim U ≤ 1 :=
  j.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
    (curveProperties_dimension smoothFieldDimension hX).le

include hX j in
/-- The closed points of an open subscheme of the curve have discrete valuation rings as local
rings. -/
theorem isDiscreteValuationRing_stalk_of_isOpenImmersion [IsIntegral U]
    (y : Scheme.ClosedPoint U) : IsDiscreteValuationRing (U.presheaf.stalk y.val) := by
  have := smoothOfRelativeDimension_one_of_isOpenImmersion hX j
  have : SmoothOfRelativeDimension 1 (𝟙 U ≫ j ≫ X.hom) := by
    simpa only [Category.id_comp] using this
  exact Scheme.smoothChart_closedPoint_dvr (𝟙 U) (j ≫ X.hom) y.val y.property

include hX in
/-- **The point divisor of a closed point `y` of `U` is the pullback of `𝒪_X(y)`.** -/
private theorem divisorToPicard_single_eq_pullbackClass [IsAlgClosed k] [IsIntegral U]
    [IsNoetherian U] [∀ y : Scheme.ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk y.val)]
    [LocallyOfFiniteType (j ≫ X.hom)] (hdim : topologicalKrullDim U ≤ 1)
    (y : Scheme.ClosedPoint U) :
    DivisorClass.divisorToPicard U hdim (Finsupp.single y 1) =
      pullbackClass j (classOf X.left (PointDivisor.positiveLineBundle X hX
        (pointOfClosedPoint (j ≫ X.hom) y.val y.property ≫ j)
        (by rw [Category.assoc]; exact pointOfClosedPoint_comp (j ≫ X.hom) y.val y.property))) := by
  let q := pointOfClosedPoint (j ≫ X.hom) y.val y.property
  have hq : q ≫ (j ≫ X.hom) = 𝟙 _ := pointOfClosedPoint_comp (j ≫ X.hom) y.val y.property
  have hp : (q ≫ j) ≫ X.hom = 𝟙 _ := by rw [Category.assoc]; exact hq
  let I := PointDivisor.idealLineBundle X hX (q ≫ j) hp
  let e : (Scheme.Modules.pullback j).obj I.val ≅ Scheme.Hom.idealModule q :=
    Scheme.Hom.idealModulePullbackFactor q j
  have hI : IsLocallyRankOne U (Scheme.Hom.idealModule q) :=
    isLocallyRankOne_of_iso U e (pullbackLineBundle j I).property
  let r : Scheme.RationalPoint k U := ⟨j ≫ X.hom, q, hq⟩
  have hr : (⟨r.point, r.point_isClosed⟩ : Scheme.ClosedPoint U) = y :=
    Subtype.ext (pointOfClosedPoint_apply (j ≫ X.hom) y.val y.property _)
  have hclass : pullbackClass j (classOf X.left I) =
      classOf U ⟨Scheme.Hom.idealModule q, hI⟩ :=
    (class_eq_iff U (pullbackLineBundle j I) ⟨Scheme.Hom.idealModule q, hI⟩).mpr ⟨e⟩
  have hpt : DivisorClass.divisorToPicard U hdim (Finsupp.single y 1) =
      classOf U (dualLineBundle U ⟨Scheme.Hom.idealModule q, hI⟩) :=
    (congrArg (fun z => DivisorClass.divisorToPicard U hdim (Finsupp.single z 1)) hr).symm.trans
      (PointDivisor.idealDual_class_eq_point U r hI hdim).symm
  change DivisorClass.divisorToPicard U hdim (Finsupp.single y 1) =
    pullbackClass j (classOf X.left (dualLineBundle X.left I))
  calc DivisorClass.divisorToPicard U hdim (Finsupp.single y 1)
      = classOf U (dualLineBundle U ⟨Scheme.Hom.idealModule q, hI⟩) := hpt
    _ = -classOf U ⟨Scheme.Hom.idealModule q, hI⟩ := classOf_dual U _
    _ = -pullbackClass j (classOf X.left I) := congrArg Neg.neg hclass.symm
    _ = pullbackClass j (-classOf X.left I) :=
      (PullbackTensor.Local.pullbackClass_neg j _).symm
    _ = pullbackClass j (classOf X.left (dualLineBundle X.left I)) :=
      congrArg (pullbackClass j) (classOf_dual X.left I).symm

include hX in
/-- **For a rational point `o` outside the image of `j`, the pullback of `𝒪_X(o)` is
trivial.** -/
private theorem pullbackClass_positiveLineBundle_eq_zero (o : Spec (.of k) ⟶ X.left)
    (ho : o ≫ X.hom = 𝟙 _) (hx : o (IsLocalRing.closedPoint k) ∉ Set.range j) :
    pullbackClass j (classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) = 0 := by
  have hdisj : Disjoint (Set.range o) (Set.range j) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t, rfl⟩ hz
    have ht : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact hx (by simpa only [ht] using hz)
  let I := PointDivisor.idealLineBundle X hX o ho
  let e : (Scheme.Modules.pullback j).obj I.val ≅ (trivialLineBundle U).val :=
    Scheme.Hom.idealModulePullbackIsoOfDisjoint o j hdisj ≪≫
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit U.ringCatSheaf)).symm
  have hclass : pullbackClass j (classOf X.left I) = 0 :=
    (class_eq_iff U (pullbackLineBundle j I) (trivialLineBundle U)).mpr ⟨e⟩
  change pullbackClass j (classOf X.left (dualLineBundle X.left I)) = 0
  calc pullbackClass j (classOf X.left (dualLineBundle X.left I))
      = pullbackClass j (-classOf X.left I) := congrArg (pullbackClass j) (classOf_dual X.left I)
    _ = -pullbackClass j (classOf X.left I) := PullbackTensor.Local.pullbackClass_neg j _
    _ = 0 := by rw [hclass, neg_zero]

/-- The classes of a scheme with no points vanish. -/
private theorem picardGroup_eq_zero_of_isEmpty [IsEmpty U] (c : PicardGroup U) : c = 0 := by
  induction c using Quotient.inductionOn with
  | h L =>
    have hL : IsZero L.val := (Scheme.Modules.isZero_iff_stalks _).mpr fun x => isEmptyElim x
    have hO : IsZero (trivialLineBundle U).val :=
      (Scheme.Modules.isZero_iff_stalks _).mpr fun x => isEmptyElim x
    exact (class_eq_iff U L (trivialLineBundle U)).mpr ⟨hL.iso hO⟩

variable [IsAlgClosed k]

include hX in
/-- `Pic(X) → Pic(U)` is surjective for every open immersion into the curve. -/
theorem pullbackClass_surjective_of_isOpenImmersion :
    Function.Surjective (pullbackClass j) := by
  classical
  intro c
  rcases isEmpty_or_nonempty U with hU | hU
  · exact ⟨0, (pullbackClass_zero j).trans (picardGroup_eq_zero_of_isEmpty c).symm⟩
  have : IsIntegral X.left :=
    curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have := isNoetherian_of_isOpenImmersion hX j
  have := isDiscreteValuationRing_stalk_of_isOpenImmersion hX j
  have := curveProperties_locallyOfFiniteType hX
  have hdim := topologicalKrullDim_le_one_of_isOpenImmersion hX j
  let S := (PullbackTensor.Local.pullbackHom j).range
  have hpoint (y : Scheme.ClosedPoint U) :
      DivisorClass.divisorToPicard U hdim (Finsupp.single y 1) ∈ S := by
    have hp : (pointOfClosedPoint (j ≫ X.hom) y.val y.property ≫ j) ≫ X.hom = 𝟙 _ := by
      rw [Category.assoc]
      exact pointOfClosedPoint_comp (j ≫ X.hom) y.val y.property
    refine ⟨classOf X.left (PointDivisor.positiveLineBundle X hX
      (pointOfClosedPoint (j ≫ X.hom) y.val y.property ≫ j) hp), ?_⟩
    exact (divisorToPicard_single_eq_pullbackClass hX j hdim y).symm
  have hdiv (E : Divisor U) : DivisorClass.divisorToPicard U hdim E ∈ S := by
    induction E using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact S.zero_mem
    | add E F hE hF => rw [map_add]; exact S.add_mem hE hF
    | single y m =>
      have hs : Finsupp.single y m = m • Finsupp.single y (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_zsmul]
      exact S.zsmul_mem (hpoint y) m
  obtain ⟨a, rfl⟩ := DivisorClass.divisorClassToPicard_surjective U hdim c
  induction a using QuotientAddGroup.induction_on with
  | H E => exact hdiv E

include hX in
/-- Degree-zero Picard classes surject onto an open missing a closed point (Milne, Lectures on
Étale Cohomology v2.21, proof of Proposition 14.12, p. 97; Stacks, Tag 03RR). -/
theorem exists_curveDegree_eq_zero_pullbackClass_eq_of_isOpenImmersion
    (hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j) (c : PicardGroup U) :
    ∃ b : PicardGroup X.left,
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX b = 0 ∧ pullbackClass j b = c := by
  have := curveProperties_locallyOfFiniteType hX
  obtain ⟨x, hxc, hxj⟩ := hx
  let o := pointOfClosedPoint X.hom x hxc
  have ho : o ≫ X.hom = 𝟙 _ := pointOfClosedPoint_comp X.hom x hxc
  have hoj : o (IsLocalRing.closedPoint k) ∉ Set.range j := by
    rw [show o (IsLocalRing.closedPoint k) = x from pointOfClosedPoint_apply X.hom x hxc _]
    exact hxj
  let deg := curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula X hX
  let r := PullbackTensor.Local.pullbackHom j
  let O := classOf X.left (PointDivisor.positiveLineBundle X hX o ho)
  have hO : deg O = 1 := curveDegree_positiveLineBundle hX o ho
  have hrO : r O = 0 := pullbackClass_positiveLineBundle_eq_zero hX j o ho hoj
  have hd : Function.Surjective (deg.comp r.ker.subtype) := by
    intro m
    refine ⟨⟨m • O, ?_⟩, ?_⟩
    · change r (m • O) = 0
      rw [map_zsmul, hrO, smul_zero]
    · change deg (m • O) = m
      rw [map_zsmul, hO, smul_eq_mul, mul_one]
  obtain ⟨b, hb⟩ := AddMonoidHom.surjective_comp_ker_subtype r deg
    (pullbackClass_surjective_of_isOpenImmersion hX j) hd c
  exact ⟨b, b.property, hb⟩

end Complement

end AlgebraicGeometry.Scheme.OverField.Curve

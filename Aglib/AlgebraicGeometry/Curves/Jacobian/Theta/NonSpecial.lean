/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AbelDimension
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EffectiveParameters
public import Aglib.AlgebraicGeometry.Curves.Jacobian.DegreeZero
public import Aglib.AlgebraicGeometry.Curves.Picard.PointDegree

/-!
# Line bundles with no sections below the genus

For each nonnegative degree n below the coherent genus, the original curve
has an actual line bundle of degree n with no nonzero global section. Choose
a rational point outside the proper degree-n based Abel image of the same
Jacobian, take its actual Picard class, and undo the base-point normalization.
A nonzero section would give an actual Abel parameter and contradict the
chosen point. The conclusion contains no chosen base point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem exists_rationalPoint_not_mem_range
    {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (f : Z ⟶ Y) [IsProper f] (hns : ¬ Function.Surjective f) :
    ∃ b : Spec (.of k) ⟶ Y, b ≫ p = 𝟙 _ ∧
      b (IsLocalRing.closedPoint k) ∉ Set.range f := by
  classical
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  have hn : ((Set.range f)ᶜ).Nonempty := by
    by_contra hn
    apply hns
    intro y
    by_contra hy
    exact hn ⟨y, hy⟩
  obtain ⟨z, hz, hclosed⟩ := nonempty_inter_closedPoints hn
    f.isClosedMap.isClosed_range.isOpen_compl.isLocallyClosed
  refine ⟨pointOfClosedPoint p z hclosed, pointOfClosedPoint_comp p z hclosed, ?_⟩
  have hp : pointOfClosedPoint p z hclosed (IsLocalRing.closedPoint k) = z :=
    pointOfClosedPoint_apply p z hclosed _
  rw [hp]
  exact hz

open Abel.BoundedFamily

variable {X : FScheme k} (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

include P R

-- Preserve the original representative, component and rational-point coercions.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In every nonnegative degree below the genus there is an actual line
bundle with no nonzero global section. The proof uses the same supplied
Picard representative and its actual identity component throughout. -/
theorem exists_lineBundle_noSections_of_degree_lt_genus (n : ℕ)
    (hn : n < coherentGenus k X) :
    ∃ L : LineBundle X.left,
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
        X hX (classOf X.left L) = (n : ℤ) ∧
      ∀ s : L.val.val.obj (op ⊤), s = 0 := by
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  let := picardCommGrpObj X.hom P R
  obtain ⟨o, ho⟩ := hX.exists_rationalPoint_of_isAlgClosed
  have : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  have := isProper_jacobianAbelMorphism hX o ho P R n
  obtain ⟨b, hb, hbnot⟩ := exists_rationalPoint_not_mem_range
    (identityComponentOver P.obj).hom (jacobianAbelMorphism hX o ho P R n).left
    (not_surjective_jacobianAbelMorphism hX o ho P R hn)
  let b' : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj := Over.homMk b hb
  obtain ⟨c, hc⟩ :=
    (picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral P R).2
      (b' ≫ identityComponentι P.obj)
  have hcdegree : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX c = 0 := by
    apply (picardPoint_mem_identityComponent_iff_of_isAlgClosed hX P R c).mp
    rw [hc]
    change (identityComponent P.obj).ι (b (IsLocalRing.closedPoint k)) ∈
      (identityComponent P.obj : Set P.obj.left)
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨L, hL⟩ := Quotient.exists_rep
    (c + n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho))
  change classOf X.left L =
    c + n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho) at hL
  have hdegree : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
      X hX (classOf X.left L) = (n : ℤ) := by
    rw [hL, map_add, map_nsmul, hcdegree, curveDegree_positiveLineBundle]
    simp
  refine ⟨L, hdegree, fun s => ?_⟩
  by_contra hs
  obtain ⟨a, ha⟩ := exists_comp_abelMorphism_of_nonzero_section hX o ho P R n L hdegree s hs
  have hnormalized : classOf X.left L -
      n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho) = c := by
    rw [hL]
    abel
  rw [hnormalized] at ha
  have hpoint : a ≫ jacobianAbelMorphism hX o ho P R n = b' := by
    apply (cancel_mono (identityComponentι P.obj)).mp
    rw [Category.assoc, jacobianAbelMorphism_comp_inclusion, ha, hc]
  apply hbnot
  refine ⟨a.left (IsLocalRing.closedPoint k), ?_⟩
  exact congrArg (fun q => q.left (IsLocalRing.closedPoint k)) hpoint

end AlgebraicGeometry.Scheme.OverField.Curve

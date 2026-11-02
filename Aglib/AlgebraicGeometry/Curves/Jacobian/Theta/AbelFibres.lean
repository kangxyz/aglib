/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AbelGeometry
public import Aglib.AlgebraicGeometry.Curves.Jacobian.RationalPoints
public import Aglib.AlgebraicGeometry.Curves.Picard.EffectiveClass.Uniqueness
public import Aglib.AlgebraicGeometry.Morphisms.Finite.ClosedPointFibres

/-!
# Finite ordered Abel fibres in a rank-one linear system

An actual line bundle with h0=1 has one effective divisor in its class.
Every ordered tuple in its based Abel fibre therefore uses only points in
that divisor's finite support. The original coordinate maps distinguish the
tuples. Over an algebraically closed field this bounds the closed points of
the actual fibre; Jacobson density makes its whole point set finite.

This proves actual finite point fibres for the proper/quasi-finite dimension
argument. It does not identify their scheme lengths or infer birationality
from pointwise injectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.Cohomology Scheme.RelativePicard
open Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

open Picard Picard.DivisorClass

variable {k : Type u} [Field k] {X : FScheme k}

private def coordinateSection {n : ℕ}
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n) (i : Fin n) :
    𝟙_ (Over (Spec (.of k))) ⟶ X :=
  Over.homMk (a.left ≫ coordinate X.hom n i) (by
    rw [Category.assoc, coordinate_over, Over.w a])

variable (hX : Properties X) (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

-- Compare the same original identity-fibre and graph-family maps.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comp_abelMorphism_eq_coordinateClass {n : ℕ}
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n) :
    letI := hX.smooth
    letI := hX.proper
    a ≫ (abelMorphism o ho P R n).hom = picardPoint P R
      (∑ i : Fin n,
        (classOf X.left (PointDivisor.positiveLineBundle X hX
          (coordinateSection a i).left (Over.w (coordinateSection a i))) -
            classOf X.left (PointDivisor.positiveLineBundle X hX o ho))) := by
  let := hX.smooth
  let := hX.proper
  apply parameterPoint_comp_abelMorphism_eq_picardPoint o ho P R a.left (Over.w a)
  rw [lineBundle_class_at_point]
  change (PullbackTensor.Local.pullbackHom _) (∑ i : Fin n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact pointDifference_class_pullback_identity X hX o ho
    (coordinateSection a i).left (Over.w (coordinateSection a i))

variable [IsAlgClosed k]

private theorem rationalPoint_ext_of_apply_eq {T : FScheme k}
    [LocallyOfFiniteType T.hom] (a b : 𝟙_ (Over (Spec (.of k))) ⟶ T)
    (h : a.left (IsLocalRing.closedPoint k) = b.left (IsLocalRing.closedPoint k)) : a = b := by
  apply Over.OverMorphism.ext
  have h' : (pointEquivClosedPoint T.hom) ⟨a.left, Over.w a⟩ =
      (pointEquivClosedPoint T.hom) ⟨b.left, Over.w b⟩ := Subtype.ext h
  exact congrArg Subtype.val ((pointEquivClosedPoint T.hom).injective h')

variable [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

-- The finite-support bound uses the original field-point and Picard presentations.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual point fibre of the ordered degree-n Abel morphism at a
normalized class with h0=1 is finite. No assertion of reduced fibre or
generic degree is part of this conclusion. -/
theorem finite_preimage_abelMorphism_of_h0_one (n : ℕ) (L : LineBundle X.left)
    (h0 : Module.finrank k (moduleCohomology k X L.val 0) = 1) :
    letI := hX.smooth
    letI := hX.proper
    ((abelMorphism o ho P R n).hom.left ⁻¹'
      {(picardPoint P R (classOf X.left L -
        n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho))).left
          (IsLocalRing.closedPoint k)}).Finite := by
  classical
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  let := PointDivisor.isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    PointDivisor.isDiscreteValuationRing_stalk X hX x
  have : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  have : Nontrivial (moduleCohomology k X L.val 0) := Module.nontrivial_of_finrank_eq_succ h0
  obtain ⟨s, hs⟩ := exists_ne (0 : moduleCohomology k X L.val 0)
  have hs' : moduleH0Equiv X L.val s ≠ 0 := fun hz =>
    hs ((moduleH0Equiv X L.val).injective (hz.trans (moduleH0Equiv X L.val).map_zero.symm))
  let hd := hX.topologicalKrullDim_eq_one.le
  obtain ⟨D, hD, hDL⟩ := exists_effective_divisor_class_of_nonzero_section
    X.left hd L (moduleH0Equiv X L.val s) hs'
  obtain ⟨e⟩ := (class_eq_iff X.left (divisorLineBundle X.left hd D) L).mp hDL
  have hD0 : Module.finrank k (moduleCohomology k X (divisorSheaf X.left D) 0) = 1 :=
    (moduleCohomologyIso X e 0).finrank_eq.trans h0
  let F := (abelMorphism o ho P R n).hom.left
  let b := picardPoint P R (classOf X.left L -
    n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho))
  have hproper : IsProper F := isProper_abelMorphism o ho P R n
  have : JacobsonSpace (parameter X.hom n).left :=
    LocallyOfFiniteType.jacobsonSpace (parameter X.hom n).hom
  have hbclosed : IsClosed ({b.left (IsLocalRing.closedPoint k)} : Set P.obj.left) :=
    (show Scheme.RationalPoint k P.obj.left from ⟨P.obj.hom, b.left, Over.w b⟩).point_isClosed
  apply JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints
    (X := (parameter X.hom n).left) (hbclosed.preimage F.continuous)
  let Z : Set (parameter X.hom n).left :=
    F ⁻¹' {b.left (IsLocalRing.closedPoint k)} ∩ closedPoints (parameter X.hom n).left
  change Z.Finite
  let a (z : Z) : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n :=
    Over.homMk (pointOfClosedPoint (parameter X.hom n).hom z.val z.property.2)
      (pointOfClosedPoint_comp (parameter X.hom n).hom z.val z.property.2)
  have haval (z : Z) : (a z).left (IsLocalRing.closedPoint k) = z.val :=
    pointOfClosedPoint_apply (parameter X.hom n).hom z.val z.property.2 _
  have ha (z : Z) : a z ≫ (abelMorphism o ho P R n).hom = b := by
    apply rationalPoint_ext_of_apply_eq
    change F ((a z).left (IsLocalRing.closedPoint k)) = b.left (IsLocalRing.closedPoint k)
    rw [haval]
    exact z.property.1
  let E (z : Z) : Divisor X.left := ∑ i : Fin n,
    PointDivisor.pointDivisor X (coordinateSection (a z) i).left
      (Over.w (coordinateSection (a z) i)) 1
  have hE (z : Z) : ∀ x, 0 ≤ E z x := by
    intro x
    dsimp only [E]
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun i _ => PointDivisor.pointDivisor_nonneg X
      (coordinateSection (a z) i).left (Over.w (coordinateSection (a z) i)) 1 x
  have hEclass (z : Z) : divisorToPicard X.left hd (E z) = classOf X.left L := by
    have hc := (picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
      P R).1 ((comp_abelMorphism_eq_coordinateClass hX o ho P R (a z)).symm.trans (ha z))
    have hsum : (∑ i : Fin n, classOf X.left (PointDivisor.positiveLineBundle X hX
        (coordinateSection (a z) i).left (Over.w (coordinateSection (a z) i)))) =
        divisorToPicard X.left hd (E z) := by
      dsimp only [E]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => PointDivisor.positiveLineBundle_class_eq_pointDivisor
        X hX (coordinateSection (a z) i).left (Over.w (coordinateSection (a z) i)) hd
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hc
    rw [hsum] at hc
    have h := congrArg (fun c : PicardGroup X.left =>
      c + n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) hc
    simpa only [sub_add_cancel] using h
  have hED (z : Z) : E z = D :=
    (effective_divisor_eq_of_class_eq_of_h0_one X hd D (E z) hD (hE z)
      (hDL.trans (hEclass z).symm) hD0).symm
  have hmem (z : Z) (i : Fin n) : PointDivisor.closedPoint X
      (coordinateSection (a z) i).left (Over.w (coordinateSection (a z) i)) ∈ D.support := by
    let x := PointDivisor.closedPoint X
      (coordinateSection (a z) i).left (Over.w (coordinateSection (a z) i))
    have hcoeff : 1 ≤ E z x := by
      dsimp only [E]
      rw [Finsupp.finsetSum_apply]
      calc
        (1 : ℤ) = PointDivisor.pointDivisor X (coordinateSection (a z) i).left
            (Over.w (coordinateSection (a z) i)) 1 x := by
          simp only [PointDivisor.pointDivisor, x, Finsupp.single_eq_same]
        _ ≤ ∑ j : Fin n, PointDivisor.pointDivisor X (coordinateSection (a z) j).left
            (Over.w (coordinateSection (a z) j)) 1 x :=
          Finset.single_le_sum (fun j _ => PointDivisor.pointDivisor_nonneg X
            (coordinateSection (a z) j).left (Over.w (coordinateSection (a z) j)) 1 x)
            (Finset.mem_univ i)
    rw [hED z] at hcoeff
    apply Finsupp.mem_support_iff.mpr
    change D x ≠ 0
    omega
  let φ : Z → (Fin n → {x : ClosedPoint X.left // x ∈ D.support}) := fun z i =>
    ⟨PointDivisor.closedPoint X (coordinateSection (a z) i).left
      (Over.w (coordinateSection (a z) i)), hmem z i⟩
  have hinj : Function.Injective φ := by
    intro z z' hh
    have hcoords (i : Fin n) : coordinateSection (a z) i = coordinateSection (a z') i := by
      apply rationalPoint_ext_of_apply_eq
      exact congrArg Subtype.val (congrArg Subtype.val (congrFun hh i))
    have haa : a z = a z' := by
      apply finiteProductOver_hom_ext (fun _ : Fin n => Over.mk X.hom)
      intro i
      apply Over.OverMorphism.ext
      exact congrArg Over.Hom.left (hcoords i)
    apply Subtype.ext
    have heq := congrArg (fun q : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n =>
      q.left (IsLocalRing.closedPoint k)) haa
    simpa only [haval] using heq
  have : Finite Z := Finite.of_injective φ hinj
  exact Set.toFinite Z

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ComponentCoordinates
public import Aglib.AlgebraicGeometry.Limits.PullbackTransport
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.PairToLine
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.FiniteClosedCover
/-!
# Ordered cycle coordinates on the original component maps
Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`IntrinsicSplitNode/ResolvedCoordinates.lean`, lines 478–1155.
SHA-256: `424932cf8a97432d3030dacda7f9d34b15e99b6b09a00ef681e3d3969bb2681a`.
-/
@[expose] public section
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Pullback.Transport
open AlgebraicGeometry.Scheme.TwoPoint AlgebraicGeometry.Scheme.RegularityDescent
open AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
section
/-! Source-only actual n>=3 coordinate constructor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 3)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hext : NormalProperCurveGenericExtension.{u})
  (hdvr : ProperBirationalDVRIsomorphismLocus.{u})
local notation "k" => ResidueField R
local notation "F" => finalSpecialFibre M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc
local notation "f" => strictP1ToFinal M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc hx hy hext
local notation "P" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
local notation "left" => originalLeftStrictPoint M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "right" => originalRightStrictPoint M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "last" => (Fin.last (m + 1) : Fin (m + 2))
local notation "b" => Scheme.ProjectiveLine.structureMap k
/-- Index zero is the strict component: its incoming point is the RIGHT end.
The other incoming points are the actual original exceptional starts. -/
def manyIncoming (i : Fin (m + 3)) : Spec (.of k) ⟶ Scheme.ProjectiveLine.projectiveP1 k :=
  Fin.cases right (Resolution.interiorStart (R := R) (m + 2)) i
/-- The strict outgoing point is the LEFT end, followed by exceptional finishes. -/
def manyOutgoing (i : Fin (m + 3)) : Spec (.of k) ⟶ Scheme.ProjectiveLine.projectiveP1 k :=
  Fin.cases left (Resolution.interiorFinish (R := R) (m + 2)) i
local notation "s" =>
  manyIncoming M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr
local notation "t" =>
  manyOutgoing M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr
@[simp] lemma manyIncoming_zero : s 0 = right := rfl
@[simp] lemma manyOutgoing_zero : t 0 = left := rfl
@[simp] lemma manyIncoming_succ (j : Fin (m + 2)) :
    s j.succ = Resolution.interiorStart (R := R) (m + 2) j := rfl
@[simp] lemma manyOutgoing_succ (j : Fin (m + 2)) :
    t j.succ = Resolution.interiorFinish (R := R) (m + 2) j := rfl
@[reassoc] lemma manyIncoming_over (i : Fin (m + 3)) : s i ≫ b = 𝟙 _ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact originalRightStrictPoint_over M π hπ m a ha he ρ hρ hex hp hatlas hbc hx
      hy hext hdvr
  · exact Resolution.interiorStart_over (R := R) (m + 2) j
@[reassoc] lemma manyOutgoing_over (i : Fin (m + 3)) : t i ≫ b = 𝟙 _ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact originalLeftStrictPoint_over M π hπ m a ha he ρ hρ hex hp hatlas hbc hx
      hy hext hdvr
  · exact Resolution.interiorFinish_over (R := R) (m + 2) j
lemma manyEndpoints_ne (i : Fin (m + 3)) : s i ≠ t i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · intro h
    exact strict_endpoints_ne M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext
      hdvr h.symm
  · intro h
    let z : Spec (.of k) := Classical.choice inferInstance
    exact Set.disjoint_left.mp (Resolution.interior_endpoints_disjoint (R := R) (m + 2) j)
      ⟨z, rfl⟩ ⟨z, congrArg (fun q : Spec (.of k) ⟶
        Scheme.ProjectiveLine.projectiveP1 k => q z) h.symm⟩
/-- Constructed component coordinates, not an extra diagram input. -/
def manyCoordinateIso (i : Fin (m + 3)) :
    Scheme.ProjectiveLine.projectiveP1 k ≅ Scheme.PinchedLine.lineGluing k :=
  pairToLineIso k (s i) (t i)
    (manyIncoming_over M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr i)
    (manyOutgoing_over M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr i)
    (manyEndpoints_ne M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr i)
local notation "e" =>
  manyCoordinateIso M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr
@[reassoc] lemma manyCoordinateIso_incoming (i : Fin (m + 3)) :
    s i ≫ (e i).hom = Scheme.Polygon.targetLinePoint k 0 := pairToLineIso_first ..
@[reassoc] lemma manyCoordinateIso_outgoing (i : Fin (m + 3)) :
    t i ≫ (e i).hom = Scheme.Polygon.targetLinePoint k 1 := pairToLineIso_second ..
@[reassoc] lemma manyCoordinateIso_inv_zero (i : Fin (m + 3)) :
    Scheme.Polygon.targetLinePoint k 0 ≫ (e i).inv = s i := pairToLineIso_inv_first ..
@[reassoc] lemma manyCoordinateIso_inv_one (i : Fin (m + 3)) :
    Scheme.Polygon.targetLinePoint k 1 ≫ (e i).inv = t i := pairToLineIso_inv_second ..
@[reassoc] lemma manyCoordinateIso_over (i : Fin (m + 3)) :
    (e i).hom ≫ Scheme.PinchedLine.lineStructure k = b := pairToLineIso_over ..
@[reassoc] lemma manyCoordinateIso_inv_over (i : Fin (m + 3)) :
    (e i).inv ≫ b = Scheme.PinchedLine.lineStructure k := pairToLineIso_inv_over ..
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
end -- original EOF scope
end
section
/-! Source-only actual n=2 coordinate constructor, retaining both shared points. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ 2))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
  (σ : ResidueField R)
  (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) σ)
  (hne : ρ ≠ σ)
local notation "k" => ResidueField R
local notation "f" => strictP1ToFinal M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "g" => originalExceptionalP1 M π hπ 1 a ha he ρ hρ hex hp hatlas hbc 0
local notation "J" => originalExceptionalToSpecial M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc
local notation "b" => Scheme.ProjectiveLine.structureMap k
local notation "base" => pullback.snd (modification M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W) (Resolution.residueBase (R := R))
local notation "s" =>
  twoComponentStrictBoundary M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
local notation "t" =>
  twoComponentExceptionalBoundary M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
/-- The SAME full pair is ordered oppositely on the strict component. -/
def twoIncoming (i : Fin 2) : Spec (.of k) ⟶ Scheme.ProjectiveLine.projectiveP1 k :=
  Fin.cases (productPoint1 k ≫ s) (fun _ => productPoint0 k ≫ t) i
/-- The outgoing points of the two-component cycle: point zero on the strict side and point one on
the exceptional side. -/
def twoOutgoing (i : Fin 2) : Spec (.of k) ⟶ Scheme.ProjectiveLine.projectiveP1 k :=
  Fin.cases (productPoint0 k ≫ s) (fun _ => productPoint1 k ≫ t) i
local notation "start" => twoIncoming M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
local notation "finish" => twoOutgoing M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
@[simp] lemma twoIncoming_zero : start 0 = productPoint1 k ≫ s := rfl
@[simp] lemma twoOutgoing_zero : finish 0 = productPoint0 k ≫ s := rfl
@[simp] lemma twoIncoming_one : start 1 = productPoint0 k ≫ t := rfl
@[simp] lemma twoOutgoing_one : finish 1 = productPoint1 k ≫ t := rfl
@[reassoc] lemma twoIncoming_over (i : Fin 2) : start i ≫ b = 𝟙 _ := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · simpa only [twoIncoming, Fin.cases_zero, Fin.cases_succ, Category.assoc] using
      twoComponentStrictPoint1_over M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
  · simpa only [twoIncoming, Fin.cases_zero, Fin.cases_succ, Category.assoc] using
      twoComponentExceptionalPoint0_over M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
@[reassoc] lemma twoOutgoing_over (i : Fin 2) : finish i ≫ b = 𝟙 _ := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · simpa only [twoOutgoing, Fin.cases_zero, Fin.cases_succ, Category.assoc] using
      twoComponentStrictPoint0_over M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
  · simpa only [twoOutgoing, Fin.cases_zero, Fin.cases_succ, Category.assoc] using
      twoComponentExceptionalPoint1_over M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
variable (hdvr : ProperBirationalDVRIsomorphismLocus.{u})
include hdvr in
lemma twoEndpoints_ne (i : Fin 2) : start i ≠ finish i := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · intro h
    exact twoComponentStrictPoints_ne M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne h.symm
  · exact twoComponentExceptionalPoints_ne M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
      hdvr
/-- Both isomorphisms are constructed from the two original projections of
one shared complete scheme-theoretic intersection. -/
def twoCoordinateIso (i : Fin 2) :
    Scheme.ProjectiveLine.projectiveP1 k ≅ Scheme.PinchedLine.lineGluing k :=
  pairToLineIso k (start i) (finish i)
    (twoIncoming_over M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne i)
    (twoOutgoing_over M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne i)
    (twoEndpoints_ne M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne hdvr i)
local notation "e" =>
  twoCoordinateIso M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne hdvr
@[reassoc] lemma twoCoordinateIso_incoming (i : Fin 2) :
    start i ≫ (e i).hom = Scheme.Polygon.targetLinePoint k 0 := pairToLineIso_first ..
@[reassoc] lemma twoCoordinateIso_outgoing (i : Fin 2) :
    finish i ≫ (e i).hom = Scheme.Polygon.targetLinePoint k 1 := pairToLineIso_second ..
@[reassoc] lemma twoCoordinateIso_inv_zero (i : Fin 2) :
    Scheme.Polygon.targetLinePoint k 0 ≫ (e i).inv = start i := pairToLineIso_inv_first ..
@[reassoc] lemma twoCoordinateIso_inv_one (i : Fin 2) :
    Scheme.Polygon.targetLinePoint k 1 ≫ (e i).inv = finish i := pairToLineIso_inv_second ..
@[reassoc] lemma twoCoordinateIso_over (i : Fin 2) :
    (e i).hom ≫ Scheme.PinchedLine.lineStructure k = b := pairToLineIso_over ..
@[reassoc] lemma twoCoordinateIso_inv_over (i : Fin 2) :
    (e i).inv ≫ b = Scheme.PinchedLine.lineStructure k := pairToLineIso_inv_over ..
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
end -- original EOF scope
end
section
/-! Source-only exact actual-source cyclic pair classification. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 3)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hext : NormalProperCurveGenericExtension.{u})
  (hdvr : ProperBirationalDVRIsomorphismLocus.{u})
local notation "k" => ResidueField R
local notation "F" => finalSpecialFibre M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc
local notation "f" => strictP1ToFinal M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc hx hy hext
local notation "P" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
local notation "left" => originalLeftStrictPoint M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "right" => originalRightStrictPoint M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "last" => (Fin.last (m + 1) : Fin (m + 2))
local notation "b" => Scheme.ProjectiveLine.structureMap k
local notation "s" =>
  manyIncoming M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr
local notation "t" =>
  manyOutgoing M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr
local notation "c" => componentMap M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc hx hy hext
lemma rotate_many_zero : finRotate (m + 3) 0 = (0 : Fin (m + 2)).succ := by
  exact finRotate_of_lt (Nat.succ_pos (m + 1))
lemma rotate_many_last : finRotate (m + 3) (last).succ = 0 := finRotate_last
lemma rotate_many_succ (i j : Fin (m + 2)) (h : i.val + 1 = j.val) :
    finRotate (m + 3) i.succ = j.succ := by
  have hi : i.val + 1 < m + 2 := by omega
  calc
    finRotate (m + 3) i.succ = ⟨i.val + 2, by omega⟩ := finRotate_of_lt hi
    _ = j.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
/-- Every outgoing/incoming square is the actual scheme pullback on the
literal finite reindexing of the original strict and exceptional maps. -/
lemma manyOutgoing_isPullback (i : Fin (m + 3)) :
    IsPullback (t i) (s (finRotate (m + 3) i)) (c i) (c (finRotate (m + 3) i)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [rotate_many_zero]
    simpa only [manyOutgoing_zero, manyIncoming_succ, componentMap_zero, componentMap_succ]
      using originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy hext hdvr
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [rotate_many_last]
      simpa only [manyOutgoing_succ, manyIncoming_zero, componentMap_succ, componentMap_zero]
        using (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
          hx hy hext hdvr).flip
    · rw [rotate_many_succ m j.castSucc j.succ (by simp)]
      simpa only [manyOutgoing_succ, manyIncoming_succ, componentMap_succ] using
        originalExceptionalP1_adjacent_isPullback M π hπ (m + 2) a ha he ρ hρ
          hex hp hatlas hbc j.castSucc j.succ
          ((exceptional_adjacent_iff (m + 2) j.castSucc j.succ).mpr (by simp))
/-- Distinct non-neighbours have empty genuine pullbacks; no reduced-support
replacement or graph-only inference is used. -/
lemma manyPair_empty (i j : Fin (m + 3)) (hij : i ≠ j)
    (hnext : j ≠ finRotate (m + 3) i) (hprev : i ≠ finRotate (m + 3) j) :
    IsEmpty (pullback (c i) (c j) : Scheme.{u}) := by
  revert j
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij hnext hprev
      exact (hij rfl).elim
    · intro hij hnext hprev
      have h0 : j ≠ 0 := by
        intro h; subst j; exact hnext (rotate_many_zero m).symm
      have hl : j ≠ last := by
        intro h; subst j; exact hprev (rotate_many_last m).symm
      simpa only [componentMap_zero, componentMap_succ] using
        strictExceptionalInterior_empty M π hπ m a ha he ρ hρ
          hex hp hatlas hbc hx hy hext j h0 hl
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij hnext hprev
      have h0 : i ≠ 0 := by
        intro h; subst i; exact hprev (rotate_many_zero m).symm
      have hl : i ≠ last := by
        intro h; subst i; exact hnext (rotate_many_last m).symm
      rw [componentMap_succ, componentMap_zero]
      let := strictExceptionalInterior_empty M π hπ m a ha he ρ hρ
        hex hp hatlas hbc hx hy hext i h0 hl
      exact Function.isEmpty (pullbackSymmetry (P i) f).hom
    · intro hij hnext hprev
      have hne : i ≠ j := fun h => hij (congrArg Fin.succ h)
      have hn : ¬ Resolution.ChainAdjacent (m + 2) (.inr i) (.inr j) := by
        intro h
        exact hnext (rotate_many_succ m i j ((exceptional_adjacent_iff (m + 2) i j).mp h)).symm
      have hback : ¬ Resolution.ChainAdjacent (m + 2) (.inr j) (.inr i) := by
        intro h
        exact hprev (rotate_many_succ m j i ((exceptional_adjacent_iff (m + 2) j i).mp h)).symm
      simpa only [componentMap_succ] using originalExceptionalP1_nonadjacent_empty
        M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc i j hne hn hback
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
end -- original EOF scope
end
section
/-! Source-only complete forward and inverse compatibility on actual pairs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 3)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hext : NormalProperCurveGenericExtension.{u})
  (hdvr : ProperBirationalDVRIsomorphismLocus.{u})
local notation "k" => ResidueField R
local notation "F" => finalSpecialFibre M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc
local notation "f" => strictP1ToFinal M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc hx hy hext
local notation "P" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
local notation "left" => originalLeftStrictPoint M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "right" => originalRightStrictPoint M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "last" => (Fin.last (m + 1) : Fin (m + 2))
local notation "b" => Scheme.ProjectiveLine.structureMap k
local notation "s" =>
  manyIncoming M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr
local notation "t" =>
  manyOutgoing M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr
local notation "c" => componentMap M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc hx hy hext
local notation "e" =>
  manyCoordinateIso M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext hdvr
local notation "d" => Scheme.Polygon.componentTarget k (m + 3)
/-- All source pairs: self pairs, both edge orientations and empty pairs. -/
lemma manyForward_compatible (i j : Fin (m + 3)) :
    pullback.fst (c i) (c j) ≫ (e i).hom ≫ d i =
      pullback.snd (c i) (c j) ≫ (e j).hom ≫ d j := by
  by_cases hij : i = j
  · subst j
    let : IsClosedImmersion (c i) := componentMap_closed M π hπ (m + 1) a ha he ρ hρ hex hp hatlas
      hbc hx hy hext
      hdvr i
    have h : pullback.fst (c i) (c i) = pullback.snd (c i) (c i) :=
      (cancel_mono (c i)).mp pullback.condition
    rw [h]
  by_cases hnext : j = finRotate (m + 3) i
  · subst j
    apply compatible_on_pullback_of_square (manyOutgoing_isPullback M π hπ m a ha he ρ hρ hex hp
      hatlas hbc hx hy hext hdvr i)
    simpa only [Category.assoc, manyCoordinateIso_outgoing_assoc,
      manyCoordinateIso_incoming_assoc] using Scheme.Polygon.target_endpoint_collision k (m + 3) i
  by_cases hprev : i = finRotate (m + 3) j
  · subst i
    apply compatible_on_pullback_of_square (manyOutgoing_isPullback M π hπ m a ha he ρ hρ hex hp
      hatlas hbc hx hy hext hdvr j).flip
    simpa only [Category.assoc, manyCoordinateIso_outgoing_assoc,
      manyCoordinateIso_incoming_assoc] using (Scheme.Polygon.target_endpoint_collision k (m + 3)
        j).symm
  · let := manyPair_empty M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext i j hij hnext hprev
    exact AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _
/-- The inverse maps satisfy a separately derived compatibility on every
complete actual TARGET pair. No cancellation of a forward descent is assumed. -/
lemma manyBackward_compatible (i j : Fin (m + 3)) :
    pullback.fst (d i) (d j) ≫ (e i).inv ≫ c i =
      pullback.snd (d i) (d j) ≫ (e j).inv ≫ c j := by
  by_cases hij : i = j
  · subst j
    let : IsClosedImmersion (d i) :=
      Scheme.Polygon.componentTarget_closedImmersion_of_one_lt k (m + 3) (by omega) i
    have h : pullback.fst (d i) (d i) = pullback.snd (d i) (d i) :=
      (cancel_mono (d i)).mp pullback.condition
    rw [h]
  by_cases hnext : j = finRotate (m + 3) i
  · subst j
    apply compatible_on_pullback_of_square (Scheme.Polygon.outgoingPair_isPullback k (m + 3) (by
      omega) i)
    simpa only [Category.assoc, manyCoordinateIso_inv_one_assoc,
      manyCoordinateIso_inv_zero_assoc] using (manyOutgoing_isPullback M π hπ m a ha he ρ hρ hex
        hp hatlas hbc hx hy hext hdvr i).w
  by_cases hprev : i = finRotate (m + 3) j
  · subst i
    apply compatible_on_pullback_of_square (Scheme.Polygon.outgoingPair_isPullback k (m + 3) (by
      omega) j).flip
    simpa only [Category.assoc, manyCoordinateIso_inv_one_assoc,
      manyCoordinateIso_inv_zero_assoc] using (manyOutgoing_isPullback M π hπ m a ha he ρ hρ hex
        hp hatlas hbc hx hy hext hdvr j).w.symm
  · let := Scheme.Polygon.targetPair_empty_of_nonadjacent k (m + 3) i j hij hnext hprev
    exact AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
end -- original EOF scope
end
section
/-! Source-only full two-component pair compatibility, in both directions. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
@[reassoc] lemma productPoint0_boundaryLineMap (k : Type u) [Field k] :
    productPoint0 k ≫ Scheme.Polygon.boundaryLineMap k = Scheme.Polygon.targetLinePoint k 0 := by
  rw [Scheme.Polygon.boundaryLineMap_coprod,
    Scheme.Pullback.SpecProducts.specProductIso, Iso.symm_hom,
    productPoint0_coprodSpecIso_assoc, coprod.inl_desc]
@[reassoc] lemma productPoint1_boundaryLineMap (k : Type u) [Field k] :
    productPoint1 k ≫ Scheme.Polygon.boundaryLineMap k = Scheme.Polygon.targetLinePoint k 1 := by
  rw [Scheme.Polygon.boundaryLineMap_coprod,
    Scheme.Pullback.SpecProducts.specProductIso, Iso.symm_hom,
    productPoint1_coprodSpecIso_assoc, coprod.inr_desc]
@[reassoc] lemma productPoint0_reverseBoundary (k : Type u) [Field k] :
    productPoint0 k ≫ Scheme.Polygon.reverseBoundaryLineMap k = Scheme.Polygon.targetLinePoint k 1
      := by
  rw [Scheme.Polygon.reverseBoundaryLineMap,
    Scheme.Pullback.SpecProducts.specProductIso, Iso.symm_hom,
    productPoint0_coprodSpecIso_assoc, coprod.inl_desc]
@[reassoc] lemma productPoint1_reverseBoundary (k : Type u) [Field k] :
    productPoint1 k ≫ Scheme.Polygon.reverseBoundaryLineMap k = Scheme.Polygon.targetLinePoint k 0
      := by
  rw [Scheme.Polygon.reverseBoundaryLineMap,
    Scheme.Pullback.SpecProducts.specProductIso, Iso.symm_hom,
    productPoint1_coprodSpecIso_assoc, coprod.inr_desc]
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ 2))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
  (σ : ResidueField R)
  (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) σ)
  (hne : ρ ≠ σ)
local notation "k" => ResidueField R
local notation "f" => strictP1ToFinal M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "g" => originalExceptionalP1 M π hπ 1 a ha he ρ hρ hex hp hatlas hbc 0
local notation "J" => originalExceptionalToSpecial M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc
local notation "b" => Scheme.ProjectiveLine.structureMap k
local notation "base" => pullback.snd (modification M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W) (Resolution.residueBase (R := R))
local notation "s" =>
  twoComponentStrictBoundary M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
local notation "t" =>
  twoComponentExceptionalBoundary M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
local notation "E" => twoComponentPairIso M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
local notation "start" => twoIncoming M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
local notation "finish" => twoOutgoing M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
local notation "c" => componentMap M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "d" => Scheme.Polygon.componentTarget k 2
variable (hdvr : ProperBirationalDVRIsomorphismLocus.{u})
local notation "e" =>
  twoCoordinateIso M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne hdvr
/-- Forward compatibility uses BOTH points of the complete source pair. -/
lemma twoForward_01 :
    pullback.fst (c 0) (c 1) ≫ (e 0).hom ≫ d 0 =
      pullback.snd (c 0) (c 1) ≫ (e 1).hom ≫ d 1 := by
  have hc0 : c 0 = f := componentMap_zero M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H
  have hc1 : c 1 = g := componentMap_succ M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H (0 : Fin
    1)
  have hb : s ≫ (e 0).hom ≫ d 0 = t ≫ (e 1).hom ≫ d 1 := by
    apply productPoints_hom_ext k
    · have h : finish 0 ≫ (e 0).hom ≫ d 0 = start 1 ≫ (e 1).hom ≫ d 1 := by
        rw [twoCoordinateIso_outgoing_assoc, twoCoordinateIso_incoming_assoc]
        simpa only [Scheme.Polygon.rotate_two_eq_other (0 : Fin 2) 1 (by decide)] using
          Scheme.Polygon.target_endpoint_collision k 2 0
      simpa only [twoOutgoing_zero, twoIncoming_one, Category.assoc] using h
    · have h : start 0 ≫ (e 0).hom ≫ d 0 = finish 1 ≫ (e 1).hom ≫ d 1 := by
        rw [twoCoordinateIso_incoming_assoc, twoCoordinateIso_outgoing_assoc]
        simpa only [Scheme.Polygon.rotate_two_eq_other (1 : Fin 2) 0 (by decide)] using
          (Scheme.Polygon.target_endpoint_collision k 2 1).symm
      simpa only [twoIncoming_zero, twoOutgoing_one, Category.assoc] using h
  rw [hc0, hc1, ← cancel_epi (E).inv]
  simpa only [twoComponentStrictBoundary, twoComponentExceptionalBoundary, Category.assoc] using hb
/-- Backward compatibility uses BOTH points of the complete target pair,
and the same original source square with the corresponding reversed order. -/
lemma twoBackward_01 :
    pullback.fst (d 0) (d 1) ≫ (e 0).inv ≫ c 0 =
      pullback.snd (d 0) (d 1) ≫ (e 1).inv ≫ c 1 := by
  have hc0 : c 0 = f := componentMap_zero M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H
  have hc1 : c 1 = g := componentMap_succ M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H (0 : Fin
    1)
  rw [← cancel_epi (Scheme.Polygon.twoPairIso k 0 1 (by decide)).inv]
  simp only [Scheme.Polygon.twoPairIso_inv_fst_assoc, Scheme.Polygon.twoPairIso_inv_snd_assoc]
  apply productPoints_hom_ext k
  · rw [productPoint0_boundaryLineMap_assoc, productPoint0_reverseBoundary_assoc,
      twoCoordinateIso_inv_zero_assoc, twoCoordinateIso_inv_one_assoc,
      twoIncoming_zero, twoOutgoing_one, hc0, hc1]
    simpa only [Category.assoc] using congrArg (fun z => productPoint1 k ≫ z)
      (twoComponentBoundary_square M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne)
  · rw [productPoint1_boundaryLineMap_assoc, productPoint1_reverseBoundary_assoc,
      twoCoordinateIso_inv_one_assoc, twoCoordinateIso_inv_zero_assoc,
      twoOutgoing_zero, twoIncoming_one, hc0, hc1]
    simpa only [Category.assoc] using congrArg (fun z => productPoint0 k ≫ z)
      (twoComponentBoundary_square M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne)
/-- The two orientations of the FULL pair plus both self pairs. -/
lemma twoForward_compatible (i j : Fin 2) :
    pullback.fst (c i) (c j) ≫ (e i).hom ≫ d i =
      pullback.snd (c i) (c j) ≫ (e j).hom ≫ d j := by
  let : ∀ i, IsClosedImmersion (c i) := fun i =>
    componentMap_closed M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr i
  fin_cases i <;> fin_cases j
  · exact compatible_self _ _
  · exact twoForward_01 M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne hdvr
  · exact compatible_flip _ _ _ _ (twoForward_01 M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ
      hσ hne hdvr)
  · exact compatible_self _ _
lemma twoBackward_compatible (i j : Fin 2) :
    pullback.fst (d i) (d j) ≫ (e i).inv ≫ c i =
      pullback.snd (d i) (d j) ≫ (e j).inv ≫ c j := by
  let : ∀ i, IsClosedImmersion (d i) := fun i =>
    Scheme.Polygon.componentTarget_closedImmersion_of_one_lt k 2 (by decide) i
  fin_cases i <;> fin_cases j
  · exact compatible_self _ _
  · exact twoBackward_01 M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne hdvr
  · exact compatible_flip _ _ _ _ (twoBackward_01 M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ
      hσ hne hdvr)
  · exact compatible_self _ _
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
end -- original EOF scope
end
section
/-! Source-only uniform actual finite component diagram, exponent >=2. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
open AlgebraicGeometry.Scheme.ProjectiveLine (projectiveP1)
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
local notation "k" => ResidueField R
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
variable (hdvr : ProperBirationalDVRIsomorphismLocus.{u})
  (σ : ResidueField R)
  (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) σ)
  (hne : ρ ≠ σ)
/-- The uniform actual component isomorphism. The two-cycle branch keeps its
full shared pair; all larger cycles use the actual incoming/outgoing sections. -/
def coordinateIso (j : Fin (m + 2)) : projectiveP1 k ≅ Scheme.PinchedLine.lineGluing k := by
  cases m with
  | zero =>
    exact twoCoordinateIso M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
      hdvr j
  | succ q =>
    exact manyCoordinateIso M π hπ q a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr j
local notation "e" =>
  coordinateIso M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr σ hσ hne
local notation "c" => componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "d" => Scheme.Polygon.componentTarget k (m + 2)
@[reassoc] lemma coordinateIso_over (j : Fin (m + 2)) :
    (e j).hom ≫ Scheme.PinchedLine.lineStructure k = Scheme.ProjectiveLine.structureMap k := by
  cases m with
  | zero =>
    exact twoCoordinateIso_over M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
      hdvr j
  | succ q =>
    exact manyCoordinateIso_over M π hπ q a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr j
@[reassoc] lemma coordinateIso_inv_over (j : Fin (m + 2)) :
    (e j).inv ≫ Scheme.ProjectiveLine.structureMap k = Scheme.PinchedLine.lineStructure k := by
  cases m with
  | zero =>
    exact twoCoordinateIso_inv_over M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
      hdvr j
  | succ q =>
    exact manyCoordinateIso_inv_over M π hπ q a ha he ρ hρ hex hp hatlas hbc hx hy
      H hdvr j
lemma coordinateIso_forward_compatible (i j : Fin (m + 2)) :
    pullback.fst (c i) (c j) ≫ (e i).hom ≫ d i =
      pullback.snd (c i) (c j) ≫ (e j).hom ≫ d j := by
  cases m with
  | zero =>
    exact twoForward_compatible M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
      hdvr i j
  | succ q =>
    exact manyForward_compatible M π hπ q a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr i j
lemma coordinateIso_backward_compatible (i j : Fin (m + 2)) :
    pullback.fst (d i) (d j) ≫ (e i).inv ≫ c i =
      pullback.snd (d i) (d j) ≫ (e j).inv ≫ c j := by
  cases m with
  | zero =>
    exact twoBackward_compatible M π hπ a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
      hdvr i j
  | succ q =>
    exact manyBackward_compatible M π hπ q a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr i j
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
end -- original EOF scope
end

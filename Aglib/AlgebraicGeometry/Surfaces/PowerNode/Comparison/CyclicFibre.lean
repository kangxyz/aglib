/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.CycleCoordinates
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ComponentComplements
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.ExponentOne
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.SplitNodePinching
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.One
public import Aglib.AlgebraicGeometry.Curves.Models.Components.SubsetCover
public import Aglib.AlgebraicGeometry.Gluing.FiniteClosedCover
public import Aglib.AlgebraicGeometry.Curves.GenericExtension
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR

/-!
# Cyclic geometry of the same actual resolved residue fibre

Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`IntrinsicSplitNode/ResolvedCycle.lean`, lines 42–102, 129–239.
SHA-256: `c042a2bce2ec8245c369f8d3e245c1453e8d43ecb7ec83f02effd830c8d9f68e`.
`IntrinsicSplitNode/AllPositive.lean`, lines 48–83.
SHA-256: `f22ca01eb72fdaafcfe6d71c8fe6221a3c1f7fac35dd757083ff17b7e3137c05`.
`IntrinsicSplitNode/ValueOne.lean`, lines 59–97, 174–281, 301–341.
SHA-256: `456fa148ece80652b570110e61ff7aa374ea52a4d46f3e703d0d2239f1120acf`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open Scheme.Blowup Scheme.PowerNode Scheme.ProjectiveLine
open Scheme.RegularityDescent Scheme.FunctionField.GenericExtension
open Scheme.LocalRing.ResidueFiber Scheme.FiniteClosedCover WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
section ManyComponents
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
  (H : NormalProperCurveGenericExtension.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hdvr : Scheme.ProperBirationalDVRIsomorphismLocus.{u})
local notation "k" => ResidueField R
local notation "πY" => modification M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
local notation "e" => resolvedComponentEquiv M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc (Nat.succ_pos (m + 0))
local notation "i" => indexedComponent M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy H
local notation "ranges" => indexedComponent_range M π hπ m
  a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr

local instance cyclicComponentsFinite : Finite (irreducibleComponents F) :=
  Finite.of_equiv (Option (Fin (m + 1))) e

variable (σ : ResidueField R)
  (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) σ)
  (hne : ρ ≠ σ)
local notation "c" => componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "ec" => componentEquiv M π hπ m a ha he ρ hρ hex hp hatlas hbc
local notation "coord" => coordinateIso M π hπ m a ha he ρ hρ hex hp hatlas hbc
  hx hy H hdvr σ hσ hne
local notation "d" => Scheme.Polygon.componentTarget k (m + 2)
local notation "sF" => pullback.snd πY (Scheme.LocalRing.residueSpecMap R)

/-- Reindexing keeps the actual original inclusion, not merely its range. -/
lemma indexedComponent_reindexed (j : Fin (m + 2)) : i (ec j) = c j := by
  simp only [indexedComponent, Equiv.symm_apply_apply]

include hdvr in
/-- The finite infimum uses the same original component kernels. -/
lemma actualUnionIdeal_eq_native (S : Finset (Fin (m + 2))) :
    unionIdeal c S = unionIdeal i (S.map (ec).toEmbedding) := by
  let : ∀ v, IsClosedImmersion (i v) := fun v =>
    indexedComponent_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr v
  let : ∀ _ : irreducibleComponents F, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  have hm : (fun j => i (ec j)) = c := funext (indexedComponent_reindexed
    M π hπ m a ha he ρ hρ hex hp hatlas hbc H hx hy)
  rw [← hm]
  exact ComponentFamily.reindexedUnionIdeal_eq_native πY i ec S

include hdvr σ hσ hne in
/-- Source-side finite partial intersections are proved from the actual complementary pairs. -/
lemma actualPartialOverlap_family (S : Finset (Fin (m + 2))) :
    ∀ U : Finset (Fin (m + 2)), U ⊆ S → ∀ j ∈ S, j ∉ U →
      IsReduced (pullback (unionMap c U) (c j)) := by
  let : ∀ v, IsClosedImmersion (i v) := fun v =>
    indexedComponent_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr v
  let : ∀ _ : irreducibleComponents F, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  have hm : (fun j => i (ec j)) = c := funext (indexedComponent_reindexed
    M π hπ m a ha he ρ hρ hex hp hatlas hbc H hx hy)
  rw [← hm]
  exact ComponentFamily.reindexedPartialOverlap_family πY i ec S
    (componentOtherTwoPointIso M π hπ m a ha he ρ hρ hex hp hatlas hbc
      H hx hy hdvr σ hσ hne)

/-- Whole-fibre cyclic recognition by actual finite closed-cover descent in both directions. -/
def resolvedCycleIso : Over.mk sF ≅ Over.mk (Scheme.Polygon.structureMap k (m + 2)) := by
  let : IsReduced F := finalSpecialFibre_reduced M π hπ (m + 2) (Nat.succ_pos (m + 1))
    a ha he ρ hρ hex hp hatlas hbc
  let : IsReduced (Scheme.Polygon.cycleScheme k (m + 2)) :=
    Scheme.Polygon.cycleScheme_reduced_from_charts k (m + 2)
  let : ∀ j, IsClosedImmersion (c j) := fun j =>
    componentMap_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr j
  let : ∀ j, IsClosedImmersion (d j) := fun j =>
    Scheme.Polygon.componentTarget_closedImmersion_of_one_lt k (m + 2) (by omega) j
  refine Scheme.FiniteClosedCover.Isomorphism.overIso c d coord Finset.univ
    (actualPartialOverlap_family M π hπ m a ha he ρ hρ hex hp hatlas hbc
      H hx hy hdvr σ hσ hne Finset.univ)
    (Scheme.Polygon.targetPartialOverlap_family k (m + 2) (by omega) Finset.univ)
    (fun firstIndex _ secondIndex _ =>
      coordinateIso_forward_compatible M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy H hdvr σ hσ hne firstIndex secondIndex)
    (fun firstIndex _ secondIndex _ =>
      coordinateIso_backward_compatible M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy H hdvr σ hσ hne firstIndex secondIndex)
    ?_ ?_ sF (Scheme.Polygon.structureMap k (m + 2)) ?_
  · apply Set.eq_univ_of_forall
    intro z
    have hz : z ∈ ⋃ j : Fin (m + 2), Set.range (c j) := by
      rw [componentMap_ranges_cover M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy H hdvr]
      trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨⟨j, Finset.mem_univ j⟩, hj⟩
  · apply Set.eq_univ_of_forall
    intro z
    obtain ⟨j, hj⟩ := Scheme.Polygon.targetComponents_cover k (m + 2) z
    exact Set.mem_iUnion.mpr ⟨⟨j, Finset.mem_univ j⟩,
      (Scheme.Polygon.componentTarget_range k (m + 2) j).symm ▸ hj⟩
  · intro j _
    rw [Scheme.Polygon.componentTarget_over, coordinateIso_over]
    exact (componentMap_base M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j).symm

local notation "iso" => resolvedCycleIso M π hπ m a ha he ρ hρ hex hp hatlas hbc
  H hx hy hdvr σ hσ hne

@[reassoc] lemma resolvedCycleIso_component (j : Fin (m + 2)) :
    c j ≫ (iso).hom.left = (coord j).hom ≫ d j := by
  let : IsReduced F := finalSpecialFibre_reduced M π hπ (m + 2) (Nat.succ_pos (m + 1))
    a ha he ρ hρ hex hp hatlas hbc
  let : IsReduced (Scheme.Polygon.cycleScheme k (m + 2)) :=
    Scheme.Polygon.cycleScheme_reduced_from_charts k (m + 2)
  let : ∀ j, IsClosedImmersion (c j) := fun j =>
    componentMap_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr j
  let : ∀ j, IsClosedImmersion (d j) := fun j =>
    Scheme.Polygon.componentTarget_closedImmersion_of_one_lt k (m + 2) (by omega) j
  unfold resolvedCycleIso
  apply Scheme.FiniteClosedCover.Isomorphism.overIso_hom_component
  exact Finset.mem_univ j

@[reassoc] lemma resolvedCycleIso_inv_component (j : Fin (m + 2)) :
    d j ≫ (iso).inv.left = (coord j).inv ≫ c j := by
  let : IsReduced F := finalSpecialFibre_reduced M π hπ (m + 2) (Nat.succ_pos (m + 1))
    a ha he ρ hρ hex hp hatlas hbc
  let : IsReduced (Scheme.Polygon.cycleScheme k (m + 2)) :=
    Scheme.Polygon.cycleScheme_reduced_from_charts k (m + 2)
  let : ∀ j, IsClosedImmersion (c j) := fun j =>
    componentMap_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr j
  let : ∀ j, IsClosedImmersion (d j) := fun j =>
    Scheme.Polygon.componentTarget_closedImmersion_of_one_lt k (m + 2) (by omega) j
  unfold resolvedCycleIso
  apply Scheme.FiniteClosedCover.Isomorphism.overIso_inv_component
  exact Finset.mem_univ j

@[reassoc] lemma resolvedCycleIso_over :
    (iso).hom.left ≫ Scheme.Polygon.structureMap k (m + 2) = sF := (iso).hom.w

@[reassoc] lemma resolvedCycleIso_inv_over :
    (iso).inv.left ≫ sF = Scheme.Polygon.structureMap k (m + 2) := (iso).inv.w

/-- The same geometry with the proved blowup, curve-extension, smooth-stalk
and proper-birational DVR suppliers filled internally. Regularity descent
uses the actual etale stalk maps through the native chart theorems. -/
def resolvedCycleIsoConcrete :
    Over.mk (pullback.snd
      (modification M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ
        Scheme.Blowup.noetherianBlowupExistence Scheme.Blowup.noetherianBlowupProper
        Scheme.Blowup.blowupAffineAtlas Scheme.Blowup.blowupFlatBaseChange ≫ structureMap W)
      (Scheme.LocalRing.residueSpecMap R)) ≅
    Over.mk (Scheme.Polygon.structureMap k (m + 2)) :=
  resolvedCycleIso M π hπ m a ha he ρ hρ
    Scheme.Blowup.noetherianBlowupExistence Scheme.Blowup.noetherianBlowupProper
    Scheme.Blowup.blowupAffineAtlas Scheme.Blowup.blowupFlatBaseChange
    normalProperCurveGenericExtension hx hy
    Scheme.properBirationalDVRIsomorphismLocus σ hσ hne
end ManyComponents

section PositiveExponent
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π)
  (n : ℕ) (hn : 0 < n) (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (σ : ResidueField R)
  (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) σ)
  (hne : ρ ≠ σ)
local notation "k" => ResidueField R
local notation "πY" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W
local notation "sF" => pullback.snd πY (Scheme.LocalRing.residueSpecMap R)

local notation "σY" => infinityLift M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "sectionY" => Scheme.LocalRing.ResidueFiber.«section» πY σY
  (infinityLift_structure M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)

/-- The same actual residue section is carried to the coefficient-equation infinity. -/
@[reassoc] theorem exponentOneResidueEquationIso_section (h : n = 1) :
    sectionY ≫
      (exponentOneResidueEquationIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.left =
        infinitySection (W.baseChange k) := by
  have hs : sectionY ≫
      (exponentOneResiduePullbackIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.left =
        baseChangedInfinitySection (S := k) W := by
    apply pullback.hom_ext
    · rw [Category.assoc, exponentOneResiduePullbackIso_fst, ← Category.assoc,
        Scheme.LocalRing.ResidueFiber.section_projection, Category.assoc,
        infinityLift_triangle]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, exponentOneResiduePullbackIso_snd,
        Scheme.LocalRing.ResidueFiber.section_structureMap]
      exact (pullback.lift_snd _ _ _).symm
  change sectionY ≫
    ((exponentOneResiduePullbackIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.left ≫
      (specialCoefficientIso W).inv) = _
  rw [← Category.assoc, hs]
  apply (cancel_mono (specialCoefficientIso W).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (coefficientBaseChangeIso_pointed (S := k) W).symm

/-- Exponent one uses its actual residue equation and the actual one-cycle bridge. -/
def exponentOneCycleIso (h : n = 1) :
    Over.mk sF ≅ Over.mk (Scheme.Polygon.structureMap k 1) :=
  exponentOneResidueEquationIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc h ≪≫
    WeierstrassCurve.Projective.SplitNode.originalIsoPinchedOver
      k (W.map (IsLocalRing.residue R)) x y ρ σ he hx hy hne
      (by simpa only [WeierstrassCurve.CriticalNeighborhood.SplitTangent,
        WeierstrassCurve.translate_a1, WeierstrassCurve.translate_a2,
        WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂] using hρ)
      (by simpa only [WeierstrassCurve.CriticalNeighborhood.SplitTangent,
        WeierstrassCurve.translate_a1, WeierstrassCurve.translate_a2,
        WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂] using hσ) ≪≫
    (Scheme.Polygon.cycleOneOverIso k).symm

/-- The actual original specialized section keeps the same one-cycle infinity point. -/
@[reassoc] theorem exponentOneCycleIso_section (h : n = 1) :
    sectionY ≫ (exponentOneCycleIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
      hx hy σ hσ hne h).hom.left =
    Scheme.PinchedLine.infinitySection k ≫ (Scheme.Polygon.cycleOneOverIso k).inv.left := by
  have hsection : sectionY ≫
      (exponentOneResidueEquationIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.left =
      infinitySection (W.map (IsLocalRing.residue R)) :=
    exponentOneResidueEquationIso_section M π hπ n hn a ha he ρ hρ hex hp hatlas hbc h
  change sectionY ≫
      ((exponentOneResidueEquationIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.left ≫
        (WeierstrassCurve.Projective.SplitNode.originalIsoPinchedOver
          k (W.map (IsLocalRing.residue R)) x y ρ σ he hx hy hne _ _).hom.left ≫
        (Scheme.Polygon.cycleOneOverIso k).inv.left) = _
  rw [← Category.assoc, hsection,
    ← Category.assoc, WeierstrassCurve.Projective.SplitNode.originalIsoPinchedOver_infinity]

variable (H : NormalProperCurveGenericExtension.{u})
  (hdvr : Scheme.ProperBirationalDVRIsomorphismLocus.{u})

/-- Reindex only the actual exponent of the same original Run. -/
def resolvedCycleIsoOfTwoLe (h₂ : 2 ≤ n) :
    Over.mk sF ≅ Over.mk (Scheme.Polygon.structureMap k n) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ m =>
      exact resolvedCycleIso M π hπ m a ha he ρ hρ hex hp hatlas hbc
        H hx hy hdvr σ hσ hne

/-- Same-Run geometry for every positive actual exponent, with separate one/many proofs. -/
def resolvedCycleIsoOfPositive : Over.mk sF ≅ Over.mk (Scheme.Polygon.structureMap k n) := by
  by_cases h : n = 1
  · subst n
    exact exponentOneCycleIso M π hπ 1 hn a ha he ρ hρ hex hp hatlas hbc hx hy σ hσ hne rfl
  · exact resolvedCycleIsoOfTwoLe M π hπ n hn a ha he ρ hρ hex hp hatlas hbc hx hy
      σ hσ hne H hdvr (by omega)

/-- The actual positive-exponent comparison with all available theorem-family
suppliers applied to the same original Run and actual etale charts. -/
def resolvedCycleIsoOfPositiveConcrete :
    Over.mk (pullback.snd
      (modification M π hπ n hn a ha he ρ hρ
        Scheme.Blowup.noetherianBlowupExistence Scheme.Blowup.noetherianBlowupProper
        Scheme.Blowup.blowupAffineAtlas Scheme.Blowup.blowupFlatBaseChange ≫ structureMap W)
      (Scheme.LocalRing.residueSpecMap R)) ≅
    Over.mk (Scheme.Polygon.structureMap k n) :=
  resolvedCycleIsoOfPositive M π hπ n hn a ha he ρ hρ
    Scheme.Blowup.noetherianBlowupExistence Scheme.Blowup.noetherianBlowupProper
    Scheme.Blowup.blowupAffineAtlas Scheme.Blowup.blowupFlatBaseChange
    hx hy σ hσ hne normalProperCurveGenericExtension
    Scheme.properBirationalDVRIsomorphismLocus
end PositiveExponent
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
end

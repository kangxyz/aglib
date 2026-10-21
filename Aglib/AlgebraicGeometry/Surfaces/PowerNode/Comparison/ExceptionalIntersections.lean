/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.PullbackTransport
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.OuterStrictIntersections

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ExceptionalIntersections`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`18259629b0c8327652670c40dc955a562ac41b17f57991e4fa7260e8dc29d8e5`.
Actual exceptional intersections and neighboring-point squares transported through the same finite
  modification. Index lemmas support the original geometric maps; no terminal model, marking or
  component-intersection record is introduced.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode WeierstrassCurve
open AlgebraicGeometry.Scheme.FunctionField AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

open _root_.AlgebraicGeometry.Scheme (SmoothClosedPointDimension SmoothFieldRegularity)

/-!
# Exceptional intersection transport and neighbor squares

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section WeierstrassExceptionalIntersections

/-! The exact local P1/P1 intersections transported to the same global resolved
special fibre. Both residue-point projections remain the original sections. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (q : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (q + 1)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "P" => originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc
local notation "J" => originalExceptionalToSpecial M π hπ (q + 1) (Nat.succ_pos q) a ha he ρ hρ
  hex hp hatlas hbc
local notation "L" => Resolution.exceptionalToSpecial π hπ hex hp hatlas q
local notation "Q" => Resolution.exceptionalP1 π hπ hex hp hatlas q

lemma originalExceptionalP1_intersection_transport (i j : Fin q) {Z : Scheme.{u}}
    (s t : Z ⟶ AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 (ResidueField R))
    (H : IsPullback s t (Resolution.interiorComponent π hπ hex hp hatlas q i)
      (Resolution.interiorComponent π hπ hex hp hatlas q j)) :
    IsPullback s t (P i) (P j) := by
  have H' : IsPullback s t (Q i ≫ L) (Q j ≫ L) := by
    simpa only [Resolution.exceptionalP1_special] using H
  exact Scheme.Pullback.Transport.exceptional_intersection_postcompose
    (Scheme.Pullback.Transport.exceptional_intersection_cancel L H') J

/-- Adjacent exceptional curves meet in the actual original residue point,
with their retained finish/start morphisms as the literal projections. -/
lemma originalExceptionalP1_adjacent_isPullback (i j : Fin q)
    (hij : Resolution.ChainAdjacent q (.inr i) (.inr j)) :
    IsPullback (Resolution.interiorFinish (R := R) q i)
      (Resolution.interiorStart (R := R) q j) (P i) (P j) :=
  originalExceptionalP1_intersection_transport M π hπ q a ha he ρ hρ hex hp hatlas hbc i j _ _
    (Resolution.chainAdjacent_isPullback π hπ hex hp hatlas hij)

lemma originalExceptionalP1_nonadjacent_disjoint (i j : Fin q) (hij : i ≠ j)
    (hij' : ¬ Resolution.ChainAdjacent q (.inr i) (.inr j))
    (hji' : ¬ Resolution.ChainAdjacent q (.inr j) (.inr i)) :
    Disjoint (Set.range (P i)) (Set.range (P j)) := by
  have H := Resolution.nonadjacent_components_disjoint π hπ hex hp hatlas q
    (.inr i) (.inr j) (fun h => hij (Sum.inr.inj h)) hij' hji'
  apply Set.disjoint_left.mpr
  rintro z ⟨p,rfl⟩ ⟨r,hr⟩
  have hE : Q j r = Q i p := (J).isClosedEmbedding.injective hr
  have hL : Resolution.interiorComponent π hπ hex hp hatlas q j r =
      Resolution.interiorComponent π hπ hex hp hatlas q i p := by
    have hh := congrArg L hE
    change (Q j ≫ L) r = (Q i ≫ L) p at hh
    simpa only [Resolution.exceptionalP1_special] using hh
  exact Set.disjoint_left.mp H ⟨p,rfl⟩ ⟨r,hL⟩

lemma originalExceptionalP1_nonadjacent_empty (i j : Fin q) (hij : i ≠ j)
    (hij' : ¬ Resolution.ChainAdjacent q (.inr i) (.inr j))
    (hji' : ¬ Resolution.ChainAdjacent q (.inr j) (.inr i)) :
    IsEmpty (pullback (P i) (P j) : Scheme.{u}) :=
  Scheme.isEmpty_pullback_iff.mpr
    (originalExceptionalP1_nonadjacent_disjoint M π hπ q a ha he ρ hρ hex hp hatlas hbc i j hij
      hij' hji')

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassExceptionalIntersections


section WeierstrassExceptionalEndpointSupport

/-! Exact support exclusions at the retained exceptional endpoint sections. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (q : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (q + 1)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "P" => originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc
local notation "J" => originalExceptionalToSpecial M π hπ (q + 1) (Nat.succ_pos q) a ha he ρ hρ
  hex hp hatlas hbc
local notation "L" => Resolution.exceptionalToSpecial π hπ hex hp hatlas q
local notation "Q" => Resolution.exceptionalP1 π hπ hex hp hatlas q

/-- The actual chain order determines adjacency of two exceptional indices. -/
lemma exceptional_adjacent_iff (i j : Fin q) :
    Resolution.ChainAdjacent q (.inr i) (.inr j) ↔ i.val + 1 = j.val := by
  rw [Resolution.chainAdjacent_iff_consecutive]
  simp only [Resolution.extensionIndexInv, Fin.val_succ, Fin.val_castSucc]
  omega

lemma originalExceptionalP1_other_preimage (i j : Fin q) (hij : i ≠ j) :
    (P i) ⁻¹' Set.range (P j) ⊆
      Set.range (Resolution.interiorStart (R := R) q i) ∪
      Set.range (Resolution.interiorFinish (R := R) q i) := by
  intro z hz
  by_cases hf : Resolution.ChainAdjacent q (.inr i) (.inr j)
  · right
    rw [Scheme.Pullback.Fibre.pullback_range_snd
      (originalExceptionalP1_adjacent_isPullback M π hπ q a ha he ρ hρ hex hp hatlas hbc i j
        hf).flip]
    exact hz
  by_cases hr : Resolution.ChainAdjacent q (.inr j) (.inr i)
  · left
    rw [Scheme.Pullback.Fibre.pullback_range_snd
      (originalExceptionalP1_adjacent_isPullback M π hπ q a ha he ρ hρ hex hp hatlas hbc j i hr)]
    exact hz
  exact False.elim (Set.disjoint_left.mp
    (originalExceptionalP1_nonadjacent_disjoint M π hπ q a ha he ρ hρ hex hp hatlas hbc i j hij hf
      hr)
    ⟨z,rfl⟩ hz)

/-- An actual start endpoint lies on another exceptional component exactly
when that component is its preceding chain neighbor. -/
lemma originalExceptionalP1_start_mem_iff (i j : Fin q) (hij : i ≠ j)
    (z : Spec (.of (ResidueField R))) :
    (Resolution.interiorStart (R := R) q i ≫ P i) z ∈ Set.range (P j) ↔
      j.val + 1 = i.val := by
  constructor
  · intro hz
    by_cases hr : Resolution.ChainAdjacent q (.inr j) (.inr i)
    · exact (exceptional_adjacent_iff q j i).mp hr
    by_cases hf : Resolution.ChainAdjacent q (.inr i) (.inr j)
    · have hfz : Resolution.interiorStart (R := R) q i z ∈
          Set.range (Resolution.interiorFinish (R := R) q i) := by
        rw [Scheme.Pullback.Fibre.pullback_range_snd
          (originalExceptionalP1_adjacent_isPullback M π hπ q a ha he ρ hρ hex hp hatlas hbc i j
            hf).flip]
        exact hz
      exact False.elim (Set.disjoint_left.mp (Resolution.interior_endpoints_disjoint q i)
        ⟨z,rfl⟩ hfz)
    exact False.elim (Set.disjoint_left.mp
      (originalExceptionalP1_nonadjacent_disjoint M π hπ q a ha he ρ hρ hex hp hatlas hbc i j hij
        hf hr)
      ⟨Resolution.interiorStart (R := R) q i z,rfl⟩ hz)
  · intro h
    have H := originalExceptionalP1_adjacent_isPullback M π hπ q a ha he ρ hρ hex hp hatlas hbc
      j i ((exceptional_adjacent_iff q j i).mpr h)
    refine ⟨Resolution.interiorFinish (R := R) q j z,?_⟩
    exact congrArg (fun f => f z) H.w

/-- An actual finish endpoint lies on another exceptional component exactly
when that component is its following chain neighbor. -/
lemma originalExceptionalP1_finish_mem_iff (i j : Fin q) (hij : i ≠ j)
    (z : Spec (.of (ResidueField R))) :
    (Resolution.interiorFinish (R := R) q i ≫ P i) z ∈ Set.range (P j) ↔
      i.val + 1 = j.val := by
  constructor
  · intro hz
    by_cases hf : Resolution.ChainAdjacent q (.inr i) (.inr j)
    · exact (exceptional_adjacent_iff q i j).mp hf
    by_cases hr : Resolution.ChainAdjacent q (.inr j) (.inr i)
    · have hrz : Resolution.interiorFinish (R := R) q i z ∈
          Set.range (Resolution.interiorStart (R := R) q i) := by
        rw [Scheme.Pullback.Fibre.pullback_range_snd
          (originalExceptionalP1_adjacent_isPullback M π hπ q a ha he ρ hρ hex hp hatlas hbc j i
            hr)]
        exact hz
      exact False.elim (Set.disjoint_left.mp (Resolution.interior_endpoints_disjoint q i)
        hrz ⟨z,rfl⟩)
    exact False.elim (Set.disjoint_left.mp
      (originalExceptionalP1_nonadjacent_disjoint M π hπ q a ha he ρ hρ hex hp hatlas hbc i j hij
        hf hr)
      ⟨Resolution.interiorFinish (R := R) q i z,rfl⟩ hz)
  · intro h
    have H := originalExceptionalP1_adjacent_isPullback M π hπ q a ha he ρ hρ hex hp hatlas hbc
      i j ((exceptional_adjacent_iff q i j).mpr h)
    refine ⟨Resolution.interiorStart (R := R) q j z,?_⟩
    exact congrArg (fun f => f z) H.w.symm

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassExceptionalEndpointSupport


section WeierstrassStrictExceptionalSupport

/-! Derived exact strict incidence on the actual exceptional endpoint sections.
The dependency attachment squares are geometric outputs, not supplied premises. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
  AlgebraicGeometry.Scheme.RegularityDescent
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 3)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "k" => ResidueField R
local notation "P" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ (m + 3) (Nat.succ_pos (m + 2)) a ha he ρ hρ
  hex hp hatlas hbc
local notation "N" => Resolution.interiorComponent π hπ hex hp hatlas (m + 2)
local notation "D" => OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas
local notation "E" => Resolution.resolve π hπ hex hp hatlas (m + 1)
local notation "L" => Resolution.resolveLeftEnd π hπ hex hp hatlas (m + 2)
local notation "Rₑ" => Resolution.resolveRightEnd π hπ hex hp hatlas (m + 2)
local notation "last" => (Fin.last (m + 1) : Fin (m + 2))

variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hext : NormalProperCurveGenericExtension.{u})
  (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u})
local notation "e" => strictNormalizationIsoPositive M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "f" => strictP1ToFinal M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc hx hy hext
local notation "base" => pullback.snd
  (modification M π hπ (m + 3) (Nat.succ_pos (m + 2)) a ha he ρ hρ hex hp hatlas hbc ≫
    structureMap W)
  (Resolution.residueBase (R := R))

include hdvr

lemma strictP1_exceptional_preimage_subset (j : Fin (m + 2)) :
    (P j) ⁻¹' Set.range f ⊆
      Set.range (Resolution.interiorStart (R := R) (m + 2) j) ∪
      Set.range (Resolution.interiorFinish (R := R) (m + 2) j) := by
  intro z hz
  by_cases h0 : j = 0
  · subst j
    left
    rw [Scheme.Pullback.Fibre.pullback_range_snd
      (originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy hext hdvr)]
    exact hz
  by_cases hl : j = last
  · subst j
    right
    rw [Scheme.Pullback.Fibre.pullback_range_snd
      (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy hext hdvr)]
    exact hz
  exact False.elim (Set.disjoint_left.mp (Scheme.isEmpty_pullback_iff.mp
    (strictExceptionalInterior_empty M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext j h0 hl))
    hz ⟨z,rfl⟩)

lemma exceptionalStart_strict_mem_iff (j : Fin (m + 2)) (z : Spec (.of k)) :
    (Resolution.interiorStart (R := R) (m + 2) j ≫ P j) z ∈ Set.range f ↔ j = 0 := by
  constructor
  · intro hz
    by_cases h0 : j = 0
    · exact h0
    by_cases hl : j = last
    · subst j
      have hf : Resolution.interiorStart (R := R) (m + 2) last z ∈
          Set.range (Resolution.interiorFinish (R := R) (m + 2) last) := by
        rw [Scheme.Pullback.Fibre.pullback_range_snd
          (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
            hx hy hext hdvr)]
        exact hz
      exact False.elim (Set.disjoint_left.mp (Resolution.interior_endpoints_disjoint (m + 2) last)
        ⟨z,rfl⟩ hf)
    exact False.elim (Set.disjoint_left.mp (Scheme.isEmpty_pullback_iff.mp
      (strictExceptionalInterior_empty M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext j h0 hl))
      hz ⟨Resolution.interiorStart (R := R) (m + 2) j z,rfl⟩)
  · intro h
    subst j
    refine ⟨originalLeftStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr z,?_⟩
    exact congrArg (fun g => g z)
      (originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy hext hdvr).w

lemma exceptionalFinish_strict_mem_iff (j : Fin (m + 2)) (z : Spec (.of k)) :
    (Resolution.interiorFinish (R := R) (m + 2) j ≫ P j) z ∈ Set.range f ↔ j = last := by
  constructor
  · intro hz
    by_cases hl : j = last
    · exact hl
    by_cases h0 : j = 0
    · subst j
      have hs : Resolution.interiorFinish (R := R) (m + 2) 0 z ∈
          Set.range (Resolution.interiorStart (R := R) (m + 2) 0) := by
        rw [Scheme.Pullback.Fibre.pullback_range_snd
          (originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
            hx hy hext hdvr)]
        exact hz
      exact False.elim (Set.disjoint_left.mp (Resolution.interior_endpoints_disjoint (m + 2) 0)
        hs ⟨z,rfl⟩)
    exact False.elim (Set.disjoint_left.mp (Scheme.isEmpty_pullback_iff.mp
      (strictExceptionalInterior_empty M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy hext j h0 hl))
      hz ⟨Resolution.interiorFinish (R := R) (m + 2) j z,rfl⟩)
  · intro h
    subst j
    refine ⟨originalRightStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr z,?_⟩
    exact congrArg (fun g => g z)
      (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy hext hdvr).w

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictExceptionalSupport


section ExceptionalNeighborIndices

/-! The actual predecessor/successor labels after the two affine ends are
identified with the single strict component. No component count is assumed. -/
noncomputable section
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {q : ℕ}

/-- The preceding exceptional index, or `none` at the left end of the chain. -/
def previousExceptional (i : Fin q) : Option (Fin q) :=
  if h : 0 < i.val then some ⟨i.val-1,by omega⟩ else none

/-- The following exceptional index, or `none` at the right end of the chain. -/
def followingExceptional (i : Fin q) : Option (Fin q) :=
  if h : i.val+1 < q then some ⟨i.val+1,h⟩ else none

lemma previousExceptional_eq_none (i : Fin q) :
    previousExceptional i = none ↔ i.val = 0 := by
  unfold previousExceptional
  split_ifs
  all_goals simp_all
  all_goals omega

lemma followingExceptional_eq_none (i : Fin q) :
    followingExceptional i = none ↔ i.val+1 = q := by
  unfold followingExceptional
  split_ifs <;> simp_all <;> omega

lemma previousExceptional_eq_some (i j : Fin q) :
    previousExceptional i = some j ↔ j.val+1 = i.val := by
  unfold previousExceptional
  split_ifs with h
  · rw [Option.some.injEq,Fin.ext_iff]
    change (i.val - 1 = j.val) ↔ j.val + 1 = i.val
    omega
  · constructor
    · intro hnone
      cases hnone
    · intro hnum
      exfalso
      omega

lemma followingExceptional_eq_some (i j : Fin q) :
    followingExceptional i = some j ↔ i.val+1 = j.val := by
  unfold followingExceptional
  split_ifs with h
  · rw [Option.some.injEq,Fin.ext_iff]
  · constructor
    · intro hnone
      cases hnone
    · intro hnum
      exfalso
      omega

lemma previousExceptional_ne_self (i : Fin q) : previousExceptional i ≠ some i := by
  intro h
  have := (previousExceptional_eq_some i i).mp h
  omega

lemma followingExceptional_ne_self (i : Fin q) : followingExceptional i ≠ some i := by
  intro h
  have := (followingExceptional_eq_some i i).mp h
  omega

lemma exceptional_neighbors_distinct (hq : 1 < q) (i : Fin q) :
    previousExceptional i ≠ followingExceptional i := by
  intro h
  cases hp : previousExceptional i with
  | none =>
    have hf : followingExceptional i = none := h.symm.trans hp
    have h₀ := (previousExceptional_eq_none i).mp hp
    have h₁ := (followingExceptional_eq_none i).mp hf
    omega
  | some j =>
    have hf : followingExceptional i = some j := h.symm.trans hp
    have h₀ := (previousExceptional_eq_some i j).mp hp
    have h₁ := (followingExceptional_eq_some i j).mp hf
    omega

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end ExceptionalNeighborIndices


section WeierstrassExceptionalNeighborSquares

/-! Actual predecessor/successor point squares, not an assumed incidence family. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
  AlgebraicGeometry.Scheme.RegularityDescent
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 3)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "k" => ResidueField R
local notation "P" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ (m + 3) (Nat.succ_pos (m + 2)) a ha he ρ hρ
  hex hp hatlas hbc
local notation "N" => Resolution.interiorComponent π hπ hex hp hatlas (m + 2)
local notation "D" => OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas
local notation "E" => Resolution.resolve π hπ hex hp hatlas (m + 1)
local notation "L" => Resolution.resolveLeftEnd π hπ hex hp hatlas (m + 2)
local notation "Rₑ" => Resolution.resolveRightEnd π hπ hex hp hatlas (m + 2)
local notation "last" => (Fin.last (m + 1) : Fin (m + 2))

variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hext : NormalProperCurveGenericExtension.{u})
  (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u})
local notation "e" => strictNormalizationIsoPositive M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "f" => strictP1ToFinal M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc hx hy hext
local notation "base" => pullback.snd
  (modification M π hπ (m + 3) (Nat.succ_pos (m + 2)) a ha he ρ hρ hex hp hatlas hbc ≫
    structureMap W)
  (Resolution.residueBase (R := R))

local notation "PM" => resolvedP1Map M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc hx hy hext

/-- The predecessor-side endpoint is an already constructed actual point;
only the first exceptional component uses the actual strict endpoint. -/
def resolvedPreviousPoint (j : Fin (m + 2)) : Spec (.of k) ⟶
  AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k :=
  match previousExceptional j with
  | none => originalLeftStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr
  | some l => Resolution.interiorFinish (R := R) (m + 2) l

/-- The starting point of the following exceptional component, or the right strict-component
attachment at the end of the chain. -/
def resolvedFollowingPoint (j : Fin (m + 2)) : Spec (.of k) ⟶
  AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 k :=
  match followingExceptional j with
  | none => originalRightStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr
  | some l => Resolution.interiorStart (R := R) (m + 2) l

lemma resolvedPreviousPoint_isPullback (j : Fin (m + 2)) :
    IsPullback (resolvedPreviousPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr j)
      (Resolution.interiorStart (R := R) (m + 2) j)
      (PM (previousExceptional j)) (P j) := by
  cases hprev : previousExceptional j with
  | none =>
    have hj : j = 0 := Fin.ext ((previousExceptional_eq_none j).mp hprev)
    subst j
    simpa only [resolvedPreviousPoint,hprev,resolvedP1Map] using
      originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy hext hdvr
  | some l =>
    have hadj := (exceptional_adjacent_iff (m + 2) l j).mpr
      ((previousExceptional_eq_some j l).mp hprev)
    simpa only [resolvedPreviousPoint,hprev,resolvedP1Map] using
      originalExceptionalP1_adjacent_isPullback M π hπ (m + 2) a ha he ρ hρ
        hex hp hatlas hbc l j hadj

lemma resolvedFollowingPoint_isPullback (j : Fin (m + 2)) :
    IsPullback (resolvedFollowingPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr j)
      (Resolution.interiorFinish (R := R) (m + 2) j)
      (PM (followingExceptional j)) (P j) := by
  cases hnext : followingExceptional j with
  | none =>
    have hv := (followingExceptional_eq_none j).mp hnext
    have hj : j = last := Fin.ext (by simp only [Fin.val_last]; omega)
    subst j
    simpa only [resolvedFollowingPoint,hnext,resolvedP1Map] using
      originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
        hx hy hext hdvr
  | some l =>
    have hadj := (exceptional_adjacent_iff (m + 2) j l).mpr
      ((followingExceptional_eq_some j l).mp hnext)
    simpa only [resolvedFollowingPoint,hnext,resolvedP1Map] using
      (originalExceptionalP1_adjacent_isPullback M π hπ (m + 2) a ha he ρ hρ
        hex hp hatlas hbc j l hadj).flip

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassExceptionalNeighborSquares

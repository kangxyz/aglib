/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.FiberChart
public import Aglib.AlgebraicGeometry.Limits.OpenChartIntersection
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.StrictTransformCover

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.NodeChainIntersections`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`ec20912b7b45f2ac9a32c968248ba6eadc7d63b54bda08bbe32a45670ca11ef0`.
Actual recursive node-chain scheme intersections, original endpoint maps and first-blowup squares;
  all original DVR and blowup-family conditions remain explicit.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

/-!
# Open-chart intersection extension and node-chain incidence

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/



section NodeExtendedIntersections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

instance extensionChart_open (q : ℕ) (a : ComponentIndex q) :
    IsOpenImmersion (extensionChart (R := R) q a) := by
  cases a <;> dsimp [extensionChart] <;> infer_instance

lemma leftNewP1_range_subset (q : ℕ) :
    Set.range (resolveLeftNewP1 π hπ hex hp ha q) ⊆
      Set.range (recursiveMiddleChart π hπ hex hp ha q) ∪
        Set.range (leftFibreChart (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (q + 1))) := by
  rw [projective_map_range, resolveLeftNewP1_old_chart, resolveLeftNewP1_new_chart]
  exact Set.union_subset_union (morphism_range_comp_subset _ _) (morphism_range_comp_subset _ _)

lemma rightNewP1_range_subset (q : ℕ) :
    Set.range (resolveRightNewP1 π hπ hex hp ha q) ⊆
      Set.range (recursiveMiddleChart π hπ hex hp ha q) ∪
        Set.range (rightFibreChart (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (q + 1))) := by
  rw [projective_map_range, resolveRightNewP1_old_chart, resolveRightNewP1_new_chart]
  exact Set.union_subset_union (morphism_range_comp_subset _ _) (morphism_range_comp_subset _ _)

lemma newP1_intersection_support (q : ℕ) :
    Set.range (resolveLeftNewP1 π hπ hex hp ha q) ∩
      Set.range (resolveRightNewP1 π hπ hex hp ha q) ⊆
        Set.range (recursiveMiddleChart π hπ hex hp ha q) := by
  intro z hz
  rcases leftNewP1_range_subset π hπ hex hp ha q hz.1 with hm | hl
  · exact hm
  rcases rightNewP1_range_subset π hπ hex hp ha q hz.2 with hm | hr
  · exact hm
  exact False.elim (Set.disjoint_left.mp (positive_outer_fibres_disjoint hπ q
    (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1))) hl hr)

lemma extended_intersection_support (q : ℕ) (a b : ComponentIndex q) (hab : a ≠ b) :
    Set.range (extendedComponent π hπ hex hp ha q a) ∩
      Set.range (extendedComponent π hπ hex hp ha q b) ⊆
        Set.range (recursiveMiddleChart π hπ hex hp ha q) := by
  rcases a with a | a
  · rcases b with b | b
    · fin_cases a <;> fin_cases b
      · exact False.elim (hab rfl)
      · exact newP1_intersection_support π hπ hex hp ha q
      · intro z hz
        exact newP1_intersection_support π hπ hex hp ha q ⟨hz.2, hz.1⟩
      · exact False.elim (hab rfl)
    · exact fun z hz => morphism_range_comp_subset _ _ hz.2
  · exact fun z hz => morphism_range_comp_subset _ _ hz.1

/-- Every actual old scheme-theoretic intersection extends with its original
maps through the compactifications; the support premise is proved above. -/
lemma extended_components_isPullback (q : ℕ) (a b : ComponentIndex q) (hab : a ≠ b)
    {P : Scheme.{u}} (s : P ⟶ componentScheme (R := R) q a)
    (t : P ⟶ componentScheme (R := R) q b)
    (H : IsPullback s t (componentMap π hπ hex hp ha q a) (componentMap π hπ hex hp ha q b)) :
    IsPullback (s ≫ extensionChart (R := R) q a) (t ≫ extensionChart (R := R) q b)
      (extendedComponent π hπ hex hp ha q a) (extendedComponent π hπ hex hp ha q b) :=
  AlgebraicGeometry.isPullback_of_openCharts_of_range_inter
    (recursiveMiddleChart π hπ hex hp ha q) (extensionChart (R := R) q a) (extensionChart (R := R)
      q b)
    (componentMap π hπ hex hp ha q a) (componentMap π hπ hex hp ha q b)
    (extendedComponent π hπ hex hp ha q a) (extendedComponent π hπ hex hp ha q b)
    s t (extendedComponent_isPullback π hπ hex hp ha q a)
    (extendedComponent_isPullback π hπ hex hp ha q b) H
    (extended_intersection_support π hπ hex hp ha q a b hab)

lemma extended_components_disjoint (q : ℕ) (a b : ComponentIndex q) (hab : a ≠ b)
    (H : Disjoint (Set.range (componentMap π hπ hex hp ha q a))
      (Set.range (componentMap π hπ hex hp ha q b))) :
    Disjoint (Set.range (extendedComponent π hπ hex hp ha q a))
      (Set.range (extendedComponent π hπ hex hp ha q b)) := by
  rw [Set.disjoint_left]
  intro z hza hzb
  obtain ⟨x, hx⟩ := extended_intersection_support π hπ hex hp ha q a b hab ⟨hza,hzb⟩
  have hax : x ∈ recursiveMiddleChart π hπ hex hp ha q ⁻¹'
      Set.range (extendedComponent π hπ hex hp ha q a) := by
    change recursiveMiddleChart π hπ hex hp ha q x ∈ Set.range (extendedComponent π hπ hex hp ha q
      a)
    rw [hx]
    exact hza
  have hbx : x ∈ recursiveMiddleChart π hπ hex hp ha q ⁻¹'
      Set.range (extendedComponent π hπ hex hp ha q b) := by
    change recursiveMiddleChart π hπ hex hp ha q x ∈ Set.range (extendedComponent π hπ hex hp ha q
      b)
    rw [hx]
    exact hzb
  rw [extendedComponent_preimage_middle] at hax hbx
  exact Set.disjoint_left.mp H hax hbx

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExtendedIntersections


section NodeChainEndpoints

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

/-- The recursively oriented starting section of an interior projective component. -/
def interiorStart : (q : ℕ) → Fin q → (Spec (.of k) ⟶ projectiveP1 k)
  | 0, i => Fin.elim0 i
  | 1, _ => Reciprocal.zeroSection k
  | q + 2, i => Fin.cases (Reciprocal.infinitySection k)
      (Fin.lastCases (Reciprocal.zeroSection k) (interiorStart q)) i

/-- The recursively oriented finishing section of an interior projective component. -/
def interiorFinish : (q : ℕ) → Fin q → (Spec (.of k) ⟶ projectiveP1 k)
  | 0, i => Fin.elim0 i
  | 1, _ => Reciprocal.infinitySection k
  | q + 2, i => Fin.cases (Reciprocal.zeroSection k)
      (Fin.lastCases (Reciprocal.infinitySection k) (interiorFinish q)) i

/-- The affine endpoint for an end component, or the starting section for an interior component. -/
def componentStart (q : ℕ) : ∀ a : ComponentIndex q,
    Spec (.of k) ⟶ componentScheme (R := R) q a
  | .inl _ => Cross.endpoint k
  | .inr i => interiorStart (R := R) q i

/-- The affine endpoint for an end component, or the finishing section for an interior component. -/
def componentFinish (q : ℕ) : ∀ a : ComponentIndex q,
    Spec (.of k) ⟶ componentScheme (R := R) q a
  | .inl _ => Cross.endpoint k
  | .inr i => interiorFinish (R := R) q i

lemma extensionIndex_rightInverse (q : ℕ) :
    Function.LeftInverse (extensionIndex q) (extensionIndexInv q) := by
  rintro (a | i)
  · fin_cases a
    · rfl
    · simp only [extensionIndexInv, extensionIndex, Fin.cases_succ, Fin.lastCases_last]
      rfl
  · simp only [extensionIndexInv, extensionIndex, Fin.cases_succ, Fin.lastCases_castSucc]

lemma extensionIndexInv_injective (q : ℕ) : Function.Injective (extensionIndexInv q) :=
  (extensionIndex_rightInverse q).injective

lemma interiorStart_extension (q : ℕ) (a : ComponentIndex q) (ha : a ≠ .inl 0) :
    componentStart (R := R) q a ≫ extensionChart (R := R) q a =
      interiorStart (R := R) (q + 2) (extensionIndexInv q a) := by
  rcases a with a | a
  · fin_cases a
    · exact False.elim (ha rfl)
    · simp only [componentStart, extensionChart, extensionIndexInv, interiorStart,
        Fin.cases_succ, Fin.lastCases_last]
      rfl
  · simp only [componentStart, extensionChart, extensionIndexInv, interiorStart,
      Fin.cases_succ, Fin.lastCases_castSucc, Category.comp_id]

lemma interiorFinish_extension (q : ℕ) (a : ComponentIndex q) (ha : a ≠ .inl 1) :
    componentFinish (R := R) q a ≫ extensionChart (R := R) q a =
      interiorFinish (R := R) (q + 2) (extensionIndexInv q a) := by
  rcases a with a | a
  · fin_cases a
    · rfl
    · exact False.elim (ha rfl)
  · simp only [componentFinish, extensionChart, extensionIndexInv, interiorFinish,
      Fin.cases_succ, Fin.lastCases_castSucc, Category.comp_id]

/-- Oriented adjacency of the recursively ordered actual component family. -/
inductive ChainAdjacent : (q : ℕ) → ComponentIndex q → ComponentIndex q → Prop
  | base : ChainAdjacent 0 (.inl 0) (.inl 1)
  | twoLeft : ChainAdjacent 1 (.inl 0) (.inr 0)
  | twoRight : ChainAdjacent 1 (.inr 0) (.inl 1)
  | stepLeft (q : ℕ) : ChainAdjacent (q + 2) (.inl 0) (.inr 0)
  | stepRight (q : ℕ) : ChainAdjacent (q + 2) (.inr (Fin.last q).succ) (.inl 1)
  | stepInterior {q : ℕ} {a b : ComponentIndex q} (h : ChainAdjacent q a b) :
      ChainAdjacent (q + 2) (.inr (extensionIndexInv q a)) (.inr (extensionIndexInv q b))

lemma ChainAdjacent.first_ne_right {q : ℕ} {a b : ComponentIndex q}
    (h : ChainAdjacent q a b) : a ≠ .inl 1 := by cases h <;> simp
lemma ChainAdjacent.second_ne_left {q : ℕ} {a b : ComponentIndex q}
    (h : ChainAdjacent q a b) : b ≠ .inl 0 := by cases h <;> simp
lemma ChainAdjacent.ne {q : ℕ} {a b : ComponentIndex q}
    (h : ChainAdjacent q a b) : a ≠ b := by
  induction h with
  | base => simp
  | twoLeft => simp
  | twoRight => simp
  | stepLeft => simp
  | stepRight => simp
  | @stepInterior q a b h ih =>
    intro he
    exact ih (extensionIndexInv_injective q (Sum.inr.inj he))

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeChainEndpoints


section NodeChainOrder

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution

lemma ChainAdjacent.consecutive {q : ℕ} {a b : ComponentIndex q}
    (h : ChainAdjacent q a b) :
    (extensionIndexInv q a).val + 1 = (extensionIndexInv q b).val := by
  induction h
  all_goals
    simp only [extensionIndexInv, Fin.val_succ, Fin.val_castSucc, Fin.val_zero,
      Fin.val_last] at *
  all_goals omega

lemma chainAdjacent_of_consecutive : ∀ q (a b : ComponentIndex q),
    (extensionIndexInv q a).val + 1 = (extensionIndexInv q b).val → ChainAdjacent q a b
  | 0, .inl a, .inl b, h => by
    fin_cases a <;> fin_cases b
    · simp [extensionIndexInv] at h
    · exact ChainAdjacent.base
    · simp [extensionIndexInv] at h
    · simp [extensionIndexInv] at h
  | 0, .inl _, .inr b, _ => Fin.elim0 b
  | 0, .inr a, _, _ => Fin.elim0 a
  | 1, .inl a, .inl b, h => by
    fin_cases a <;> fin_cases b <;> simp [extensionIndexInv] at h
  | 1, .inl a, .inr b, h => by
    fin_cases a <;> fin_cases b
    · exact ChainAdjacent.twoLeft
    · simp [extensionIndexInv] at h
  | 1, .inr a, .inl b, h => by
    fin_cases a; fin_cases b
    · simp [extensionIndexInv] at h
    · exact ChainAdjacent.twoRight
  | 1, .inr a, .inr b, h => by
    fin_cases a; fin_cases b; simp [extensionIndexInv] at h
  | q + 2, .inl a, .inl b, h => by
    fin_cases a <;> fin_cases b <;> simp only [extensionIndexInv, Fin.val_succ,
      Fin.val_last, Fin.val_zero] at h <;> omega
  | q + 2, .inl a, .inr b, h => by
    fin_cases a
    · have hb : b = 0 := by
        apply Fin.ext
        change b.val = 0
        simp only [extensionIndexInv, Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at h
        omega
      subst b
      exact ChainAdjacent.stepLeft q
    · simp only [extensionIndexInv, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at h
      omega
  | q + 2, .inr a, .inl b, h => by
    fin_cases b
    · simp only [extensionIndexInv, Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at h
      omega
    · have ha : a = (Fin.last q).succ := by
        apply Fin.ext
        simp only [extensionIndexInv, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at h ⊢
        omega
      subst a
      exact ChainAdjacent.stepRight q
  | q + 2, .inr a, .inr b, h => by
    have hh : a.val + 1 = b.val := by
      simp only [extensionIndexInv, Fin.val_succ, Fin.val_castSucc] at h
      omega
    have hi := chainAdjacent_of_consecutive q (extensionIndex q a) (extensionIndex q b) (by
      rw [extensionIndex_leftInverse q a, extensionIndex_leftInverse q b]
      exact hh)
    simpa only [extensionIndex_leftInverse q a, extensionIndex_leftInverse q b] using
      ChainAdjacent.stepInterior hi

/-- The proved recursive adjacency is exactly consecutive position in a line,
with the two actual affine ends at positions 0 and q + 1. -/
theorem chainAdjacent_iff_consecutive {q : ℕ} {a b : ComponentIndex q} :
    ChainAdjacent q a b ↔ (extensionIndexInv q a).val + 1 = (extensionIndexInv q b).val :=
  ⟨ChainAdjacent.consecutive, chainAdjacent_of_consecutive q a b⟩

lemma chainAdjacent_at_position (q : ℕ) (i : Fin (q + 1)) :
    ChainAdjacent q (extensionIndex q i.castSucc) (extensionIndex q i.succ) := by
  apply chainAdjacent_of_consecutive
  rw [extensionIndex_leftInverse q i.castSucc, extensionIndex_leftInverse q i.succ]
  rfl

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeChainOrder


section NodeAdjacentIntersections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

/-- Every adjacent pair of actual components meets scheme-theoretically in
Spec(k), with the literal finish/start endpoint sections as the two projections. -/
theorem chainAdjacent_isPullback {q : ℕ} {a b : ComponentIndex q} (h : ChainAdjacent q a b) :
    IsPullback (componentFinish (R := R) q a) (componentStart (R := R) q b)
      (componentMap π hπ hex hp ha q a) (componentMap π hπ hex hp ha q b) := by
  induction h with
  | base => exact base_ends_isPullback π hπ
  | twoLeft => exact twoLeftEnd_intersection_isPullback hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)
  | twoRight => exact (twoRightEnd_intersection_isPullback hπ (OneStepBlowup.ofFamilies π 0 hex hp
    ha)).flip
  | stepLeft q => exact resolveLeftEnd_newP1_isPullback π hπ hex hp ha q
  | stepRight q =>
    simpa only [componentMap, componentStart, componentFinish, interiorComponent, interiorFinish,
      Fin.cases_succ, Fin.lastCases_last] using
      (resolveRightEnd_newP1_isPullback π hπ hex hp ha q).flip
  | @stepInterior q a b h ih =>
    have H := extended_components_isPullback π hπ hex hp ha q a b h.ne
      (componentFinish (R := R) q a) (componentStart (R := R) q b) ih
    rw [interiorFinish_extension q a h.first_ne_right,
      interiorStart_extension q b h.second_ne_left] at H
    change IsPullback (interiorFinish (R := R) (q + 2) (extensionIndexInv q a))
      (interiorStart (R := R) (q + 2) (extensionIndexInv q b))
      (interiorComponent π hπ hex hp ha (q + 2) (extensionIndexInv q a))
      (interiorComponent π hπ hex hp ha (q + 2) (extensionIndexInv q b))
    rw [interiorComponent_eq_extended, interiorComponent_eq_extended,
      extensionIndex_rightInverse q a, extensionIndex_rightInverse q b]
    exact H

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeAdjacentIntersections


section NodeNonadjacentIntersections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

lemma leftEnd_interior_disjoint_of_ne (q : ℕ) (i : Fin (q + 2)) (hi : i ≠ 0) :
    Disjoint (Set.range (resolveLeftEnd π hπ hex hp ha (q + 2)))
      (Set.range (interiorComponent π hπ hex hp ha (q + 2) i)) := by
  revert hi
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
  · exact fun h => False.elim (h rfl)
  · intro _
    simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_last] using
      leftEnd_rightNewP1_disjoint π hπ hex hp ha q
  · intro _
    simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_castSucc, recursiveMiddleChart,
      resolveLeftEnd, resolveRightEnd, resolve] using
      (leftEnd_middle_disjoint hπ (OneStepBlowup.ofFamilies π (q + 1) hex hp ha)
        (resolve π hπ hex hp ha (q + 1))).mono_right
          (morphism_range_comp_subset (interiorComponent π hπ hex hp ha q j) _)

lemma rightEnd_interior_disjoint_of_ne (q : ℕ) (i : Fin (q + 2)) (hi : i ≠ (Fin.last q).succ) :
    Disjoint (Set.range (resolveRightEnd π hπ hex hp ha (q + 2)))
      (Set.range (interiorComponent π hπ hex hp ha (q + 2) i)) := by
  revert hi
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
  · intro _
    exact rightEnd_leftNewP1_disjoint π hπ hex hp ha q
  · exact fun h => False.elim (h rfl)
  · intro _
    simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_castSucc, recursiveMiddleChart,
      resolveLeftEnd, resolveRightEnd, resolve] using
      (rightEnd_middle_disjoint hπ (OneStepBlowup.ofFamilies π (q + 1) hex hp ha)
        (resolve π hπ hex hp ha (q + 1))).mono_right
          (morphism_range_comp_subset (interiorComponent π hπ hex hp ha q j) _)

/-- The complete nonadjacent-image exclusion for the actual component family. -/
theorem nonadjacent_components_disjoint : ∀ q (a b : ComponentIndex q), a ≠ b →
    ¬ ChainAdjacent q a b → ¬ ChainAdjacent q b a →
    Disjoint (Set.range (componentMap π hπ hex hp ha q a))
      (Set.range (componentMap π hπ hex hp ha q b))
  | 0, .inl a, .inl b, h, hf, hr => by
    fin_cases a <;> fin_cases b
    · exact False.elim (h rfl)
    · exact False.elim (hf ChainAdjacent.base)
    · exact False.elim (hr ChainAdjacent.base)
    · exact False.elim (h rfl)
  | 0, .inl _, .inr b, _, _, _ => Fin.elim0 b
  | 0, .inr a, _, _, _, _ => Fin.elim0 a
  | 1, .inl a, .inl b, h, _, _ => by
    fin_cases a <;> fin_cases b
    · exact False.elim (h rfl)
    · exact two_ends_disjoint hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)
    · exact (two_ends_disjoint hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)).symm
    · exact False.elim (h rfl)
  | 1, .inl a, .inr b, _, hf, hr => by
    fin_cases a <;> fin_cases b
    · exact False.elim (hf ChainAdjacent.twoLeft)
    · exact False.elim (hr ChainAdjacent.twoRight)
  | 1, .inr a, .inl b, _, hf, hr => by
    fin_cases a; fin_cases b
    · exact False.elim (hr ChainAdjacent.twoLeft)
    · exact False.elim (hf ChainAdjacent.twoRight)
  | 1, .inr a, .inr b, h, _, _ => False.elim (h (congrArg Sum.inr (Subsingleton.elim a b)))
  | q + 2, .inl a, .inl b, h, _, _ => by
    fin_cases a <;> fin_cases b
    · exact False.elim (h rfl)
    · exact recursive_ends_disjoint π hπ hex hp ha q
    · exact (recursive_ends_disjoint π hπ hex hp ha q).symm
    · exact False.elim (h rfl)
  | q + 2, .inl a, .inr b, _, hf, hr => by
    fin_cases a
    · apply leftEnd_interior_disjoint_of_ne
      intro hb
      subst b
      exact hf (ChainAdjacent.stepLeft q)
    · apply rightEnd_interior_disjoint_of_ne
      intro hb
      subst b
      exact hr (ChainAdjacent.stepRight q)
  | q + 2, .inr a, .inl b, _, hf, hr => by
    fin_cases b
    · apply Disjoint.symm
      apply leftEnd_interior_disjoint_of_ne
      intro ha
      subst a
      exact hr (ChainAdjacent.stepLeft q)
    · apply Disjoint.symm
      apply rightEnd_interior_disjoint_of_ne
      intro ha
      subst a
      exact hf (ChainAdjacent.stepRight q)
  | q + 2, .inr a, .inr b, h, hf, hr => by
    change Disjoint (Set.range (interiorComponent π hπ hex hp ha (q + 2) a))
      (Set.range (interiorComponent π hπ hex hp ha (q + 2) b))
    rw [interiorComponent_eq_extended, interiorComponent_eq_extended]
    have hn : extensionIndex q a ≠ extensionIndex q b := by
      intro hh
      exact h (congrArg Sum.inr (extensionIndex_injective q hh))
    apply extended_components_disjoint π hπ hex hp ha q _ _ hn
    apply nonadjacent_components_disjoint q _ _ hn
    · intro hh
      apply hf
      simpa only [extensionIndex_leftInverse q a, extensionIndex_leftInverse q b] using
        ChainAdjacent.stepInterior hh
    · intro hh
      apply hr
      simpa only [extensionIndex_leftInverse q a, extensionIndex_leftInverse q b] using
        ChainAdjacent.stepInterior hh

/-- Nonadjacent intersections are the actual empty scheme pullbacks. -/
lemma nonadjacent_intersection_empty (q : ℕ) (a b : ComponentIndex q) (hab : a ≠ b)
    (hf : ¬ ChainAdjacent q a b) (hr : ¬ ChainAdjacent q b a) :
    IsEmpty (pullback (componentMap π hπ hex hp ha q a) (componentMap π hπ hex hp ha q b) :
      Scheme) :=
  Scheme.isEmpty_pullback_iff.mpr (nonadjacent_components_disjoint π hπ hex hp ha q a b hab hf hr)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeNonadjacentIntersections


section NodeEndpointSections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

lemma interior_endpoints_pair : ∀ q (i : Fin q),
    (interiorStart (R := R) q i = Reciprocal.zeroSection k ∧
      interiorFinish (R := R) q i = Reciprocal.infinitySection k) ∨
    (interiorStart (R := R) q i = Reciprocal.infinitySection k ∧
      interiorFinish (R := R) q i = Reciprocal.zeroSection k)
  | 0, i => Fin.elim0 i
  | 1, _ => Or.inl ⟨rfl,rfl⟩
  | q + 2, i => by
    refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
    · exact Or.inr ⟨rfl,rfl⟩
    · simp only [interiorStart, interiorFinish, Fin.cases_succ, Fin.lastCases_last]
      exact Or.inl ⟨by trivial, by trivial⟩
    · simpa only [interiorStart, interiorFinish, Fin.cases_succ, Fin.lastCases_castSucc] using
        interior_endpoints_pair q j

lemma interior_endpoints_disjoint (q : ℕ) (i : Fin q) :
    Disjoint (Set.range (interiorStart (R := R) q i))
      (Set.range (interiorFinish (R := R) q i)) := by
  rcases interior_endpoints_pair (R := R) q i with ⟨hs,hf⟩ | ⟨hs,hf⟩
  · rw [hs,hf]
    exact Reciprocal.endpoints_disjoint k
  · rw [hs,hf]
    exact (Reciprocal.endpoints_disjoint k).symm

lemma interiorStart_over (q : ℕ) (i : Fin q) :
    interiorStart (R := R) q i ≫ structureMap k = 𝟙 _ := by
  rcases interior_endpoints_pair (R := R) q i with ⟨hs,_⟩ | ⟨hs,_⟩
  · rw [hs, Reciprocal.zeroSection_over]
  · rw [hs, Reciprocal.infinitySection_over]
lemma interiorFinish_over (q : ℕ) (i : Fin q) :
    interiorFinish (R := R) q i ≫ structureMap k = 𝟙 _ := by
  rcases interior_endpoints_pair (R := R) q i with ⟨_,hf⟩ | ⟨_,hf⟩
  · rw [hf, Reciprocal.infinitySection_over]
  · rw [hf, Reciprocal.zeroSection_over]

instance interiorStart_closed (q : ℕ) (i : Fin q) :
    IsClosedImmersion (interiorStart (R := R) q i) := by
  rcases interior_endpoints_pair (R := R) q i with ⟨hs,_⟩ | ⟨hs,_⟩ <;> rw [hs] <;> infer_instance
instance interiorFinish_closed (q : ℕ) (i : Fin q) :
    IsClosedImmersion (interiorFinish (R := R) q i) := by
  rcases interior_endpoints_pair (R := R) q i with ⟨_,hf⟩ | ⟨_,hf⟩ <;> rw [hf] <;> infer_instance

/-- The residue-field structure morphism of each affine end or interior projective component. -/
def componentStructure (q : ℕ) : ∀ a : ComponentIndex q,
    componentScheme (R := R) q a ⟶ Spec (.of k)
  | .inl _ => Reciprocal.affineBase k
  | .inr _ => structureMap k

@[reassoc] lemma componentStart_over (q : ℕ) (a : ComponentIndex q) :
    componentStart (R := R) q a ≫ componentStructure (R := R) q a = 𝟙 _ := by
  cases a with
  | inl a => exact Reciprocal.affineOrigin_over k
  | inr a => exact interiorStart_over q a
@[reassoc] lemma componentFinish_over (q : ℕ) (a : ComponentIndex q) :
    componentFinish (R := R) q a ≫ componentStructure (R := R) q a = 𝟙 _ := by
  cases a with
  | inl a => exact Reciprocal.affineOrigin_over k
  | inr a => exact interiorFinish_over q a

/-- Consecutive ordered components have the exact residue-point intersection. -/
lemma consecutive_components_isPullback (q : ℕ) (i : Fin (q + 1)) :
    IsPullback (componentFinish (R := R) q (extensionIndex q i.castSucc))
      (componentStart (R := R) q (extensionIndex q i.succ))
      (componentMap π hπ hex hp ha q (extensionIndex q i.castSucc))
      (componentMap π hπ hex hp ha q (extensionIndex q i.succ)) :=
  chainAdjacent_isPullback π hπ hex hp ha (chainAdjacent_at_position q i)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeEndpointSections


section NodeFirstOuterPullbacks

/-! Full local P1 pullbacks of the literal first left/right fibre charts,
with exact comparison to their maps into the first blowup. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution


variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {π : R} {m : ℕ} (D : OneStepBlowup.Data π m) (hπ : Irreducible π)
  (E : Data π m)
local notation "r" => residueBase (R := R)
local notation "Nbase" => Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))

/-- False is LEFT and true is RIGHT, agreeing with the retained global charts. -/
def firstOuterFibreChart (side : Bool) : outerFibre (π := π) ⟶ sourceSpecialFibre (step D hπ E) :=
  if side then rightFibreChart D hπ E else leftFibreChart D hπ E

instance firstOuterFibreChart_open (side : Bool) : IsOpenImmersion (firstOuterFibreChart D hπ E
  side) := by
  cases side <;> simp only [firstOuterFibreChart, Bool.false_eq_true, ↓reduceIte] <;> infer_instance

@[reassoc] lemma firstOuterFibreChart_base (side : Bool) :
    firstOuterFibreChart D hπ E side ≫ pullback.snd ((step D hπ E).map ≫ base) r =
      pullback.snd Nbase r := by
  cases side <;> simp only [firstOuterFibreChart, Bool.false_eq_true, ↓reduceIte,
    leftFibreChart_base_triangle, rightFibreChart_base_triangle]

lemma firstOuterFibreChart_firstBlowup_square (side : Bool) :
    IsPullback (pullback.fst Nbase r) (firstOuterFibreChart D hπ E side)
      (firstOuterChartMap D hπ side)
      (pullback.fst ((step D hπ E).map ≫ base) r ≫ stepToBlowup D hπ E) := by
  cases side
  · simpa only [firstOuterFibreChart, firstOuterChartMap, Bool.false_eq_true,
      ↓reduceIte, Category.comp_id, leftFibreChart, rightFibreChart, sourceSpecialFibre] using
      ((fibreChart_square (stepLeftChart D hπ E) Nbase
        ((step D hπ E).map ≫ base) r (stepLeftChart_base_triangle D hπ E)).flip.paste_vert
          (stepLeftChart_isPullback D hπ E).flip).flip
  · simpa only [firstOuterFibreChart, firstOuterChartMap, ↓reduceIte, Category.comp_id,
    leftFibreChart, rightFibreChart, sourceSpecialFibre] using
      ((fibreChart_square (stepRightChart D hπ E) Nbase
        ((step D hπ E).map ≫ base) r (stepRightChart_base_triangle D hπ E)).flip.paste_vert
          (stepRightChart_isPullback D hπ E).flip).flip

end AlgebraicGeometry.Scheme.PowerNode.Resolution
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (m : ℕ) (side : Bool) (j : Fin (m + 1))
local notation "r" => residueBase (R := R)
local notation "Nbase" => Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))
local notation "D₀" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "E₀" => resolve π hπ hex hp hatlas m
local notation "N" => interiorComponent π hπ hex hp hatlas (m + 1) j
local notation "O" => firstOuterFibreChart D₀ hπ E₀ side

/-- The pullback of an interior projective component to the chosen first outer fibre chart. -/
abbrev firstOuterP1 : Scheme.{u} := pullback N O
/-- The projection from the outer-chart pullback to the interior projective component. -/
abbrev firstOuterP1ToP1 : firstOuterP1 π hπ hex hp hatlas m side j ⟶
    AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 (ResidueField R) :=
  pullback.fst N O
/-- The projection from the outer-chart pullback to the outer node fibre. -/
abbrev firstOuterP1ToNode : firstOuterP1 π hπ hex hp hatlas m side j ⟶ outerFibre (π := π) :=
  pullback.snd N O

lemma firstOuterP1_firstBlowup_square :
    IsPullback (firstOuterP1ToNode π hπ hex hp hatlas m side j ≫ pullback.fst Nbase r)
      (firstOuterP1ToP1 π hπ hex hp hatlas m side j)
      (firstOuterChartMap D₀ hπ side)
      (N ≫ pullback.fst ((resolve π hπ hex hp hatlas (m + 2)).map ≫ base) r ≫
        stepToBlowup D₀ hπ E₀) := by
  exact (IsPullback.of_hasPullback N O).flip.paste_horiz
    (firstOuterFibreChart_firstBlowup_square D₀ hπ E₀ side)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeFirstOuterPullbacks

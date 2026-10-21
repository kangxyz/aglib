/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ExceptionalFibres

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ComponentInventory`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`06a89f0375b32eee50e6ac483b6401b6046528adfc91a3e12f96daa7394ed40e`.
Actual node/pointed scheme maps, full covers, original structural triangles and source quantifiers
  are retained. Universal blowup inputs remain conditional.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

/-!
# Actual irreducible components and exceptional component inventory

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section NodeActualComponents

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

/-- Indices for the two affine end components and the `q` interior projective components. -/
abbrev ComponentIndex (q : ℕ) := Fin 2 ⊕ Fin q

/-- The affine line for an end index and the projective line for an interior index. -/
def componentScheme (q : ℕ) : ComponentIndex q → Scheme.{u}
  | .inl _ => Cross.line k
  | .inr _ => projectiveP1 k

/-- The chosen affine end or interior projective component mapped into the resolved special
fibre. -/
def componentMap (q : ℕ) : ∀ a : ComponentIndex q,
    componentScheme (R := R) q a ⟶ sourceSpecialFibre (resolve π hπ hex hp ha (q + 1))
  | .inl 0 => resolveLeftEnd π hπ hex hp ha q
  | .inl 1 => resolveRightEnd π hπ hex hp ha q
  | .inr i => interiorComponent π hπ hex hp ha q i

instance componentScheme_integral (q : ℕ) (a : ComponentIndex q) :
    IsIntegral (componentScheme (R := R) q a) := by
  cases a <;> dsimp [componentScheme] <;> infer_instance

instance componentMap_closed (q : ℕ) (a : ComponentIndex q) :
    IsClosedImmersion (componentMap π hπ hex hp ha q a) := by
  rcases a with a | a
  · fin_cases a <;> dsimp [componentMap] <;> infer_instance
  · exact interiorComponent_closedImmersion π hπ hex hp ha q a

lemma componentMap_covered (q : ℕ) (z : sourceSpecialFibre (resolve π hπ hex hp ha (q + 1))) :
    ∃ a : ComponentIndex q, z ∈ Set.range (componentMap π hπ hex hp ha q a) := by
  rcases resolve_components_cover π hπ hex hp ha q z with h | h | ⟨i, h⟩
  · exact ⟨.inl 0, h⟩
  · exact ⟨.inl 1, h⟩
  · exact ⟨.inr i, h⟩

lemma componentMap_range_irreducible (q : ℕ) (a : ComponentIndex q) :
    IsIrreducible (Set.range (componentMap π hπ hex hp ha q a)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (componentScheme (R := R) q a)).image
      (componentMap π hπ hex hp ha q a) (componentMap π hπ hex hp ha q a).continuous.continuousOn

@[reassoc] lemma componentMap_base (q : ℕ) (a : ComponentIndex q) :
    componentMap π hπ hex hp ha q a ≫
      pullback.snd ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase =
        match a with
        | .inl _ => Reciprocal.affineBase k
        | .inr _ => structureMap k := by
  rcases a with a | a
  · fin_cases a
    · exact resolveLeftEnd_base π hπ hex hp ha q
    · exact resolveRightEnd_base π hπ hex hp ha q
  · exact interiorComponent_base π hπ hex hp ha q a

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeActualComponents


section NodeComponentTopology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial Topology
open PlaneNode _root_.PowerNode.Rees AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution


lemma affine_endpoint_not_surjective (k : Type u) [Field k] :
    ¬ Function.Surjective (Cross.endpoint k) := by
  intro h
  obtain ⟨p, hp⟩ := h (⟨⊥, inferInstance⟩ : Cross.line k)
  have hx : Polynomial.X ∈ (Cross.endpoint k p).asIdeal := by
    change (Polynomial.evalRingHom (0 : k)) Polynomial.X ∈ p.asIdeal
    simp
  rw [hp] at hx
  simp at hx

lemma zeroSection_not_surjective (k : Type u) [Field k] :
    ¬ Function.Surjective (Reciprocal.zeroSection k) := by
  intro h
  obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (.of k)))
  obtain ⟨q, hq⟩ := h (Reciprocal.infinitySection k p)
  exact Reciprocal.zeroSection_not_infinity k q
    (hq ▸ ⟨Reciprocal.affineOrigin k p, rfl⟩)

lemma infinitySection_not_surjective (k : Type u) [Field k] :
    ¬ Function.Surjective (Reciprocal.infinitySection k) := by
  intro h
  obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (.of k)))
  obtain ⟨q, hq⟩ := h (Reciprocal.zeroSection k p)
  exact Reciprocal.infinitySection_not_zero k q
    (hq ▸ ⟨Reciprocal.affineOrigin k p, rfl⟩)

lemma projective_map_range (k : Type u) [CommRing k] {Y : Scheme.{u}}
    (f : projectiveP1 k ⟶ Y) :
    Set.range f = Set.range (chart k 0 ≫ f) ∪ Set.range (chart k 1 ≫ f) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rcases Reciprocal.charts_cover k x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨a, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩) <;> exact ⟨_, rfl⟩


end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeComponentTopology


section NodeComponentExtensions

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

/-- Each old actual component extends to an actual projective component in the
next recursive source: old ends acquire their exceptional affine charts. -/
def extendedComponent (q : ℕ) : ComponentIndex q →
    (projectiveP1 k ⟶ sourceSpecialFibre (resolve π hπ hex hp ha (q + 3)))
  | .inl 0 => resolveLeftNewP1 π hπ hex hp ha q
  | .inl 1 => resolveRightNewP1 π hπ hex hp ha q
  | .inr i => interiorComponent π hπ hex hp ha q i ≫ recursiveMiddleChart π hπ hex hp ha q

/-- The zero affine chart for an end component, and the identity for an interior projective
component. -/
def extensionChart (q : ℕ) : ∀ a : ComponentIndex q,
    componentScheme (R := R) q a ⟶ projectiveP1 k
  | .inl _ => chart k 0
  | .inr _ => 𝟙 _

lemma extendedComponent_isPullback (q : ℕ) (a : ComponentIndex q) :
    IsPullback (componentMap π hπ hex hp ha q a) (extensionChart (R := R) q a)
      (recursiveMiddleChart π hπ hex hp ha q) (extendedComponent π hπ hex hp ha q a) := by
  rcases a with a | a
  · fin_cases a
    · exact stepLeftCompactification_zero_isPullback hπ q
        (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1))
        (resolveLeftEnd π hπ hex hp ha q) (resolveLeftEnd_target π hπ hex hp ha q)
        (resolveLeftEnd_base π hπ hex hp ha q)
    · exact stepRightCompactification_zero_isPullback hπ q
        (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1))
        (resolveRightEnd π hπ hex hp ha q) (resolveRightEnd_target π hπ hex hp ha q)
        (resolveRightEnd_base π hπ hex hp ha q)
  · dsimp only [extensionChart, componentMap, extendedComponent]
    apply IsPullback.of_vert_isIso_mono
    exact ⟨by simp⟩

lemma extendedComponent_preimage_middle (q : ℕ) (a : ComponentIndex q) :
    recursiveMiddleChart π hπ hex hp ha q ⁻¹' Set.range (extendedComponent π hπ hex hp ha q a) =
      Set.range (componentMap π hπ hex hp ha q a) :=
  (pullback_range_fst (extendedComponent_isPullback π hπ hex hp ha q a)).symm

lemma extendedComponent_not_subset_of_old (q : ℕ) (a b : ComponentIndex q)
    (h : ¬ Set.range (componentMap π hπ hex hp ha q a) ⊆
      Set.range (componentMap π hπ hex hp ha q b)) :
    ¬ Set.range (extendedComponent π hπ hex hp ha q a) ⊆
      Set.range (extendedComponent π hπ hex hp ha q b) := by
  intro hsub
  apply h
  rw [← extendedComponent_preimage_middle, ← extendedComponent_preimage_middle]
  exact Set.preimage_mono hsub

lemma extendedComponent_not_subset_leftEnd (q : ℕ) (a : ComponentIndex q) :
    ¬ Set.range (extendedComponent π hπ hex hp ha q a) ⊆
      Set.range (resolveLeftEnd π hπ hex hp ha (q + 2)) := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty (componentScheme (R := R) q a))
  have hx : recursiveMiddleChart π hπ hex hp ha q (componentMap π hπ hex hp ha q a x) ∈
      Set.range (extendedComponent π hπ hex hp ha q a) := by
    change componentMap π hπ hex hp ha q a x ∈
      recursiveMiddleChart π hπ hex hp ha q ⁻¹' Set.range (extendedComponent π hπ hex hp ha q a)
    rw [extendedComponent_preimage_middle]
    exact ⟨x, rfl⟩
  exact Set.disjoint_left.mp (leftEnd_middle_disjoint hπ
    (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1)))
      (h hx) ⟨_, rfl⟩

lemma extendedComponent_not_subset_rightEnd (q : ℕ) (a : ComponentIndex q) :
    ¬ Set.range (extendedComponent π hπ hex hp ha q a) ⊆
      Set.range (resolveRightEnd π hπ hex hp ha (q + 2)) := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty (componentScheme (R := R) q a))
  have hx : recursiveMiddleChart π hπ hex hp ha q (componentMap π hπ hex hp ha q a x) ∈
      Set.range (extendedComponent π hπ hex hp ha q a) := by
    change componentMap π hπ hex hp ha q a x ∈
      recursiveMiddleChart π hπ hex hp ha q ⁻¹' Set.range (extendedComponent π hπ hex hp ha q a)
    rw [extendedComponent_preimage_middle]
    exact ⟨x, rfl⟩
  exact Set.disjoint_left.mp (rightEnd_middle_disjoint hπ
    (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1)))
      (h hx) ⟨_, rfl⟩

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeComponentExtensions


section NodeComponentAvoidance

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


lemma recursive_ends_disjoint (q : ℕ) :
    Disjoint (Set.range (resolveLeftEnd π hπ hex hp ha (q + 2)))
      (Set.range (resolveRightEnd π hπ hex hp ha (q + 2))) := by
  exact (positive_outer_fibres_disjoint hπ q
    (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1))).mono
      (morphism_range_comp_subset _ _) (morphism_range_comp_subset _ _)

lemma leftEnd_rightNewP1_disjoint (q : ℕ) :
    Disjoint (Set.range (resolveLeftEnd π hπ hex hp ha (q + 2)))
      (Set.range (resolveRightNewP1 π hπ hex hp ha q)) := by
  rw [projective_map_range, resolveRightNewP1_old_chart, resolveRightNewP1_new_chart]
  apply Disjoint.union_right
  · exact (leftEnd_middle_disjoint hπ
      (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1))).mono_right
        (morphism_range_comp_subset _ _)
  · exact (positive_outer_fibres_disjoint hπ q
      (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1))).mono
        (morphism_range_comp_subset _ _) (morphism_range_comp_subset _ _)

lemma rightEnd_leftNewP1_disjoint (q : ℕ) :
    Disjoint (Set.range (resolveRightEnd π hπ hex hp ha (q + 2)))
      (Set.range (resolveLeftNewP1 π hπ hex hp ha q)) := by
  rw [projective_map_range, resolveLeftNewP1_old_chart, resolveLeftNewP1_new_chart]
  apply Disjoint.union_right
  · exact (rightEnd_middle_disjoint hπ
      (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1))).mono_right
        (morphism_range_comp_subset _ _)
  · exact (positive_outer_fibres_disjoint hπ q
      (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) (resolve π hπ hex hp ha (q + 1))).symm.mono
        (morphism_range_comp_subset _ _) (morphism_range_comp_subset _ _)

lemma leftEnd_not_subset_extended (q : ℕ) (a : ComponentIndex q) :
    ¬ Set.range (resolveLeftEnd π hπ hex hp ha (q + 2)) ⊆
      Set.range (extendedComponent π hπ hex hp ha q a) := by
  rcases a with a | a
  · fin_cases a
    · exact not_subset_range_of_pullback (resolveLeftEnd_newP1_isPullback π hπ hex hp ha q)
        (affine_endpoint_not_surjective k)
    · exact nonempty_not_subset_of_disjoint (leftEnd_rightNewP1_disjoint π hπ hex hp ha q)
        (range_nonempty _)
  · exact nonempty_not_subset_of_disjoint
      ((leftEnd_middle_disjoint hπ (OneStepBlowup.ofFamilies π (q + 1) hex hp ha)
        (resolve π hπ hex hp ha (q + 1))).mono_right (morphism_range_comp_subset _ _))
      (range_nonempty _)

lemma rightEnd_not_subset_extended (q : ℕ) (a : ComponentIndex q) :
    ¬ Set.range (resolveRightEnd π hπ hex hp ha (q + 2)) ⊆
      Set.range (extendedComponent π hπ hex hp ha q a) := by
  rcases a with a | a
  · fin_cases a
    · exact nonempty_not_subset_of_disjoint (rightEnd_leftNewP1_disjoint π hπ hex hp ha q)
        (range_nonempty _)
    · exact not_subset_range_of_pullback (resolveRightEnd_newP1_isPullback π hπ hex hp ha q)
        (affine_endpoint_not_surjective k)
  · exact nonempty_not_subset_of_disjoint
      ((rightEnd_middle_disjoint hπ (OneStepBlowup.ofFamilies π (q + 1) hex hp ha)
        (resolve π hπ hex hp ha (q + 1))).mono_right (morphism_range_comp_subset _ _))
      (range_nonempty _)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeComponentAvoidance


section NodeComponentInventory

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

/-- Orders the extended components with the left end first, interior components next, and the
right end last. -/
def extensionIndex (q : ℕ) : Fin (q + 2) → ComponentIndex q :=
  Fin.cases (.inl 0) (Fin.lastCases (.inl 1) Sum.inr)

/-- Places an end or interior component index in the corresponding ordered list of extended
components. -/
def extensionIndexInv (q : ℕ) : ComponentIndex q → Fin (q + 2)
  | .inl 0 => 0
  | .inl 1 => (Fin.last q).succ
  | .inr i => i.castSucc.succ

lemma extensionIndex_leftInverse (q : ℕ) :
    Function.LeftInverse (extensionIndexInv q) (extensionIndex q) := by
  intro i
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
  · rfl
  · simp only [extensionIndex, Fin.cases_succ, Fin.lastCases_last, extensionIndexInv]
  · simp only [extensionIndex, Fin.cases_succ, Fin.lastCases_castSucc, extensionIndexInv]

lemma extensionIndex_injective (q : ℕ) : Function.Injective (extensionIndex q) :=
  (extensionIndex_leftInverse q).injective

lemma interiorComponent_eq_extended (q : ℕ) (i : Fin (q + 2)) :
    interiorComponent π hπ hex hp ha (q + 2) i =
      extendedComponent π hπ hex hp ha q (extensionIndex q i) := by
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
  · rfl
  · simp only [interiorComponent, extensionIndex, Fin.cases_succ, Fin.lastCases_last,
    extendedComponent]
  · simp only [interiorComponent, extensionIndex, Fin.cases_succ, Fin.lastCases_castSucc,
    extendedComponent]


lemma baseLeftEnd_not_subset_right :
    ¬ Set.range (baseLeftEnd π hπ) ⊆ Set.range (baseRightEnd π hπ) := by
  rw [baseLeftEnd_eq, baseRightEnd_eq]
  exact not_subset_postcompose _ _ _ (baseCrossIso π hπ).hom.injective
    (Cross.left_not_subset_right k)

lemma baseRightEnd_not_subset_left :
    ¬ Set.range (baseRightEnd π hπ) ⊆ Set.range (baseLeftEnd π hπ) := by
  rw [baseLeftEnd_eq, baseRightEnd_eq]
  exact not_subset_postcompose _ _ _ (baseCrossIso π hπ).hom.injective
    (Cross.right_not_subset_left k)

/-- Pairwise noncontainment of the actual closed component images, derived from
the recursive pullback charts and the two separately constructed base cases. -/
lemma componentMap_pairwise_not_subset : ∀ q (a b : ComponentIndex q), a ≠ b →
    ¬ Set.range (componentMap π hπ hex hp ha q a) ⊆
      Set.range (componentMap π hπ hex hp ha q b)
  | 0, .inl a, .inl b, h => by
    fin_cases a <;> fin_cases b
    · exact False.elim (h rfl)
    · exact baseLeftEnd_not_subset_right π hπ
    · exact baseRightEnd_not_subset_left π hπ
    · exact False.elim (h rfl)
  | 0, .inl _, .inr b, _ => Fin.elim0 b
  | 0, .inr a, _, _ => Fin.elim0 a
  | 1, .inl a, .inl b, h => by
    fin_cases a <;> fin_cases b
    · exact False.elim (h rfl)
    · exact nonempty_not_subset_of_disjoint
        (two_ends_disjoint hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)) (range_nonempty _)
    · exact nonempty_not_subset_of_disjoint
        (two_ends_disjoint hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)).symm (range_nonempty _)
    · exact False.elim (h rfl)
  | 1, .inl a, .inr b, _ => by
    fin_cases a <;> fin_cases b
    · exact not_subset_range_of_pullback
        (twoLeftEnd_intersection_isPullback hπ (OneStepBlowup.ofFamilies π 0 hex hp ha))
        (affine_endpoint_not_surjective k)
    · exact not_subset_range_of_pullback
        (twoRightEnd_intersection_isPullback hπ (OneStepBlowup.ofFamilies π 0 hex hp ha))
        (affine_endpoint_not_surjective k)
  | 1, .inr a, .inl b, _ => by
    fin_cases a; fin_cases b
    · exact not_subset_range_of_pullback
        (twoLeftEnd_intersection_isPullback hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)).flip
        (zeroSection_not_surjective k)
    · exact not_subset_range_of_pullback
        (twoRightEnd_intersection_isPullback hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)).flip
        (infinitySection_not_surjective k)
  | 1, .inr a, .inr b, h => False.elim (h (congrArg Sum.inr (Subsingleton.elim a b)))
  | q + 2, .inl a, .inl b, h => by
    fin_cases a <;> fin_cases b
    · exact False.elim (h rfl)
    · exact nonempty_not_subset_of_disjoint (recursive_ends_disjoint π hπ hex hp ha q)
        (range_nonempty _)
    · exact nonempty_not_subset_of_disjoint (recursive_ends_disjoint π hπ hex hp ha q).symm
        (range_nonempty _)
    · exact False.elim (h rfl)
  | q + 2, .inl a, .inr b, _ => by
    fin_cases a
    · change ¬ Set.range (resolveLeftEnd π hπ hex hp ha (q + 2)) ⊆
        Set.range (interiorComponent π hπ hex hp ha (q + 2) b)
      rw [interiorComponent_eq_extended]
      exact leftEnd_not_subset_extended π hπ hex hp ha q _
    · change ¬ Set.range (resolveRightEnd π hπ hex hp ha (q + 2)) ⊆
        Set.range (interiorComponent π hπ hex hp ha (q + 2) b)
      rw [interiorComponent_eq_extended]
      exact rightEnd_not_subset_extended π hπ hex hp ha q _
  | q + 2, .inr a, .inl b, _ => by
    fin_cases b
    · change ¬ Set.range (interiorComponent π hπ hex hp ha (q + 2) a) ⊆
        Set.range (resolveLeftEnd π hπ hex hp ha (q + 2))
      rw [interiorComponent_eq_extended]
      exact extendedComponent_not_subset_leftEnd π hπ hex hp ha q _
    · change ¬ Set.range (interiorComponent π hπ hex hp ha (q + 2) a) ⊆
        Set.range (resolveRightEnd π hπ hex hp ha (q + 2))
      rw [interiorComponent_eq_extended]
      exact extendedComponent_not_subset_rightEnd π hπ hex hp ha q _
  | q + 2, .inr a, .inr b, h => by
    change ¬ Set.range (interiorComponent π hπ hex hp ha (q + 2) a) ⊆
      Set.range (interiorComponent π hπ hex hp ha (q + 2) b)
    rw [interiorComponent_eq_extended, interiorComponent_eq_extended]
    apply extendedComponent_not_subset_of_old
    exact componentMap_pairwise_not_subset q _ _ (by
      intro hh
      exact h (congrArg Sum.inr (extensionIndex_injective q hh)))

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeComponentInventory


section NodeIrreducibleComponentCorrespondence

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

lemma irreducible_subset_actual_component (q : ℕ)
    {s : Set (sourceSpecialFibre (resolve π hπ hex hp ha (q + 1)))} (hs : IsIrreducible s) :
    ∃ a : ComponentIndex q, s ⊆ Set.range (componentMap π hπ hex hp ha q a) := by
  classical
  let t := Finset.univ.image (fun a : ComponentIndex q => Set.range (componentMap π hπ hex hp ha q
    a))
  have ht : ∀ z ∈ t, IsClosed z := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    exact (componentMap π hπ hex hp ha q a).isClosedEmbedding.isClosed_range
  have hc : s ⊆ ⋃₀ (t : Set (Set (sourceSpecialFibre (resolve π hπ hex hp ha (q + 1))))) := by
    intro z _
    obtain ⟨a, ha⟩ := componentMap_covered π hπ hex hp ha q z
    exact ⟨_, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ha⟩
  obtain ⟨z, hz, hsz⟩ := isIrreducible_iff_sUnion_isClosed.mp hs t ht hc
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨a, hsz⟩

lemma actual_component_mem_irreducibleComponents (q : ℕ) (a : ComponentIndex q) :
    Set.range (componentMap π hπ hex hp ha q a) ∈
      irreducibleComponents (sourceSpecialFibre (resolve π hπ hex hp ha (q + 1))) := by
  refine ⟨componentMap_range_irreducible π hπ hex hp ha q a, ?_⟩
  intro s hs has
  obtain ⟨b, hb⟩ := irreducible_subset_actual_component π hπ hex hp ha q hs
  by_cases hab : a = b
  · subst b
    exact hb
  · exact False.elim (componentMap_pairwise_not_subset π hπ hex hp ha q a b hab (has.trans hb))

/-- Exhaustive correspondence with actual maximal irreducible closed subsets;
not merely the cardinality of a proposed component graph. -/
theorem resolve_irreducibleComponents_eq (q : ℕ) :
    irreducibleComponents (sourceSpecialFibre (resolve π hπ hex hp ha (q + 1))) =
      Set.range (fun a : ComponentIndex q => Set.range (componentMap π hπ hex hp ha q a)) := by
  ext s
  constructor
  · intro hs
    obtain ⟨a, hsub⟩ := irreducible_subset_actual_component π hπ hex hp ha q hs.1
    exact ⟨a, (Set.Subset.antisymm hsub (hs.2 (componentMap_range_irreducible π hπ hex hp ha q a)
      hsub)).symm⟩
  · rintro ⟨a, rfl⟩
    exact actual_component_mem_irreducibleComponents π hπ hex hp ha q a

/-- Each index names its actual closed integral A1 or P1 component scheme and
is in bijection with the irreducible components of the literal special fibre. -/
def actualComponentEquiv (q : ℕ) : ComponentIndex q ≃
    irreducibleComponents (sourceSpecialFibre (resolve π hπ hex hp ha (q + 1))) :=
  Equiv.ofBijective
    (fun a => ⟨Set.range (componentMap π hπ hex hp ha q a),
      actual_component_mem_irreducibleComponents π hπ hex hp ha q a⟩) (by
    constructor
    · intro a b h
      by_contra hab
      exact componentMap_pairwise_not_subset π hπ hex hp ha q a b hab
        ((congrArg Subtype.val h).le)
    · intro s
      have hs := (resolve_irreducibleComponents_eq π hπ hex hp ha q).le s.property
      obtain ⟨a, ha⟩ := hs
      exact ⟨a, Subtype.ext ha⟩)

lemma actualComponentEquiv_range (q : ℕ) (a : ComponentIndex q) :
    (actualComponentEquiv π hπ hex hp ha q a).val =
      Set.range (componentMap π hπ hex hp ha q a) := rfl

/-- The component count is a consequence of the actual component equivalence. -/
lemma resolve_irreducibleComponents_card (q : ℕ) :
    Nat.card (irreducibleComponents (sourceSpecialFibre (resolve π hπ hex hp ha (q + 1)))) = q + 2
      := by
  rw [← Nat.card_congr (actualComponentEquiv π hπ hex hp ha q), Nat.card_eq_fintype_card]
  simp [ComponentIndex, Nat.add_comm]

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeIrreducibleComponentCorrespondence


section NodeExceptionalComponentInventory

/-! Exhaustive P1 component inventory of the literal exceptional fibre. The
count follows from actual coverage, irreducibility, and pairwise noncontainment. -/
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

/-- The two A1 pieces contribute only attachment points, already on P1 images. -/
lemma exceptionalP1_cover (q : ℕ) (hq : 0 < q)
    (z : literalExceptionalFibre π hπ hex hp ha q) :
    ∃ i : Fin q, z ∈ Set.range (exceptionalP1 π hπ hex hp ha q i) := by
  rcases resolve_components_cover π hπ hex hp ha q
      (exceptionalToSpecial π hπ hex hp ha q z) with hl | hr | ⟨i,hi⟩
  · have hz : z ∈ Set.range (leftExceptionalPoint π hπ hex hp ha q) := by
      rw [pullback_range_snd (leftExceptionalPoint_isPullback π hπ hex hp ha q)]
      exact hl
    obtain ⟨p,hpoint⟩ := hz
    obtain ⟨i,s,hs⟩ := leftExceptionalPoint_on_P1 π hπ hex hp ha q hq
    refine ⟨i,s p,?_⟩
    change (s ≫ exceptionalP1 π hπ hex hp ha q i) p = z
    rw [hs]
    exact hpoint
  · have hz : z ∈ Set.range (rightExceptionalPoint π hπ hex hp ha q) := by
      rw [pullback_range_snd (rightExceptionalPoint_isPullback π hπ hex hp ha q)]
      exact hr
    obtain ⟨p,hpoint⟩ := hz
    obtain ⟨i,s,hs⟩ := rightExceptionalPoint_on_P1 π hπ hex hp ha q hq
    refine ⟨i,s p,?_⟩
    change (s ≫ exceptionalP1 π hπ hex hp ha q i) p = z
    rw [hs]
    exact hpoint
  · obtain ⟨p,hpoint⟩ := hi
    refine ⟨i,p,(exceptionalToSpecial π hπ hex hp ha q).injective ?_⟩
    change (exceptionalP1 π hπ hex hp ha q i ≫ exceptionalToSpecial π hπ hex hp ha q) p = _
    rw [exceptionalP1_special]
    exact hpoint

lemma exceptionalP1_pairwise_not_subset (q : ℕ) (i j : Fin q) (hij : i ≠ j) :
    ¬ Set.range (exceptionalP1 π hπ hex hp ha q i) ⊆
      Set.range (exceptionalP1 π hπ hex hp ha q j) := by
  intro H
  apply componentMap_pairwise_not_subset π hπ hex hp ha q (.inr i) (.inr j)
    (fun h => hij (Sum.inr.inj h))
  change Set.range (interiorComponent π hπ hex hp ha q i) ⊆ Set.range (interiorComponent π hπ hex
    hp ha q j)
  rintro _ ⟨p,rfl⟩
  obtain ⟨r,hr⟩ := H ⟨p,rfl⟩
  refine ⟨r,?_⟩
  have hh := congrArg (exceptionalToSpecial π hπ hex hp ha q) hr
  change (exceptionalP1 π hπ hex hp ha q j ≫ exceptionalToSpecial π hπ hex hp ha q) r =
    (exceptionalP1 π hπ hex hp ha q i ≫ exceptionalToSpecial π hπ hex hp ha q) p at hh
  simpa only [exceptionalP1_special, componentMap] using hh

lemma exceptionalP1_range_irreducible (q : ℕ) (i : Fin q) :
    IsIrreducible (Set.range (exceptionalP1 π hπ hex hp ha q i)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (projectiveP1 k)).image
      (exceptionalP1 π hπ hex hp ha q i) (exceptionalP1 π hπ hex hp ha q i).continuous.continuousOn

lemma irreducible_subset_exceptionalP1 (q : ℕ) (hq : 0 < q)
    {s : Set (literalExceptionalFibre π hπ hex hp ha q)} (hs : IsIrreducible s) :
    ∃ i : Fin q, s ⊆ Set.range (exceptionalP1 π hπ hex hp ha q i) := by
  classical
  let t := Finset.univ.image (fun i : Fin q => Set.range (exceptionalP1 π hπ hex hp ha q i))
  have ht : ∀ z ∈ t, IsClosed z := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact (exceptionalP1 π hπ hex hp ha q i).isClosedEmbedding.isClosed_range
  have hc : s ⊆ ⋃₀ (t : Set (Set (literalExceptionalFibre π hπ hex hp ha q))) := by
    intro z _
    obtain ⟨i,hi⟩ := exceptionalP1_cover π hπ hex hp ha q hq z
    exact ⟨_, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩
  obtain ⟨z,hz,hsz⟩ := isIrreducible_iff_sUnion_isClosed.mp hs t ht hc
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
  exact ⟨i,hsz⟩

lemma exceptionalP1_mem_irreducibleComponents (q : ℕ) (hq : 0 < q) (i : Fin q) :
    Set.range (exceptionalP1 π hπ hex hp ha q i) ∈
      irreducibleComponents (literalExceptionalFibre π hπ hex hp ha q) := by
  refine ⟨exceptionalP1_range_irreducible π hπ hex hp ha q i,?_⟩
  intro s hs his
  obtain ⟨j,hj⟩ := irreducible_subset_exceptionalP1 π hπ hex hp ha q hq hs
  by_cases hij : i = j
  · subst j
    exact hj
  · exact False.elim (exceptionalP1_pairwise_not_subset π hπ hex hp ha q i j hij (his.trans hj))

lemma exceptional_irreducibleComponents_eq (q : ℕ) (hq : 0 < q) :
    irreducibleComponents (literalExceptionalFibre π hπ hex hp ha q) =
      Set.range (fun i : Fin q => Set.range (exceptionalP1 π hπ hex hp ha q i)) := by
  ext s
  constructor
  · intro hs
    obtain ⟨i,hi⟩ := irreducible_subset_exceptionalP1 π hπ hex hp ha q hq hs.1
    exact ⟨i,(Set.Subset.antisymm hi (hs.2 (exceptionalP1_range_irreducible π hπ hex hp ha q i)
      hi)).symm⟩
  · rintro ⟨i,rfl⟩
    exact exceptionalP1_mem_irreducibleComponents π hπ hex hp ha q hq i

/-- Every maximal irreducible subset is represented by one actual closed P1. -/
def exceptionalComponentEquiv (q : ℕ) (hq : 0 < q) :
    Fin q ≃ irreducibleComponents (literalExceptionalFibre π hπ hex hp ha q) :=
  Equiv.ofBijective (fun i => ⟨Set.range (exceptionalP1 π hπ hex hp ha q i),
      exceptionalP1_mem_irreducibleComponents π hπ hex hp ha q hq i⟩) (by
    constructor
    · intro i j h
      by_contra hij
      exact exceptionalP1_pairwise_not_subset π hπ hex hp ha q i j hij (congrArg Subtype.val h).le
    · intro s
      obtain ⟨i,hi⟩ := (exceptional_irreducibleComponents_eq π hπ hex hp ha q hq).le s.property
      exact ⟨i,Subtype.ext hi⟩)

lemma exceptionalComponentEquiv_range (q : ℕ) (hq : 0 < q) (i : Fin q) :
    (exceptionalComponentEquiv π hπ hex hp ha q hq i).val =
      Set.range (exceptionalP1 π hπ hex hp ha q i) := rfl

/-- For exponent n = q + 1 > 1 the actual exceptional count is n-1. -/
lemma exceptional_irreducibleComponents_card (q : ℕ) (hq : 0 < q) :
    Nat.card (irreducibleComponents (literalExceptionalFibre π hπ hex hp ha q)) = q := by
  rw [← Nat.card_congr (exceptionalComponentEquiv π hπ hex hp ha q hq)]
  simp

/-- Exponent one has a residue-point origin fibre, not an exceptional P1. -/
def literalExceptionalOneIso : literalExceptionalFibre π hπ hex hp ha 0 ≅ Spec (.of k) :=
  by
    letI : IsIso (resolve π hπ hex hp ha 1).map := by
      change IsIso (𝟙 _)
      infer_instance
    exact asIso (pullback.snd (resolve π hπ hex hp ha 1).map (originalNode hπ 0))

@[reassoc (attr := simp)] lemma literalExceptionalOneIso_hom_base :
    (literalExceptionalOneIso π hπ hex hp ha).hom =
      pullback.snd (resolve π hπ hex hp ha 1).map (originalNode hπ 0) := rfl

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExceptionalComponentInventory

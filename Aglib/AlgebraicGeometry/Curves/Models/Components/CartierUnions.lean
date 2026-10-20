/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Restriction
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Interfaces
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor

/-!
# Finite unions of actual Cartier components

Source: frozen R5 `LocalModels/Incidence/CartierUnions.lean:93–191`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`. The original finite indexing,
actual kernel ideals, pairwise avoidance and three Cartier families are retained.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom.Cartier
open AlgebraicGeometry.Scheme.IdealSheafData
universe u v
namespace AlgebraicGeometry.Scheme.Hom
variable {X : Scheme.{u}} {ι : Type v} {C : ι → Scheme.{u}} (i : ∀ a, C a ⟶ X)
variable [∀ a, IsClosedImmersion (i a)]

theorem finiteIdealProduct_range (s : Finset ι) :
    Set.range (∏ a ∈ s, (i a).ker).subschemeι = ⋃ a ∈ s, Set.range (i a) := by
  classical
  rw [range_subschemeι]
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, support_mul]
    change ((i a).ker.support : Set X) ∪ ((∏ a ∈ s, (i a).ker).support : Set X) = _
    rw [ih, Scheme.Hom.support_ker, (i a).isClosedEmbedding.isClosed_range.closure_eq]
    simp

/-- A component avoiding each individual component avoids their finite union.
Only irreducibility and pairwise noncontainment are used; ambient maximality
is neither needed nor asserted. -/
theorem component_not_subset_finiteProduct [∀ a, IsIntegral (C a)]
    (s : Finset ι) (a : ι) (_ha : a ∉ s)
    (hpair : ∀ b, b ∈ s → ¬ Set.range (i a) ⊆ Set.range (i b)) :
    ¬ Set.range (i a) ⊆ Set.range (∏ b ∈ s, (i b).ker).subschemeι := by
  classical
  intro h
  rw [finiteIdealProduct_range] at h
  have hirr : IsIrreducible (Set.range (i a)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (C a)).image _ (i a).continuous.continuousOn
  have hc : ∀ z ∈ s.image (fun b => Set.range (i b)), IsClosed z := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    exact (i b).isClosedEmbedding.isClosed_range
  have hh : Set.range (i a) ⊆ ⋃₀ (s.image (fun b => Set.range (i b)) : Set (Set X)) := by
    simpa using h
  obtain ⟨z, hz, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr _ hc hh
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
  exact hpair b hb hsub

/-- Native finite Cartier-union induction. At every step, integral avoidance
constructs the Cartier intersection, the accepted binary sum theorem identifies
product and intersection, and the actual tensor comparison proves Cartierness. -/
theorem finiteIdealProduct_cartier_eq_inf
    (havoid : IntegralAvoidanceCartierPullback.{u})
    (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u})
    [∀ a, IsIntegral (C a)]
    (hI : ∀ a, IsLocallyRankOne X (idealModule (i a)))
    (hpair : ∀ a b, a ≠ b → ¬ Set.range (i a) ⊆ Set.range (i b))
    (s : Finset ι) (hs : s.Nonempty) :
    IsLocallyRankOne X (idealModule (∏ a ∈ s, (i a).ker).subschemeι) ∧
      (∏ a ∈ s, (i a).ker) = s.inf (fun a => (i a).ker) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    rw [Finset.prod_singleton, Finset.inf_singleton]
    exact ⟨isLocallyRankOne_of_iso X (idealImageIso (i a)).symm (hI a), rfl⟩
  | cons a s ha hs ih =>
    let j := (∏ b ∈ s, (i b).ker).subschemeι
    have hj : IsLocallyRankOne X (idealModule j) := ih.1
    have hn : ¬ Set.range (i a) ⊆ Set.range j :=
      component_not_subset_finiteProduct i s a ha (fun b hb =>
        hpair a b (by intro hab; subst b; exact ha hb))
    have hres := cartierRestriction_invertible havoid j (i a) hj hn
    have heq := hunion X _ _ j (i a) inferInstance inferInstance hj (hI a) hres
    have he := (htensor X _ _ j (i a) inferInstance inferInstance hj (hI a)).choose
    have hcart := isLocallyRankOne_of_iso X he
      (tensorSheaf_locallyRankOne X _ _ hj (hI a))
    dsimp only [j] at heq hcart
    rw [ker_subschemeι] at heq hcart
    rw [Finset.prod_cons, Finset.inf_cons]
    constructor
    · rw [mul_comm] at hcart
      exact hcart
    · rw [mul_comm, heq, ih.2, inf_comm]

/-- The literal finite intersection ideal defines an effective Cartier subscheme. -/
theorem finiteInfIdeal_cartier
    (havoid : IntegralAvoidanceCartierPullback.{u})
    (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u})
    [∀ a, IsIntegral (C a)]
    (hI : ∀ a, IsLocallyRankOne X (idealModule (i a)))
    (hpair : ∀ a b, a ≠ b → ¬ Set.range (i a) ⊆ Set.range (i b))
    (s : Finset ι) (hs : s.Nonempty) :
    IsLocallyRankOne X (idealModule (s.inf (fun a => (i a).ker)).subschemeι) := by
  obtain ⟨hc, he⟩ := finiteIdealProduct_cartier_eq_inf i havoid hunion htensor hI hpair s hs
  rwa [he] at hc

/-- Finite-type form for actual complementary unions indexed by a subtype. -/
theorem iInfIdeal_cartier
    (havoid : IntegralAvoidanceCartierPullback.{u})
    (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u})
    [∀ a, IsIntegral (C a)] [Finite ι] [Nonempty ι]
    (hI : ∀ a, IsLocallyRankOne X (idealModule (i a)))
    (hpair : ∀ a b, a ≠ b → ¬ Set.range (i a) ⊆ Set.range (i b)) :
    IsLocallyRankOne X (idealModule (⨅ a, (i a).ker).subschemeι) := by
  let := Fintype.ofFinite ι
  have hu : Finset.univ.inf (fun a => (i a).ker) = ⨅ a, (i a).ker := by
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true]
  rw [← hu]
  exact finiteInfIdeal_cartier i havoid hunion htensor hI hpair
    Finset.univ Finset.univ_nonempty

end AlgebraicGeometry.Scheme.Hom

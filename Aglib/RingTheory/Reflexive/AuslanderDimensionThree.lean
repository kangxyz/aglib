/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Ext.FiniteLength
public import Aglib.Algebra.Module.EndomorphismRank
public import Aglib.LinearAlgebra.TensorProduct.DualEvaluationFiniteLength
public import Aglib.RingTheory.LocalRing.ExtLengthCriterion
public import Aglib.RingTheory.Reflexive.AuslanderLengthBound

/-!
# The punctured-free Auslander criterion in dimension three

The actual endomorphism-module equivalence determines the rank of the finite-free
presentation. Canonical tensor-dual evaluation and punctured freeness give its
finite-length defects, hence the self-Ext upper bound. The finite-length Euler
obstruction then proves freeness. Punctured freeness is an explicit hypothesis;
this theorem does not assume or assert regularity of arbitrary localizations of
a regular local ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian

namespace ModuleCat

/-- The dimension-three Auslander criterion with explicit punctured freeness. -/
theorem free_of_endomorphism_equiv_of_free_punctured_of_dimension_three
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = 3) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (eEnd : Module.End R M ≃ₗ[R] (Fin r → M))
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) : Module.Free R M := by
  classical
  rcases subsingleton_or_nontrivial M with hzero | hnonzero
  · have : Subsingleton M := hzero
    infer_instance
  · have : Nontrivial M := hnonzero
    have : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    have := Module.finitePresentation_of_finite R M
    have hpd : projectiveDimension M ≤ 1 :=
      Module.projectiveDimension_le_of_isReflexive R 1 (by simp [hd]) M
    obtain ⟨P₁, P₀, _, _, _, _, _, _, _, _, f, g, hf, hg, hex⟩ :=
      exists_finite_free_shortExact_of_projectiveDimension_le_one R M hpd
    let S := ModuleCat.shortComplexOfCompEqZero f g hex.linearMap_comp_eq_zero
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hex hf hg
    let b₁ := Module.Free.chooseBasis R P₁
    let b₀ := Module.Free.chooseBasis R P₀
    have hr : Fintype.card (Module.Free.ChooseBasisIndex R P₀) =
        Fintype.card (Module.Free.ChooseBasisIndex R P₁) + r := by
      simpa only [Fintype.card_fin] using
        Module.basis_card_eq_add_card_of_end_equiv_pi eEnd b₁ b₀ f g hf hg hex
    have hC := isFiniteLength_ext_one_of_free_punctured R M hfree
    have hker := Module.isFiniteLength_ker_tensorDualEvaluation_of_free_punctured hfree
    have hcoker := Module.isFiniteLength_coker_tensorDualEvaluation_of_free_punctured hfree
    have hlen := length_ext_self_le_of_endomorphism_equiv R hd M r eEnd
      (Module.tensorDualEvaluation R M) hker hcoker
    exact free_of_ext_length_le R S hS b₁ b₀ hC r hr hlen

end ModuleCat

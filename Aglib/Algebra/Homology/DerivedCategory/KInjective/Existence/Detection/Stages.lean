/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Filtration.Quotients
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.Detection.Tests
public import Aglib.Algebra.Homology.HomComplex.ShortExact
public import Aglib.Algebra.Homology.HomComplex.WellFounded

/-! # Hom-complex acyclicity along the actual exhaustive source stages -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The original Hom-continuity comparison is the native full-prefix comparison. -/
lemma sourcePredecessorComparison_mono_of_monoOver
    {M : CochainComplex C ℤ} {J : Type w} [LinearOrder J]
    (F : J ⥤ MonoOver M) (j : J) :
    Mono (sourcePredecessorComparison (F ⋙ MonoOver.forget M ⋙ Over.forget M) j) := by
  change Mono (colimit.desc _ ((Set.principalSegIio j).cocone
    (F ⋙ MonoOver.forget M ⋙ Over.forget M)))
  exact mono_predecessor_comparison F j

end CochainComplex.HomComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic)
  (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- Every actual source stage has acyclic Hom complex once the proved test
quotients do. Successors use short exactness; limits use the entire prefix. -/
lemma acyclicStages_homComplex_acyclic
    (hI : ∀ i, (HomComplex (smallAcyclicTests hG i) I).Acyclic) (j : J) :
    (HomComplex (acyclicStages hG M hM j : CochainComplex C ℤ) I).Acyclic := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    rw [acyclicStages_bot]
    apply HomComplex.acyclic_of_nullhomotopic_target_shifts
    intro n f
    have hz : IsZero ((⊥ : Subobject M) : CochainComplex C ℤ) :=
      (isZero_zero _).of_iso Subobject.botCoeIsoZero
    exact ⟨Homotopy.ofEq (hz.eq_of_src f 0)⟩
  | succ j hj ih =>
    let f := acyclicStageSuccMap hG M hM j
    have : Mono f := inferInstanceAs (Mono (Subobject.ofLE _ _
      (acyclicStages_monotone hG M hM (Order.le_succ j))))
    rcases acyclicStageSuccMap_quotient hG M hM j hj with h | ⟨i, ⟨e⟩⟩
    · have : IsIso f := h
      exact HomComplex.acyclic_of_source_iso I (asIso f).symm ih
    · exact HomComplex.acyclic_middle_of_shortExact (ShortComplex.cokernelSequence f)
        { exact := ShortComplex.cokernelSequence_exact f
          mono_f := inferInstanceAs (Mono f)
          epi_g := inferInstanceAs (Epi (cokernel.π f)) } I
        (HomComplex.acyclic_of_source_iso I e (hI i)) ih
  | isSuccLimit j hj ih =>
    have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    let P := acyclicPredecessors hG M hM j
    let D := P ⋙ MonoOver.forget M ⋙ Over.forget M
    have (k : Set.Iio j) : Mono (HomComplex.sourcePredecessorComparison D k) :=
      HomComplex.sourcePredecessorComparison_mono_of_monoOver P k
    have hc : (HomComplex (colimit D) I).Acyclic :=
      HomComplex.acyclic_colimit_of_wellFounded D I wellFounded_lt
        (fun k => ih k.val k.property)
    exact HomComplex.acyclic_of_source_iso I (acyclicStagesLimitIso hG M hM j hj).symm hc

end CochainComplex

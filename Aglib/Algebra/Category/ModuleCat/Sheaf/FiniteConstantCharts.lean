/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantPresentation

/-!
# Finite-type constant charts on the original slice sites

A chart is an actual locally bijective map from a constant module presheaf
into the original slice restriction. The chart module is finitely generated;
its underlying set need not be finite. Actual restriction preserves these
charts, so the chart arrows form a sieve. At a terminal object one covering
sieve supplies the same local condition on every object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r m

namespace ModuleCat.Sheaf

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  {Λ : Type r} [Ring Λ] (F : Sheaf J (ModuleCat.{m} Λ))

/-- Arrows whose domains carry an original finite-type constant presentation of the sheaf. -/
def finiteTypeConstantChartSieve (U : C) : Sieve U where
  arrows V _ := ∃ M : ModuleCat.{m} Λ, Module.Finite Λ M ∧
    ∃ η : (Functor.const (Over V)ᵒᵖ).obj M ⟶
        ((J.overPullback (ModuleCat.{m} Λ) V).obj F).obj,
      CategoryTheory.Presheaf.IsLocallySurjective (J.over V) η ∧
        CategoryTheory.Presheaf.IsLocallyInjective (J.over V) η
  downward_closed := by
    rintro V W f ⟨M, hM, η, hsurj, hinj⟩ g
    let := hsurj
    let := hinj
    exact ⟨M, hM, overPresentationRestrict J F M g η, inferInstance, inferInstance⟩

/-- Pullback of the chart sieve keeps exactly the original domain-wise chart condition. -/
@[simp]
theorem finiteTypeConstantChartSieve_pullback {U V : C} (f : V ⟶ U) :
    (finiteTypeConstantChartSieve J F U).pullback f = finiteTypeConstantChartSieve J F V := rfl

/-- The original sheaf admits finite-type constant presentations on a cover of every object. -/
def HasFiniteTypeConstantCharts : Prop :=
  ∀ U : C, finiteTypeConstantChartSieve J F U ∈ J U

/-- An actual finite-type constant cover of a terminal object supplies all local charts. -/
theorem hasFiniteTypeConstantCharts_of_terminal {T : C} (hT : IsTerminal T)
    (h : finiteTypeConstantChartSieve J F T ∈ J T) : HasFiniteTypeConstantCharts J F := by
  intro U
  simpa only [finiteTypeConstantChartSieve_pullback] using J.pullback_stable (hT.from U) h

end ModuleCat.Sheaf

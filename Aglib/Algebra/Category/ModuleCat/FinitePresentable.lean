/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FilteredColimitFinitePresentation
public import Mathlib.CategoryTheory.Presentable.Finite

/-! # Finite presentation and categorical compactness of native modules

Finite generators and relations control the original maps into any filtered
colimit. Neither commutativity nor finiteness of the coefficient ring is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe r w k

variable {R : Type r} [Ring R]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Finite presentation of a module implies categorical finite presentability,
at any index size for which the original forgetful functor preserves filtered colimits. -/
theorem isFinitelyPresentable_of_finitePresentation (M : ModuleCat.{w} R)
    [Module.FinitePresentation R M]
    [PreservesFilteredColimitsOfSize.{k, k} (forget (ModuleCat.{w} R))] :
    IsFinitelyPresentable.{k} M := by
  classical
  apply IsCardinalPresentable.mk
  intro I _ _ D c hc
  have : IsFiltered I := isFiltered_of_isCardinalFiltered I Cardinal.aleph0.{k}
  constructor
  · exact exists_factor_of_finitePresentation D c hc M
  · intro i a b hab
    obtain ⟨pres, hG, hR⟩ :=
      (Module.finitePresentation_iff_exists_presentation.{0, 0}).mp
        (inferInstance : Module.FinitePresentation R M)
    let := hG
    let := hR
    have heq (g : pres.G) : ∃ (j : I) (f : i ⟶ j),
        D.map f (a (pres.var g)) = D.map f (b (pres.var g)) := by
      apply (hc.eq_iff' _ _).mp
      exact ConcreteCategory.congr_hom hab (pres.var g)
    choose j f hf using heq
    obtain ⟨l, p, q, hp⟩ := IsFiltered.wideSpan f
    refine ⟨l, p, ?_⟩
    apply hom_ext
    apply pres.toIsPresentation.postcomp_injective
    ext g
    change D.map p (a (pres.var g)) = D.map p (b (pres.var g))
    rw [← hp g, D.map_comp]
    exact congrArg (D.map (q g)) (hf g)

end ModuleCat

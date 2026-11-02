/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Exact coproducts of modules at independent scalar and value sizes

The actual module-to-abelian-group functor preserves colimits and preserves and
reflects finite limits at independent scalar and module universes. Transporting
the existing exact additive-group coproducts therefore proves native AB4 for
the original module category. The sized form uses only the existing restriction
of coproduct index size; no scalar ring, module carrier or colimit model changes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe r m w

namespace ModuleCat

variable (Λ : Type r) [Ring Λ]

/-- Native module coproducts are exact with independent scalar and module universes. -/
instance (priority := 100) ab4Independent : AB4 (ModuleCat.{m} Λ) where
  ofShape ι := by
    let F := forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m}
    let : PreservesFiniteLimits F := by
      exact PreservesLimitsOfSize0.preservesFiniteLimits F
    exact HasExactColimitsOfShape.domain_of_functor (Discrete ι) F

/-- Native exact module coproducts restrict to the required smaller index size. -/
instance (priority := 100) ab4OfSizeIndependent : AB4OfSize.{w} (ModuleCat.{max w m} Λ) :=
  AB4OfSize_shrink.{w, m} _

end ModuleCat

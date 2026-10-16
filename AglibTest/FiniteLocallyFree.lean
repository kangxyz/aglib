/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank

/-! Category objects reuse the canonical finite-local-freeness class and its
finite-presentation instance. Rank detection uses the proved pointwise
fibre-dimension theorem. -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules

universe u

example {X : Scheme.{u}} (M : Scheme.Modules.FiniteLocallyFree X) :
    Scheme.Modules.IsFiniteLocallyFree X M.obj := inferInstance

example {X : Scheme.{u}} (M : Scheme.Modules.FiniteLocallyFree X) :
    SheafOfModules.IsFinitePresentation.{u} M.obj := inferInstance

example (X : Scheme.{u}) :
    finiteLocallyFreeToFinitePresentation (X := X) ⋙ finitePresentationForget =
      finiteLocallyFreeForget :=
  finiteLocallyFreeToFinitePresentation_comp_forget

example {X : Scheme.{u}} (M : Scheme.Modules.FiniteLocallyFree X) (n : ℕ) :
    SheafHasRank M.obj n ↔ ∀ x, Scheme.Modules.FiniteLocallyFree.rank M x = n :=
  Scheme.Modules.FiniteLocallyFree.hasRank_iff_rank_eq M n

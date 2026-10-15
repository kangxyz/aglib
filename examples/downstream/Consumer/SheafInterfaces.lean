/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic

/-! Focused standalone clients of finite direct image and canonical finite local
freeness. The finite-type functor is used over arbitrary schemes. -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.QuasiCoherent

universe u

example {Z X : Scheme.{u}} (f : Z ⟶ X) [AlgebraicGeometry.IsFinite f] :
    finiteTypePushforward f ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Z ⋙ Scheme.Modules.pushforward f :=
  finiteTypePushforward_comp_inclusion f

example {X : Scheme.{u}} (M : Scheme.Modules.FiniteLocallyFree X) :
    Scheme.Modules.IsFiniteLocallyFree X M.obj := inferInstance

example {X : Scheme.{u}} (M : Scheme.Modules.FiniteLocallyFree X) :
    SheafOfModules.IsFinitePresentation.{u} M.obj := inferInstance

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.SliceExactness

/-! # Original module-valued slice exactness with an independent scalar universe -/

/-- info: 'ModuleCat.Sheaf.overPullback_preservesEpimorphisms' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPullback_preservesEpimorphisms

/-- info: 'ModuleCat.Sheaf.overPullback_preservesHomology' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPullback_preservesHomology

/-- info: 'ModuleCat.Sheaf.overPullback_preservesFiniteColimits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.overPullback_preservesFiniteColimits

open CategoryTheory

universe c h r

attribute [local instance] ModuleCat.Sheaf.hasSheafify

example {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (Λ : Type r) [Ring Λ] (U : C)
    (S : ShortComplex (Sheaf J (ModuleCat.{max c h} Λ))) (hS : S.ShortExact) :
    (S.map (J.overPullback (ModuleCat.{max c h} Λ) U)).ShortExact := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  exact hS.map _

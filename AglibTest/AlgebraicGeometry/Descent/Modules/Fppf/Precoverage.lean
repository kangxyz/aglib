/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.Precoverage
public import Aglib.AlgebraicGeometry.Descent.Modules.Pseudofunctor
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-! Focused consumer of the `HasIsos` instance of Mathlib's `Scheme.fppfPrecoverage`: with it,
Mathlib's `Pseudofunctor.IsStack.of_precoverage` and `Pseudofunctor.IsPrestack.of_precoverage`
apply to `Scheme.fppfTopology` and the quasi-coherent pseudofunctor
`Scheme.Modules.quasicoherentPseudofunctor`. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example : Scheme.fppfTopology.{u} = Scheme.fppfPrecoverage.toGrothendieck := rfl

example : Scheme.fppfPrecoverage.{u}.HasIsos := inferInstance

example (h : ∀ (S : Scheme.{u}) (R : Presieve S), R ∈ Scheme.fppfPrecoverage S →
      Scheme.Modules.quasicoherentPseudofunctor.{u}.IsStackFor R) :
    Scheme.Modules.quasicoherentPseudofunctor.{u}.IsStack Scheme.fppfTopology.{u} :=
  Pseudofunctor.IsStack.of_precoverage h

example (h : ∀ (S : Scheme.{u}) (R : Presieve S), R ∈ Scheme.fppfPrecoverage S →
      Scheme.Modules.quasicoherentPseudofunctor.{u}.IsPrestackFor R) :
    Scheme.Modules.quasicoherentPseudofunctor.{u}.IsPrestack Scheme.fppfTopology.{u} :=
  Pseudofunctor.IsPrestack.of_precoverage h

/--
info: 'AlgebraicGeometry.Scheme.instHasIsosFppfPrecoverage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.instHasIsosFppfPrecoverage

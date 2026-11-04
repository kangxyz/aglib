/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel.BaseChange

/-! Native verification of the original multiplication kernel inclusion under base change. -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.OverField
open AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.Group.MultiplicationKernel

universe u

attribute [local instance] Over.cartesianMonoidalCategory baseChange_isCommMonObj

example {F K : Type u} [Field F] [Field K] (b : Spec (.of K) ⟶ Spec (.of F))
    (E : Grp (FScheme F)) [IsCommMonObj E.X] (n : ℕ) :
    (baseChangeIso b E n).hom ≫
        Kernel.inclusion (multiplicationHom ((Over.pullback b).mapGrp.obj E) n) =
      (Over.pullback b).mapGrp.map (Kernel.inclusion (multiplicationHom E n)) :=
  baseChangeIso_hom_inclusion b E n

/--
info: 'AlgebraicGeometry.Scheme.Group.MultiplicationKernel.baseChangeIso_hom_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms baseChangeIso_hom_inclusion

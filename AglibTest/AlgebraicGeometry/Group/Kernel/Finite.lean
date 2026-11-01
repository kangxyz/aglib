/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Finite

/-! # Finiteness from the actual finite group kernel over an arbitrary base -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group

universe u

example {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)
    [IsProper G.X.hom] [LocallyOfFiniteType H.X.hom] [IsSeparated H.X.hom]
    [IsFinite (Kernel.group f).X.hom] : IsFinite f.hom.hom.left :=
  Kernel.isFinite_of_isFinite_group f

example {S : Scheme.{u}} {M G H : Grp (Over S)} {f : G ⟶ H}
    [IsProper G.X.hom] [LocallyOfFiniteType H.X.hom] [IsSeparated H.X.hom]
    (m : KernelMarking M G H f) [IsFinite M.X.hom] : IsFinite f.hom.hom.left :=
  Kernel.isFinite_of_isFinite_kernelMarking m

/--
info: 'AlgebraicGeometry.Scheme.Group.Kernel.isFinite_of_isFinite_kernelMarking' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Kernel.isFinite_of_isFinite_kernelMarking

/--
info: 'AlgebraicGeometry.Scheme.Group.Kernel.isFinite_of_isFinite_group' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Kernel.isFinite_of_isFinite_group

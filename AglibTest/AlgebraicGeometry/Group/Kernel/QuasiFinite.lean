/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.QuasiFinite

/-!
# Consumer checks for finite actual kernels and local quasi-finiteness

The generic result works over arbitrary bases, without source properness, source
quasi-compactness, target separatedness or rational lifting assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Group

universe u

namespace AglibTest.GroupKernelQuasiFinite

example {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [IsFinite (Kernel.group f).X.hom] : LocallyQuasiFinite f.hom.hom.left :=
  Kernel.locallyQuasiFinite_of_isFinite_group f

example {k : Type u} [Field k] {G H : Grp (Over (Spec (.of k)))} (f : G ⟶ H)
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [IsFinite (Kernel.group f).X.hom] : LocallyQuasiFinite f.hom.hom.left :=
  Kernel.locallyQuasiFinite_of_isFinite_group f

/--
info: 'AlgebraicGeometry.Scheme.Group.Kernel.finite_preimage_singleton_of_isFinite_kernelMarking' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Kernel.finite_preimage_singleton_of_isFinite_kernelMarking

/--
info: 'AlgebraicGeometry.Scheme.Group.Kernel.locallyQuasiFinite_of_isFinite_kernelMarking' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Kernel.locallyQuasiFinite_of_isFinite_kernelMarking

/--
info: 'AlgebraicGeometry.Scheme.Group.Kernel.locallyQuasiFinite_of_isFinite_group' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Kernel.locallyQuasiFinite_of_isFinite_group

end AglibTest.GroupKernelQuasiFinite

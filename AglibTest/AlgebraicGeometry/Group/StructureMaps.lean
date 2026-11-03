/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.StructureMaps

/-! Multiplication is flat over an arbitrary flat base group. Over a
field the required base flatness is supplied by the original native instance. -/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {S : Scheme.{u}} (G : Over S) [GrpObj G] [Flat G.hom] : Flat (μ[G]).left :=
  Scheme.Group.flat_mul G

example {k : Type u} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] :
    Flat (μ[G]).left := Scheme.Group.flat_mul G

example {k : Type u} [Field k] (G : Over (Spec (CommRingCat.of k))) :
    Flat (fst G G).left ∧ Flat (snd G G).left :=
  ⟨Scheme.Group.flat_fst G, Scheme.Group.flat_snd G⟩

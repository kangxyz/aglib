/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Flatness over an etale algebra

An actual map from an etale algebra to a flat algebra makes the target flat
over the source. The target need not be etale, local, or Noetherian.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.Etale

universe u v w

variable {R : Type u} {A : Type v} {C : Type w}
  [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
  [Etale R A] [Module.Flat R C]

/-- A map from an etale `R`-algebra to a flat `R`-algebra makes the target
flat over its source, for the algebra structure induced by this actual map. -/
lemma flat_of_algHom (f : A →ₐ[R] C) :
    letI : Algebra A C := f.toRingHom.toAlgebra
    Module.Flat A C := by
  let : Algebra A C := f.toRingHom.toAlgebra
  let B := A ⊗[R] C
  have : Module.Flat A B := Module.Flat.baseChange R A C
  let : Algebra C B := TensorProduct.rightAlgebra
  have : Etale C B := Etale.of_equiv (TensorProduct.commRight R C A)
  let q : B →ₐ[R] C :=
    TensorProduct.lift f (AlgHom.id R C) (fun _ _ => Commute.all _ _)
  let : Algebra B C := q.toRingHom.toAlgebra
  have : IsScalarTower C B C := IsScalarTower.of_algebraMap_eq fun c => by
    change c = q ((1 : A) ⊗ₜ[R] c)
    change c = f 1 * c
    simp
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => by
    change f a = q (a ⊗ₜ[R] (1 : C))
    change f a = f a * 1
    simp
  have : Etale B C := Etale.of_restrictScalars C B C
  have : Module.Flat B C := Algebra.Smooth.flat B C
  exact Module.Flat.trans A B C

end Algebra.Etale

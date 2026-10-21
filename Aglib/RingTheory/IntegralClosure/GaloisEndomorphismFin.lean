/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphism
public import Mathlib.LinearAlgebra.Pi

/-! Restricting the actual coefficient equivalence to the original base ring. -/

@[expose] public section

noncomputable section

namespace IsIntegralClosure

variable (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]
  [Fintype (L ≃ₐ[K] L)]

/-- Surjectivity of the actual Galois coefficient map supplies the base-linear
endomorphism decomposition, with only finite reindexing and scalar restriction. -/
def galoisEndomorphismFinEquiv (h : Function.Surjective (galoisEndomorphism A K L B)) :
    Module.End A B ≃ₗ[A] (Fin (Fintype.card (L ≃ₐ[K] L)) → B) :=
  ((LinearEquiv.ofBijective (galoisEndomorphism A K L B)
      ⟨galoisEndomorphism_injective A K L B, h⟩).symm.restrictScalars A).trans
    (LinearEquiv.piCongrLeft A (fun _ => B) (Fintype.equivFin (L ≃ₐ[K] L)))

end IsIntegralClosure

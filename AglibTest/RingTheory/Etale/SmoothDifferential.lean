/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.SmoothDifferential

/-! # The differential criterion retains no flatness premise for the middle map -/

@[expose] public noncomputable section

example (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Nontrivial B] [Algebra.FormallySmooth R B] [Algebra.FormallyUnramified A B]
    [Module.Free A Ω[A⁄R]] [Module.Finite A Ω[A⁄R]]
    [Module.Free B Ω[B⁄R]] [Module.Finite B Ω[B⁄R]]
    (h : Module.finrank A Ω[A⁄R] = Module.finrank B Ω[B⁄R]) :
    Algebra.FormallyEtale A B :=
  Algebra.formallyEtale_of_formallyUnramified_of_finrank_eq R A B h

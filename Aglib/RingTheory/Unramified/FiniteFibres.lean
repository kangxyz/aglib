/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Spectrum.Prime.Bijectivity
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Unramified.Basic

/-! # Finite algebras with formally unramified residue-field fibres

The finite module of differentials vanishes if its original residue-field
scalar extensions vanish. No flatness or Noetherian hypothesis is needed.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Algebra

/-- A finite algebra whose residue-field scalar extensions are formally
unramified is formally unramified. -/
theorem formallyUnramified_of_finite_of_residueField_tensorProduct
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B]
    (h : ∀ p : PrimeSpectrum R,
      FormallyUnramified p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] B)) :
    FormallyUnramified R B := by
  have : Module.Finite R Ω[B⁄R] := Module.Finite.trans B Ω[B⁄R]
  constructor
  apply Module.subsingleton_of_subsingleton_residueField_tensorProduct (R := R)
  intro p
  let := h p
  let : Algebra B (p.asIdeal.ResidueField ⊗[R] B) := TensorProduct.rightAlgebra
  exact (KaehlerDifferential.tensorKaehlerEquivBase R p.asIdeal.ResidueField B
    (p.asIdeal.ResidueField ⊗[R] B)).injective.subsingleton

end Algebra

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Spectrum.Prime.FiberInjectivity
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Constant fibre rank over a reduced local ring

A finite module over a reduced local ring is free when all of its original
prime residue-field fibres have the dimension of its closed fibre. A basis
of the closed fibre lifts to a finite free surjection by Nakayama. Equality
of fibre dimensions and reducedness make this actual surjection injective.
Finite presentation, flatness and Noetherianity are not assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct Module

namespace Module

variable (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The native prime-residue fibre at the closed point has the same dimension as
the usual quotient-residue fibre of a local ring. -/
theorem finrank_closedPoint_fiber :
    finrank (IsLocalRing.closedPoint R).asIdeal.ResidueField
        ((IsLocalRing.closedPoint R).asIdeal.Fiber M) =
      finrank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] M) := by
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let b := Module.finBasis (R ⧸ IsLocalRing.maximalIdeal R)
    ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] M)
  calc
    finrank (IsLocalRing.maximalIdeal R).ResidueField
        ((IsLocalRing.maximalIdeal R).ResidueField ⊗[R] M) =
      finrank (IsLocalRing.maximalIdeal R).ResidueField
        ((IsLocalRing.maximalIdeal R).ResidueField ⊗[R ⧸ IsLocalRing.maximalIdeal R]
          ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] M)) :=
      (AlgebraTensorModule.cancelBaseChange R (R ⧸ IsLocalRing.maximalIdeal R)
        (IsLocalRing.maximalIdeal R).ResidueField
        (IsLocalRing.maximalIdeal R).ResidueField M).finrank_eq.symm
    _ = Fintype.card (Fin (finrank (R ⧸ IsLocalRing.maximalIdeal R)
        ((R ⧸ IsLocalRing.maximalIdeal R) ⊗[R] M))) :=
      Module.finrank_eq_card_basis (b.baseChange (IsLocalRing.maximalIdeal R).ResidueField)
    _ = finrank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] M) :=
      Fintype.card_fin _

/-- A finite module over a reduced local ring is free when every original fibre has
the dimension of its closed fibre. This does not assume flatness or finite presentation. -/
theorem free_of_finrank_fiber_eq_of_isReduced [IsReduced R]
    (hdim : ∀ p : PrimeSpectrum R,
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) =
        finrank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] M)) :
    Module.Free R M := by
  classical
  let k := IsLocalRing.ResidueField R
  let V := k ⊗[R] M
  let b := Module.finBasis k V
  have hlift (j : Fin (finrank k V)) : ∃ m : M, (1 : k) ⊗ₜ[R] m = b j :=
    TensorProduct.mk_surjective R M k IsLocalRing.residue_surjective (b j)
  choose m hm using hlift
  let π : (Fin (finrank k V) →₀ R) →ₗ[R] M := Finsupp.linearCombination R m
  have hsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis m b hm
  have hfiber (p : PrimeSpectrum R) :
      finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] (Fin (finrank k V) →₀ R)) =
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
    rw [Module.finrank_eq_card_basis
      ((Finsupp.basisSingleOne : Basis (Fin (finrank k V)) R _).baseChange
        p.asIdeal.ResidueField), Fintype.card_fin]
    exact (hdim p).symm
  have hbij := π.bijective_of_surjective_of_finrank_fiber_eq hsurj hfiber
  exact Module.Free.of_basis
    (Finsupp.basisSingleOne.map (LinearEquiv.ofBijective π hbij))

/-- Local constancy of the original fibre dimension makes a finite module free over
a reduced local ring. Every prime specializes to the closed point, so local constancy
already supplies equality of all the original fibre dimensions. -/
theorem free_of_isLocallyConstant_finrank_fiber_of_isReduced [IsReduced R]
    (h : IsLocallyConstant (fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M))) : Module.Free R M := by
  apply free_of_finrank_fiber_eq_of_isReduced R M
  intro p
  have he : finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) =
      finrank (IsLocalRing.closedPoint R).asIdeal.ResidueField
        ((IsLocalRing.closedPoint R).asIdeal.Fiber M) :=
    (IsLocalRing.specializes_closedPoint p).mem_open (h.isOpen_fiber _) rfl
  exact he.trans (finrank_closedPoint_fiber R M)

end Module

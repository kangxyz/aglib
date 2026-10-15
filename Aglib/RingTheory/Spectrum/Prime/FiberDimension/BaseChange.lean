/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Original finite-module fibre dimension under arbitrary scalar extension

After any ring base change, the original fibre at a prime is the scalar
extension of the original fibre at its contracted prime. The native
residue-field embedding and actual tensor associativity identify their
dimensions. Ring and module universes are independent; no flatness,
Noetherianity or finite presentation is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct Module

namespace Module

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Original fibre dimension of a finite module is unchanged by scalar extension
to a prime lying over the contracted prime. The new ring need not be flat. -/
theorem finrank_fiber_baseChange (q : PrimeSpectrum S) :
    finrank q.asIdeal.ResidueField (q.asIdeal.Fiber (S ⊗[R] M)) =
      finrank (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
        ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber M) := by
  let φ : (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField →+*
      q.asIdeal.ResidueField :=
    Ideal.ResidueField.map _ _ (algebraMap R S) rfl
  let : Algebra (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
      q.asIdeal.ResidueField := φ.toAlgebra
  let : IsScalarTower R (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
      q.asIdeal.ResidueField := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField r).trans
      (Ideal.ResidueField.map_algebraMap
        (PrimeSpectrum.comap (algebraMap R S) q).asIdeal q.asIdeal (algebraMap R S) rfl r).symm)
  let b := Module.finBasis (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
    ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber M)
  calc
    finrank q.asIdeal.ResidueField (q.asIdeal.Fiber (S ⊗[R] M)) =
        finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) :=
      (AlgebraTensorModule.cancelBaseChange R S q.asIdeal.ResidueField
        q.asIdeal.ResidueField M).finrank_eq
    _ = finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[(PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField]
          ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber M)) :=
      (AlgebraTensorModule.cancelBaseChange R
        (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField q.asIdeal.ResidueField
        q.asIdeal.ResidueField M).finrank_eq.symm
    _ = Fintype.card (Fin (finrank
        (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
        ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber M))) :=
      Module.finrank_eq_card_basis (b.baseChange q.asIdeal.ResidueField)
    _ = finrank (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
        ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber M) := Fintype.card_fin _

end Module

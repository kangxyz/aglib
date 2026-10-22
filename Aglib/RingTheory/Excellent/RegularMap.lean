/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Regular algebra maps via finite residue-field tests

The field tests are finite-dimensional extensions represented in the source
universe. In particular, this does not require arbitrary infinite field base
changes to be Noetherian. Native `IsRegularRing` includes Noetherianity.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- A flat algebra map with geometrically regular Noetherian fibres, expressed
by the finite-extension criterion on each residue field. -/
def IsRegularMap (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Module.Flat R S ∧
  ∀ (p : Ideal R) [p.IsPrime]
    (E : Type u) [Field E] [Algebra R E] [Algebra p.ResidueField E]
    [IsScalarTower R p.ResidueField E] [FiniteDimensional p.ResidueField E],
    IsRegularRing (S ⊗[R] E)

/-- The zero-prime test, with any chosen fraction field of the domain. The
original `R`-algebra structure on the extension field is retained. -/
theorem IsRegularMap.regular_finiteGenericFibre
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] (h : IsRegularMap R S)
    (K : Type w) [Field K] [Algebra R K] [IsFractionRing R K]
    (E : Type u) [Field E] [Algebra R E] [Algebra K E]
    [IsScalarTower R K E] [FiniteDimensional K E] :
    IsRegularRing (S ⊗[R] E) := by
  let k := (⊥ : Ideal R).ResidueField
  let e : k ≃ₐ[R] K := IsLocalization.algEquiv (nonZeroDivisors R) k K
  let : Algebra k E := ((algebraMap K E).comp e.toRingHom).toAlgebra
  let : IsScalarTower R k E := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R E r = algebraMap K E (e (algebraMap R k r))
    rw [e.commutes, IsScalarTower.algebraMap_apply R K E]
  let : FiniteDimensional k E := Module.Finite.of_equiv_equiv
    e.toRingEquiv.symm (RingEquiv.refl E) (by
      ext x
      change algebraMap K E (e (e.symm x)) = algebraMap K E x
      rw [e.apply_symm_apply])
  exact h.2 (⊥ : Ideal R) E

end Algebra

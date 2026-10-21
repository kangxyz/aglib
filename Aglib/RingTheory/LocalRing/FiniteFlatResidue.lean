/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.LinearAlgebra.Trace

/-!
# Finite flat unramified local algebras with unchanged residue field

The rank calculation needs only finite flatness and formal unramifiedness,
not a global etale assertion on a prime localization.
-/

@[expose] public noncomputable section

open IsLocalRing Module

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Finite R S] [Module.Flat R S] [Algebra.FormallyUnramified R S]

/-- Finite flat formally unramified local algebras have rank equal to the
rank of the actual residue field extension. -/
lemma finrank_eq_finrank_residueField_of_finite_flat_unramified :
    Module.finrank R S = Module.finrank (ResidueField R) (ResidueField S) := by
  let : Module.Free R S := Module.free_of_flat_of_isLocalRing
  have e := AddEquiv.toLinearEquiv (R := R ⧸ maximalIdeal R) (Ideal.quotEquivOfEq <|
      Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)).toAddEquiv
    ?_
  · rw [← finrank_quotient_map (R := R) (S := S)]
    exact e.finrank_eq
  · intro r x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingEquiv.toAddEquiv_eq_coe]
    rfl

/-- A finite flat formally unramified local algebra with unchanged actual
residue field is the original base algebra. -/
theorem bijective_algebraMap_of_finite_flat_unramified_residue
    (hκ : Function.Bijective (algebraMap (ResidueField R) (ResidueField S))) :
    Function.Bijective (algebraMap R S) := by
  let : Module.Free R S := Module.free_of_flat_of_isLocalRing
  let E : ResidueField R ≃ₐ[ResidueField R] ResidueField S :=
    AlgEquiv.ofBijective (Algebra.ofId (ResidueField R) (ResidueField S)) hκ
  apply Module.Free.bijective_algebraMap_of_finrank_eq_one
  rw [finrank_eq_finrank_residueField_of_finite_flat_unramified (R := R) (S := S),
    ← E.toLinearEquiv.finrank_eq]
  exact Module.finrank_self _

end IsLocalRing

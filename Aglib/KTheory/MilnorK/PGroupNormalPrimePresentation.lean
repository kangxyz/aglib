/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.PGroupNormalSubfieldEmbedding
public import Aglib.KTheory.MilnorK.Residue.Polynomial.Support
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# A normal prime polynomial presentation inside the original field

A primitive generator presents the actual normal prime subfield of a field
embedded in a finite Galois p-group extension. The resulting map lands in
the original field, not merely its isomorphic range in the ambient field.
No norm or presentation-independence assertion is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue

variable {k H Ω : Type*} [Field k] [Field H] [Field Ω]
  [Algebra k H] [Algebra k Ω] [FiniteDimensional k H]
  [FiniteDimensional k Ω] [IsGalois k Ω] [CharZero k]

/-- An actual normal prime subfield admits a monic irreducible presentation
whose literal root field embeds into the original input field. -/
theorem exists_normal_prime_presentation_of_isPGroup_embedding
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (Ω ≃ₐ[k] Ω))
    (g : H →ₐ[k] Ω) (hH : 1 < Module.finrank k H) :
    ∃ r : MonicIrreducible k, Normal k (AdjoinRoot r.val) ∧ r.val.natDegree = p ∧
      Nonempty (AdjoinRoot r.val →ₐ[k] H) := by
  obtain ⟨L, hnormal, hdegree, _⟩ :=
    IntermediateField.exists_normal_prime_subfield_of_embedding p hG g hH
  let : Normal k L := hnormal
  let pb : PowerBasis k L := Field.powerBasisOfFiniteOfSeparable k L
  let r : MonicIrreducible k :=
    ⟨minpoly k pb.gen, minpoly.monic pb.isIntegral_gen, minpoly.irreducible pb.isIntegral_gen⟩
  let : Fact (Irreducible r.val) := ⟨r.property.2⟩
  let ε : AdjoinRoot r.val ≃ₐ[k] L := AdjoinRoot.equiv' r.val pb
    (by
      change aeval (AdjoinRoot.root r.val) r.val = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    (minpoly.aeval k pb.gen)
  refine ⟨r, Normal.of_algEquiv ε.symm, ?_, ⟨L.val.comp ε.toAlgHom⟩⟩
  change (minpoly k pb.gen).natDegree = p
  rw [pb.natDegree_minpoly, ← pb.finrank, hdegree]

end MilnorK.PolynomialNorm

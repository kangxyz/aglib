/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SylowFixedField
public import Mathlib.FieldTheory.Perfect

/-!
# Finite prime-to-prime simultaneous splitting

Over a perfect field, a finite family of nonzero polynomials of degree below
`p` splits over a finite extension of degree prime to `p`. The extension is an
actual intermediate field of the splitting field of the finite product.
Perfectness supplies separability of that splitting field; repeated polynomial
factors need not themselves be separable. No infinite closure is constructed.
-/

@[expose] public noncomputable section

namespace IntermediateField

open Polynomial

variable {k : Type*} [Field k] [PerfectField k]

/-- A specified finite family of small nonzero polynomials has an actual finite
prime-to-`p` splitting subfield of the splitting field of its product. -/
theorem exists_coprime_splitting_field_of_finset (p : ℕ) [Fact p.Prime]
    (s : Finset k[X]) (hne : ∀ q ∈ s, q ≠ 0) (hsmall : ∀ q ∈ s, q.natDegree < p) :
    ∃ S : IntermediateField k (∏ q ∈ s, q).SplittingField,
      FiniteDimensional k S ∧ p.Coprime (Module.finrank k S) ∧
      ∀ q ∈ s, (q.map (algebraMap k S)).Splits := by
  classical
  let f : k[X] := ∏ q ∈ s, q
  have hf : f ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  let : IsGalois k f.SplittingField := ⟨⟩
  apply exists_coprime_splitting_intermediateField p s hsmall
  intro q hq
  exact (SplittingField.splits f).of_dvd (Polynomial.map_ne_zero hf)
    (Polynomial.map_dvd (algebraMap k f.SplittingField) (Finset.dvd_prod_of_mem id hq))

end IntermediateField

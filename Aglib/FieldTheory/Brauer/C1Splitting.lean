/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.C1GaloisSplitting
public import Aglib.FieldTheory.Brauer.DivisionRepresentative
public import Aglib.FieldTheory.Brauer.FiniteGaloisSplitting

/-!
# Splitting over infinite C₁ fields

Finite Galois splitting is constructed independently of C₁ and reduced norms.
The descended determinant polynomial then has degree `n` in `n²` coordinates;
C₁ forces the division representative to have dimension one. Native Wedderburn
and Brauer equivalence give actual matrix splitting and the singleton native
Brauer quotient. The coefficient field is explicitly assumed infinite.
-/

@[expose] public noncomputable section

universe u v

namespace Algebra

/-- Every finite-dimensional central division algebra over an infinite C₁
field has dimension one. -/
theorem finrank_eq_one_of_isC1 (K D : Type*) [Field K] [Infinite K]
    [DivisionRing D] [Algebra K D] [FiniteDimensional K D] [IsCentral K D]
    (hK : Field.IsC1 K) : Module.finrank K D = 1 := by
  obtain ⟨L, hL, hKL, hfin, hgal, n, hn, ⟨e⟩⟩ :=
    exists_finiteGalois_matrix_splitting K D
  let : Infinite L := Infinite.of_injective (algebraMap K L) (algebraMap K L).injective
  exact finrank_eq_one_of_isC1_of_galois_splitting hK n e

/-- The scalar-field equivalence for the original central division algebra. -/
theorem nonempty_algEquiv_of_isC1 (K D : Type*) [Field K] [Infinite K]
    [DivisionRing D] [Algebra K D] [FiniteDimensional K D] [IsCentral K D]
    (hK : Field.IsC1 K) : Nonempty (K ≃ₐ[K] D) :=
  Module.nonempty_algEquiv_iff_finrank_eq_one.mpr (finrank_eq_one_of_isC1 K D hK)

end Algebra

namespace CSA

variable {K : Type u} [Field K] [Infinite K]

/-- Actual matrix splitting over an infinite C₁ field, with no splitting-field
or reduced-norm hypothesis in the statement. -/
theorem exists_matrix_of_isC1 (hK : Field.IsC1 K) (A : CSA.{u, v} K) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨n, hn, D, hD, hKD, hfin, hcentral, ⟨e⟩⟩ := exists_central_division_matrix A
  obtain ⟨d⟩ := Algebra.nonempty_algEquiv_of_isC1 K D hK
  exact ⟨n, hn, ⟨e.trans d.symm.mapMatrix⟩⟩

/-- Every central simple algebra has the scalar class in the native Brauer relation. -/
theorem isBrauerEquivalent_scalar_of_isC1 (hK : Field.IsC1 K) (A : CSA.{u, u} K) :
    IsBrauerEquivalent A (scalar K) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_matrix_of_isC1 hK A
  exact isBrauerEquivalent_scalar_of_matrix A n e

end CSA

namespace BrauerGroup

/-- The native Brauer quotient of an infinite C₁ field is a singleton.
No group structure absent from the native carrier is introduced. -/
theorem subsingleton_of_isC1 (K : Type u) [Field K] [Infinite K]
    (hK : Field.IsC1 K) : Subsingleton (BrauerGroup.{u, u} K) := by
  refine ⟨?_⟩
  intro a b
  induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
      exact Quotient.sound ((CSA.isBrauerEquivalent_scalar_of_isC1 hK A).trans
        (CSA.isBrauerEquivalent_scalar_of_isC1 hK B).symm)

end BrauerGroup

/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Central.Matrix
public import Aglib.FieldTheory.Brauer.Split

/-!
# Actual central division representatives

Finite Wedderburn theory gives a division algebra, and centrality is transported
from the original algebra through its matrix presentation and descended to the
coefficient algebra. The result is a representative in the native Brauer
relation, with the original coefficient-field structure.
-/

@[expose] public noncomputable section

universe u v

namespace CSA

variable {K : Type u} [Field K]

/-- Every finite-dimensional central simple algebra has a genuinely central
finite-dimensional division-algebra matrix presentation. -/
theorem exists_central_division_matrix (A : CSA.{u, v} K) :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type v) (_ : DivisionRing D)
      (_ : Algebra K D) (_ : FiniteDimensional K D) (_ : Algebra.IsCentral K D),
      Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) D) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, D, hD, hKD, hfin, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  let : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv K A _ e
  exact ⟨n, hn, D, hD, hKD, hfin, Algebra.IsCentral.of_matrix K D (Fin n), ⟨e⟩⟩

/-- Every native Brauer equivalence class has a central simple representative
whose nonzero elements are units. This property uses the representative's
existing ring structure, not a second division-ring structure on its carrier. -/
theorem exists_brauerEquivalent_division (A : CSA.{u, v} K) :
    ∃ B : CSA.{u, v} K, IsBrauerEquivalent A B ∧ ∀ b : B, b ≠ 0 → IsUnit b := by
  obtain ⟨n, hn, D, hD, hKD, hfin, hcentral, ⟨e⟩⟩ := exists_central_division_matrix A
  let B : CSA.{u, v} K := { toAlgCat := AlgCat.of K D }
  refine ⟨B, ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩, ?_⟩
  · exact ⟨(finOneMatrixAlgEquiv A).trans e⟩
  · intro b hb
    exact isUnit_iff_ne_zero.mpr hb

end CSA

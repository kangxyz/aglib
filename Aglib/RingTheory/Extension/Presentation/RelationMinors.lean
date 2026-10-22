/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.Fitting

/-! # Minors of actual relations belong to intrinsic Fitting ideals

A selected finite family need only consist of genuine relations. It is not required to
generate the whole relation ideal: an internal presentation indexed by the actual kernel
allows the full Jacobian-to-Fitting identity to apply without that extra assumption.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra.Generators

variable {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B] [Finite ι]

set_option backward.isDefEq.respectTransparency false in
/-- Every correctly sized Jacobian minor of actual relations belongs to the intrinsic
Fitting ideal, even when these selected relations do not generate the whole kernel. -/
theorem det_relation_pderiv_mem_fittingIdeal (P : Generators R B ι) (k : ℕ)
    (f : Fin (Nat.card ι - k) → MvPolynomial ι R) (hf : ∀ j, f j ∈ P.ker)
    (cols : Fin (Nat.card ι - k) → ι) :
    (Matrix.of fun j i => aeval P.val (pderiv (cols i) (f j))).det ∈
      Module.fittingIdeal B (KaehlerDifferential R B) k := by
  let Q : Presentation R B ι P.ker :=
    { P with
      relation := Subtype.val
      span_range_relation_eq_ker := by
        rw [Subtype.range_coe]
        exact Ideal.span_eq _ }
  rw [Q.fittingIdeal_kaehler_eq_minorIdeal]
  apply Ideal.subset_span
  refine ⟨cols, (fun j => ⟨f j, hf j⟩), ?_⟩
  change (Matrix.of fun i j => aeval P.val (pderiv (cols i) (f j))).det = _
  exact Matrix.det_transpose _

end Algebra.Generators

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The original short exact sequence of successive cycle objects

Exactness in the next degree makes the native cycle inclusion and native
map to next cycles a short exact sequence. This construction is independent
of module finiteness, flatness or projectivity.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- The cycle sequence ending at the next cycle object is short exact when the
complex is exact in that next degree. -/
theorem shortExact_cycles (K : CochainComplex C ℤ) (n : ℤ) (h : K.ExactAt (n + 1)) :
    (ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
      rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, toCycles_i,
        iCycles_d, zero_comp])).ShortExact := by
  let T := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
  have hT : T.Exact := T.exact_of_f_is_kernel (K.cyclesIsKernel n (n + 1) (by simp))
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · let f : ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
        rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, toCycles_i,
          iCycles_d, zero_comp]) ⟶ T :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := K.iCycles (n + 1)
        comm₂₃ := by simp [T] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mpr hT
  · change Mono (K.iCycles n)
    infer_instance
  · have he : (K.sc' n (n + 1) (n + 2)).Exact :=
      (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; omega)).mp h
    apply (epi_comp_iff_of_isIso (K.toCycles n (n + 1))
      (K.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp; omega)).hom).mp
    rw [toCycles_cyclesIsoSc'_hom]
    exact he.epi_toCycles

end CochainComplex

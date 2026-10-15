/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Original integer-indexed differential kernel sequences

The actual differential between successive kernels gives a short exact
sequence whenever the next cochain degree is exact. The ambient category
is arbitrary abelian; no resolution choice is made.
-/


/-!
Source: `Quillen/Algebra/Homology/CochainKernelSequence.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 53]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ)
/-- An original differential between its source and target kernels. -/
def kernelSequence (n : ℤ) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (K.d n (n + 1)))
    (kernel.lift (K.d (n + 1) (n + 2)) (K.d n (n + 1)) (K.d_comp_d n (n + 1) (n + 2)))
    (by
      apply (cancel_mono (kernel.ι (K.d (n + 1) (n + 2)))).mp
      simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp])
/-- Exactness at the next degree makes the original kernel sequence short exact. -/
theorem kernelSequence_shortExact (n : ℤ) (hK : K.ExactAt (n + 1)) :
    (kernelSequence K n).ShortExact := by
  let φ : kernelSequence K n ⟶
      ShortComplex.mk (kernel.ι (K.d n (n + 1))) (K.d n (n + 1)) (kernel.condition _) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (K.d (n + 1) (n + 2))
      comm₂₃ := by simp [kernelSequence] }
  exact
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
        (ShortComplex.exact_kernel _)
      mono_f := by change Mono (kernel.ι _); infer_instance
      epi_g := ((HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2)
        (by simp) (by simp; omega)).mp hK).epi_kernelLift }
end CochainComplex
end

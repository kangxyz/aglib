/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
/-!
# Kernel short exact sequences of an injective resolution

For an actual injective resolution in an arbitrary abelian category, the
augmentation and successive differential kernels form short exact sequences.
The maps are the original augmentation, kernel inclusions, and differential
kernel lifts. These sequences support dimension shifting without replacing
the resolution or assuming exactness of a functor applied to it.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {M : C}
    (I : CategoryTheory.InjectiveResolution M)

/-- The augmentation followed by the first differential, with its target restricted
to the next kernel. -/
def initialSequence : ShortComplex C :=
  ShortComplex.mk (X₁ := M) (I.ι.f 0)
    (kernel.lift (I.cocomplex.d 1 2) (I.cocomplex.d 0 1) (I.cocomplex.d_comp_d 0 1 2)) (by
      apply (cancel_mono (kernel.ι (I.cocomplex.d 1 2))).mp
      simp only [Category.assoc, kernel.lift_ι, zero_comp]
      exact I.ι_f_zero_comp_complex_d)

/-- The initial kernel sequence of an injective resolution is short exact. -/
lemma initialSequence_shortExact : (initialSequence I).ShortExact := by
  let φ : initialSequence I ⟶ ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (I.cocomplex.d 1 2)
      comm₂₃ := by simp [initialSequence] }
  exact
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr I.exact₀
      mono_f := by change Mono (I.ι.f 0); infer_instance
      epi_g := (I.exact_succ 0).epi_kernelLift }

/-- A differential between its source and target kernels. -/
def kernelSequence (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (I.cocomplex.d n (n + 1)))
    (kernel.lift (I.cocomplex.d (n + 1) (n + 2)) (I.cocomplex.d n (n + 1))
      (I.cocomplex.d_comp_d n (n + 1) (n + 2))) (by
        apply (cancel_mono (kernel.ι (I.cocomplex.d (n + 1) (n + 2)))).mp
        simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp])

/-- Each successive differential kernel sequence is short exact. -/
lemma kernelSequence_shortExact (n : ℕ) : (kernelSequence I n).ShortExact := by
  let φ : kernelSequence I n ⟶
      ShortComplex.mk (kernel.ι (I.cocomplex.d n (n + 1)))
        (I.cocomplex.d n (n + 1)) (kernel.condition _) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (I.cocomplex.d (n + 1) (n + 2))
      comm₂₃ := by simp [kernelSequence] }
  exact
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
        (ShortComplex.exact_kernel _)
      mono_f := by change Mono (kernel.ι _); infer_instance
      epi_g := (I.exact_succ n).epi_kernelLift }

end CategoryTheory.InjectiveResolution

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flatness from universal tensor injections and flat quotient sequences

An actual linear map into a flat module descends flatness when tensoring it
with every test module is injective. A commuting tensor square gives the
native tensor-injectivity criterion for flatness. Combined with the native
tensor exactness theorem for a flat quotient, this proves that a surjection
between flat modules has flat kernel. No purity interface is assumed.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Module.Flat

variable {R : Type u} [CommRing R] {M : Type v} {P : Type w}
  [AddCommGroup M] [AddCommGroup P] [Module R M] [Module R P]

/-- Universal injectivity of the original tensor map into a flat module
implies flatness of its source. Test modules may stay in the scalar universe;
the source and target module universes are independent. -/
theorem of_universally_lTensor_injective [Flat R P] (f : M →ₗ[R] P)
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Injective (f.lTensor N)) : Flat R M := by
  have H : ∀ ⦃N N' : Type u⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (g : N →ₗ[R] N'), Function.Injective g → Function.Injective (g.rTensor M) := by
    intro N N' _ _ _ _ g hg x y hxy
    apply h N
    apply rTensor_preserves_injective_linearMap (M := P) g hg
    have hcomm : (f.lTensor N').comp (g.rTensor M) = (g.rTensor P).comp (f.lTensor N) := by
      simp only [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
    exact (LinearMap.congr_fun hcomm x).symm.trans
      ((congrArg (f.lTensor N') hxy).trans (LinearMap.congr_fun hcomm y))
  exact (iff_rTensor_preserves_injective_linearMap' (R := R) (M := M)).mpr H

/-- The actual kernel of a surjection between flat modules is flat. The
native flat-quotient tensor exactness theorem supplies universal injectivity
of its original inclusion; the source-flatness criterion above then applies. -/
theorem ker_of_surjective [Flat R M] [Flat R P] (f : M →ₗ[R] P)
    (hf : Function.Surjective f) : Flat R (LinearMap.ker f) := by
  apply of_universally_lTensor_injective (LinearMap.ker f).subtype
  intro N _ _
  exact LinearMap.lTensor_injective_of_exact_of_flat f hf (LinearMap.ker f).subtype
    (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map f) N

end Module.Flat

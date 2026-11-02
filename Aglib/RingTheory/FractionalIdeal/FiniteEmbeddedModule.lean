/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The native numerator ideal of a finite embedded module

An actual finite module embedded in the original fraction localization is
identified with the numerator ideal of its native fractional image. The
original denominator and the value of the given embedding are retained.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

universe u v w

namespace FractionalIdeal

variable {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
  [CommRing K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- The original numerator equivalence has the original denominator-scaled value. -/
theorem algebraMap_equivNumOfIsLocalization (I : FractionalIdeal R⁰ K) (x : I) :
    algebraMap R K (I.equivNumOfIsLocalization x : R) = I.den • (x : K) := by
  change (Algebra.linearMap R K)
      ((Submodule.equivMapOfInjective (Algebra.linearMap R K)
        (FaithfulSMul.algebraMap_injective R K) I.num).symm _) = _
  exact Submodule.map_equivMapOfInjective_symm_apply (Algebra.linearMap R K)
    (FaithfulSMul.algebraMap_injective R K) I.num _

variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The native fractional ideal formed by the range of the specified finite map. -/
def finiteEmbeddedImage (f : M →ₗ[R] K) : FractionalIdeal R⁰ K :=
  ⟨f.range, isFractional_of_fg (Submodule.fg_range f)⟩

/-- An injective original map identifies its source with the native numerator ideal. -/
def finiteEmbeddedModuleEquivNum (f : M →ₗ[R] K) (hf : Function.Injective f) :
    M ≃ₗ[R] (finiteEmbeddedImage f).num :=
  (LinearEquiv.ofInjective f hf).trans (finiteEmbeddedImage f).equivNumOfIsLocalization

omit [IsDomain R] in
/-- The numerator coordinate is exactly the original embedding multiplied by its denominator. -/
theorem algebraMap_finiteEmbeddedModuleEquivNum
    (f : M →ₗ[R] K) (hf : Function.Injective f) (m : M) :
    algebraMap R K (finiteEmbeddedModuleEquivNum f hf m : R) =
      (finiteEmbeddedImage f).den • f m :=
  algebraMap_equivNumOfIsLocalization (finiteEmbeddedImage f)
    (LinearEquiv.ofInjective f hf m)

omit [IsDomain R] in
/-- A nonzero original module has a nonzero native numerator ideal. -/
theorem finiteEmbeddedImage_num_ne_bot [Nontrivial M]
    (f : M →ₗ[R] K) (hf : Function.Injective f) :
    (finiteEmbeddedImage f).num ≠ ⊥ := by
  intro h
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let e := finiteEmbeddedModuleEquivNum f hf
  have he : e m = 0 := by
    apply Subtype.ext
    change (e m : R) = 0
    have hx := (e m).property
    simpa only [h, Submodule.mem_bot] using hx
  exact hm (e.injective (he.trans e.map_zero.symm))

end FractionalIdeal

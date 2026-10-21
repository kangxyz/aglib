/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.QuotientComparison
public import Aglib.RingTheory.AdicCompletion.HomComparison

/-!
# Uniqueness of maps from an adic completion

Base-ring-linear maps into separated targets are determined on the original
module. No finite-generation hypothesis on either module is needed.
-/

@[expose] public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N] [IsHausdorff I N]

/-- A linear map from a completion to a separated target is determined by
its values on original elements, when the defining ideal is finitely generated. -/
theorem linearMap_ext_of (hI : I.FG) {f g : AdicCompletion I M →ₗ[R] N}
    (h : ∀ x : M, f (of I M x) = g (of I M x)) : f = g := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n x
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (eval I M n x)
  have hx : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R (AdicCompletion I M))) x =
      Submodule.Quotient.mk (of I M m) := by
    apply (quotientEquiv I M hI n).injective
    simpa only [quotientEquiv_mk, eval_of, Submodule.mkQ_apply] using hm.symm
  have hf := congrArg ((quotientHom I f).val n) hx
  have hg := congrArg ((quotientHom I g).val n) hx
  simp only [quotientHom_apply_mk] at hf hg
  exact hf.trans ((congrArg (Submodule.Quotient.mk (p := I ^ n • ⊤)) (h m)).trans hg.symm)

omit [IsHausdorff I N] in
/-- A bilinear map on completions is determined on pairs of original elements. -/
theorem bilinear_ext_of (hI : I.FG)
    {P : Type*} [AddCommGroup P] [Module R P] [IsHausdorff I P]
    {f g : AdicCompletion I M →ₗ[R] AdicCompletion I N →ₗ[R] P}
    (h : ∀ (x : M) (y : N), f (of I M x) (of I N y) =
      g (of I M x) (of I N y)) : f = g := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hy : ∀ m : M, f (of I M m) y = g (of I M m) y := by
    intro m
    exact LinearMap.congr_fun (linearMap_ext_of I hI (h m)) y
  exact LinearMap.congr_fun
    (linearMap_ext_of I hI (f := (LinearMap.applyₗ y).comp f)
      (g := (LinearMap.applyₗ y).comp g) hy) x

end AdicCompletion

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Recovering linear maps from their adic reductions

A compatible family of maps on the actual ideal-power quotients comes from a
unique linear map when the target is complete. Neither finiteness nor
completeness of the source is required. These are Hom types, not a second
category of formal modules. The forward maps are Mathlib's `reduceModIdeal`.
-/

@[expose] public section

noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable (N : Type*) [AddCommGroup N] [Module R N]

/-- Compatible morphisms between the actual ideal-power quotient systems. -/
def CompatibleQuotientHom :=
  { f : ∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R]
      N ⧸ (I ^ n • ⊤ : Submodule R N) //
    ∀ {m n : ℕ} (h : m ≤ n),
      Submodule.factorPow I N h ∘ₗ f n = f m ∘ₗ Submodule.factorPow I M h }

variable {M N}

/-- The compatible quotient maps induced by an actual linear map. -/
def quotientHom (f : M →ₗ[R] N) : CompatibleQuotientHom I M N :=
  ⟨fun n => (f.reduceModIdeal (I ^ n)).restrictScalars R,
    fun h => transitionMap_comp_reduceModIdeal I f h⟩

@[simp]
theorem quotientHom_apply_mk (f : M →ₗ[R] N) (n : ℕ) (x : M) :
    (quotientHom I f).val n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := rfl

/-- Precomposition with the quotient projections gives a compatible family
with unchanged source. -/
theorem quotientHom_comp_mkQ_compatible (f : CompatibleQuotientHom I M N)
    {m n : ℕ} (h : m ≤ n) :
    Submodule.factorPow I N h ∘ₗ
        (f.val n ∘ₗ (I ^ n • ⊤ : Submodule R M).mkQ) =
      f.val m ∘ₗ (I ^ m • ⊤ : Submodule R M).mkQ := by
  rw [← LinearMap.comp_assoc, f.property h, LinearMap.comp_assoc]
  rfl

variable [IsAdicComplete I N]

/-- Recover a linear map from compatible ideal-power quotient maps. -/
def liftQuotientHom (f : CompatibleQuotientHom I M N) : M →ₗ[R] N :=
  IsAdicComplete.lift I
    (fun n => f.val n ∘ₗ (I ^ n • ⊤ : Submodule R M).mkQ)
    (quotientHom_comp_mkQ_compatible I f)

@[simp]
theorem mkQ_comp_liftQuotientHom (f : CompatibleQuotientHom I M N) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R N).mkQ ∘ₗ liftQuotientHom I f =
      f.val n ∘ₗ (I ^ n • ⊤ : Submodule R M).mkQ :=
  IsAdicComplete.mkQ_comp_lift _ _ _

/-- Equality into a complete target is detected by all actual reductions. -/
theorem quotientHom_injective : Function.Injective (quotientHom I (M := M) (N := N)) := by
  intro f g h
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n x
  exact congrArg (fun q : CompatibleQuotientHom I M N =>
    q.val n (Submodule.Quotient.mk x)) h

@[simp]
theorem quotientHom_liftQuotientHom (f : CompatibleQuotientHom I M N) :
    quotientHom I (liftQuotientHom I f) = f := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact LinearMap.congr_fun (mkQ_comp_liftQuotientHom I f n) x

@[simp]
theorem liftQuotientHom_quotientHom (f : M →ₗ[R] N) :
    liftQuotientHom I (quotientHom I f) = f :=
  quotientHom_injective I (quotientHom_liftQuotientHom I (quotientHom I f))

/-- Morphisms into a complete module are exactly compatible morphisms of
its ideal-power reductions, with the original reduction as forward map. -/
def quotientHomEquiv : (M →ₗ[R] N) ≃ CompatibleQuotientHom I M N where
  toFun := quotientHom I
  invFun := liftQuotientHom I
  left_inv := liftQuotientHom_quotientHom I
  right_inv := quotientHom_liftQuotientHom I

variable (M)

@[simp]
theorem quotientHom_id (n : ℕ) :
    (quotientHom I (LinearMap.id : M →ₗ[R] M)).val n = LinearMap.id := by
  ext x
  rfl

variable {M}
variable {P : Type*} [AddCommGroup P] [Module R P]

omit [IsAdicComplete I N] in
/-- The original reductions preserve composition. -/
theorem quotientHom_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    (quotientHom I (g ∘ₗ f)).val n =
      (quotientHom I g).val n ∘ₗ (quotientHom I f).val n := by
  ext x
  rfl

end AdicCompletion

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.HomComparison
public import Aglib.RingTheory.AdicCompletion.QuotientComparison
public import Aglib.RingTheory.AdicCompletion.CompletedHom

/-!
# Formal Hom comparison on affine modules

Compatible maps between reductions are maps between completions. For finite
modules over a Noetherian ring, they are consequently the completion of Hom.
This compares compatible systems, not individual nonflat reductions of Hom.
-/

@[expose] public section

noncomputable section

namespace AdicCompletion

universe u

section General

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- A compatible family acts on completed elements componentwise. -/
def liftFormalHom (f : CompatibleQuotientHom I M N) :
    AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N :=
  { __ := lift I (fun n => f.val n ∘ₗ eval I M n)
      (fun {m n} h => by
        rw [← LinearMap.comp_assoc, f.property h, LinearMap.comp_assoc,
          transitionMap_comp_eval])
    map_smul' a x := by
      ext n
      dsimp
      rw [val_smul_eq_evalₐ_smul, val_smul_eq_evalₐ_smul]
      exact (LinearMap.extendScalarsOfSurjective
        (Ideal.Quotient.mk_surjective (I := I ^ n)) (f.val n)).map_smul _ _ }

@[simp]
theorem eval_liftFormalHom (f : CompatibleQuotientHom I M N) (n : ℕ)
    (x : AdicCompletion I M) :
    eval I N n (liftFormalHom I f x) = f.val n (eval I M n x) := rfl

/-- The map on original reductions attached to a map of completed modules. -/
def formalHomComponent (hI : I.FG)
    (f : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) (n : ℕ) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  (quotientEquiv I N hI n).toLinearMap ∘ₗ
    (quotientHom I (f.restrictScalars R)).val n ∘ₗ
    (quotientEquiv I M hI n).symm.toLinearMap

/-- The reduction map agrees with the original evaluation maps on completions. -/
theorem formalHomComponent_eval (hI : I.FG)
    (f : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N)
    (n : ℕ) (x : AdicCompletion I M) :
    formalHomComponent I hI f n (eval I M n x) = eval I N n (f x) := by
  have h : (quotientEquiv I M hI n).symm (eval I M n x) =
      Submodule.Quotient.mk x :=
    (LinearEquiv.symm_apply_eq _).mpr (quotientEquiv_mk I M hI n x).symm
  simp only [formalHomComponent, LinearMap.comp_apply, LinearEquiv.coe_coe, h,
    quotientHom_apply_mk, LinearMap.restrictScalars_apply, quotientEquiv_mk]

/-- The induced reduction map acts on the original coordinates of a completed element. -/
@[simp]
theorem formalHomComponent_val (hI : I.FG)
    (f : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N)
    (n : ℕ) (x : AdicCompletion I M) :
    formalHomComponent I hI f n (x.val n) = (f x).val n := by
  simpa only [coe_eval] using formalHomComponent_eval I hI f n x

/-- A map of completed modules gives compatible maps on the original reductions. -/
def formalHom (hI : I.FG)
    (f : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) :
    CompatibleQuotientHom I M N :=
  ⟨formalHomComponent I hI f, by
    intro m n h
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := eval_surjective I M n x
    simp only [LinearMap.comp_apply, formalHomComponent_eval]
    change transitionMap I N h (eval I N n (f x)) =
      formalHomComponent I hI f m (transitionMap I M h (eval I M n x))
    exact (transitionMap_comp_eval_apply I N h (f x)).trans
      ((formalHomComponent_eval I hI f m x).symm.trans
        (congrArg (formalHomComponent I hI f m)
          (transitionMap_comp_eval_apply I M h x).symm))⟩

@[simp]
theorem formalHom_liftFormalHom (hI : I.FG) (f : CompatibleQuotientHom I M N) :
    formalHom I hI (liftFormalHom I f) = f := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := eval_surjective I M n x
  exact formalHomComponent_eval I hI (liftFormalHom I f) n x

@[simp]
theorem liftFormalHom_formalHom (hI : I.FG)
    (f : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) :
    liftFormalHom I (formalHom I hI f) = f := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  exact formalHomComponent_eval I hI f n x

/-- Maps between completions are exactly compatible maps on original reductions. -/
def formalHomEquiv (hI : I.FG) :
    (AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N) ≃
      CompatibleQuotientHom I M N where
  toFun := formalHom I hI
  invFun := liftFormalHom I
  left_inv := liftFormalHom_formalHom I hI
  right_inv := formalHom_liftFormalHom I hI

@[simp]
theorem formalHom_map (hI : I.FG) (f : M →ₗ[R] N) :
    formalHom I hI (map I f) = quotientHom I f := by
  apply Subtype.ext
  funext n
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := eval_surjective I M n x
  exact formalHomComponent_eval I hI (map I f) n x

end General

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- Completion of Hom is Hom of the formal systems of finite modules. -/
def completedHomFormalEquiv :
    AdicCompletion I (M →ₗ[R] N) ≃ CompatibleQuotientHom I M N :=
  (completedHomEquiv I M N).toEquiv.trans (formalHomEquiv I (IsNoetherian.noetherian I))

/-- The completed comparison extends the original reduction maps. -/
@[simp]
theorem completedHomFormalEquiv_of (f : M →ₗ[R] N) :
    completedHomFormalEquiv I (of I (M →ₗ[R] N) f) = quotientHom I f := by
  change formalHom I _ (completedHomEquiv I M N (of I (M →ₗ[R] N) f)) = _
  rw [completedHomEquiv_of]
  exact formalHom_map I (IsNoetherian.noetherian I) f

end AdicCompletion

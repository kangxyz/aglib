/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Connecting maps on native derived sections

The objects are native right-derived section groups. Their connecting map is
chosen via the canonical represented-Ext normalization and the original short
exact extension class. This does not identify an independently preselected
boundary for `Functor.rightDerived`: no such boundary is used here.
-/

@[expose] public noncomputable section

universe u v w e uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

section Abstract

variable {D : Type uC} [Category.{vC} D] [Abelian D] [HasExt.{e} D]
  (P : D) (H : ℕ → D ⥤ AddCommGrpCat.{w})
  (E : ∀ M n, (H n).obj M ≃+ Ext.{e} P M n)

/-- Connecting morphism on specified additive groups normalized to original Ext. -/
def normalizedExtBoundary (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) :
    (H n).obj S.X₃ →+ (H (n + 1)).obj S.X₁ :=
  ((E S.X₁ (n + 1)).symm.toAddMonoidHom).comp
    ((hS.extClass.postcomp P rfl).comp (E S.X₃ n).toAddMonoidHom)

/-- The chosen boundary has the original short exact extension-class formula. -/
theorem normalizedExtBoundary_apply (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ)
    (x : (H n).obj S.X₃) :
    E S.X₁ (n + 1) (normalizedExtBoundary P H E S hS n x) =
      (E S.X₃ n x).comp hS.extClass rfl :=
  (E S.X₁ (n + 1)).apply_symm_apply _

variable (hE : ∀ {M N : D} (f : M ⟶ N) (n : ℕ) (x : (H n).obj M),
  E N n ((H n).map f x) = (E M n x).comp (Ext.mk₀ f) (add_zero n))

include P E hE

/-- The initial degree-zero coefficient map is injective for an original monomorphism. -/
theorem normalizedExtBoundary_injective_zero {M N : D} (f : M ⟶ N) [Mono f] :
    Function.Injective ((H 0).map f) := by
  intro x y h
  apply (E M 0).injective
  apply Ext.postcomp_mk₀_injective_of_mono P f
  exact (hE f 0 x).symm.trans ((congrArg (E N 0) h).trans (hE f 0 y))

/-- Exactness at the middle coefficient object uses its original functorial maps. -/
theorem normalizedExtBoundary_exact₂ (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((H n).map S.f) ((H n).map S.g) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := E S.X₁ n) (e₂ := E S.X₂ n) (e₃ := E S.X₃ n)
    (H := (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₂' P hS n))
  · ext x
    exact (hE S.f n x).symm
  · ext x
    exact (hE S.g n x).symm

/-- Exactness between the last coefficient map and the connecting map. -/
theorem normalizedExtBoundary_exact₃ (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((H n).map S.g) (normalizedExtBoundary P H E S hS n) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := E S.X₂ n) (e₂ := E S.X₃ n) (e₃ := E S.X₁ (n + 1))
    (H := (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' P hS n (n + 1) rfl))
  · ext x
    exact (hE S.g n x).symm
  · ext x
    exact (normalizedExtBoundary_apply P H E S hS n x).symm

/-- Exactness between the connecting map and the first coefficient map. -/
theorem normalizedExtBoundary_exact₁ (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (normalizedExtBoundary P H E S hS n) ((H (n + 1)).map S.f) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := E S.X₃ n) (e₂ := E S.X₁ (n + 1)) (e₃ := E S.X₂ (n + 1))
    (H := (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₁' P hS n (n + 1) rfl))
  · ext x
    exact (normalizedExtBoundary_apply P H E S hS n x).symm
  · ext x
    exact (hE S.f (n + 1) x).symm

end Abstract

section ModuleValued

variable {D : Type uC} [Category.{vC} D] [Abelian D] [HasExt.{e} D]
  {Λ : Type u} [Ring Λ] (P : D) (H : ℕ → D ⥤ ModuleCat.{w} Λ)
  (E : ∀ M n, (H n).obj M ≃+ Ext.{e} P M n)

/-- The full normalization construction with its original module-valued carriers. -/
def moduleNormalizedExtBoundary (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) :
    (H n).obj S.X₃ →+ (H (n + 1)).obj S.X₁ :=
  normalizedExtBoundary P (fun n => H n ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat)
    E S hS n

/-- Original Ext boundary normalization, abstracted before module specialization. -/
theorem moduleNormalizedExtBoundary_apply
    (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) (x : (H n).obj S.X₃) :
    E S.X₁ (n + 1) (moduleNormalizedExtBoundary P H E S hS n x) =
      (E S.X₃ n x).comp hS.extClass rfl :=
  normalizedExtBoundary_apply P
    (fun n => H n ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat) E S hS n x

/-- Preserve the complete endpoint values when specializing boundary normalization. -/
theorem moduleNormalizedExtBoundary_apply_of_eq
    (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ)
    (δ : (H n).obj S.X₃ →+ (H (n + 1)).obj S.X₁)
    (hδ : δ = moduleNormalizedExtBoundary P H E S hS n) (x : (H n).obj S.X₃)
    (E' : (H (n + 1)).obj S.X₁ ≃+ Ext.{e} P S.X₁ (n + 1))
    (hE' : E' = E S.X₁ (n + 1))
    (y : (H (n + 1)).obj S.X₁) (hy : y = δ x)
    (E₃ : (H n).obj S.X₃ ≃+ Ext.{e} P S.X₃ n) (hE₃ : E₃ = E S.X₃ n) :
    E' y = (E₃ x).comp hS.extClass rfl := by
  subst E' y E₃ δ
  exact moduleNormalizedExtBoundary_apply P H E S hS n x

variable (hE : ∀ {M N : D} (f : M ⟶ N) (n : ℕ) (x : (H n).obj M),
  E N n ((H n).map f x) = (E M n x).comp (Ext.mk₀ f) (add_zero n))

include P E hE

/-- Initial injectivity for specified module-valued functors. -/
theorem moduleNormalizedExtBoundary_injective_zero {M N : D} (f : M ⟶ N) [Mono f] :
    Function.Injective ((H 0).map f) :=
  normalizedExtBoundary_injective_zero P
    (fun n => H n ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat) E hE f

/-- Exactness at the middle term for specified module-valued functors. -/
theorem moduleNormalizedExtBoundary_exact₂
    (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((H n).map S.f) ((H n).map S.g) :=
  normalizedExtBoundary_exact₂ P
    (fun n => H n ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat) E hE S hS n

/-- Exactness before the chosen boundary for specified module-valued functors. -/
theorem moduleNormalizedExtBoundary_exact₃
    (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((H n).map S.g) (moduleNormalizedExtBoundary P H E S hS n) :=
  normalizedExtBoundary_exact₃ P
    (fun n => H n ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat) E hE S hS n

/-- Exactness after the chosen boundary for specified module-valued functors. -/
theorem moduleNormalizedExtBoundary_exact₁
    (S : ShortComplex D) (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (moduleNormalizedExtBoundary P H E S hS n) ((H (n + 1)).map S.f) :=
  normalizedExtBoundary_exact₁ P
    (fun n => H n ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat) E hE S hS n

end ModuleValued

end CategoryTheory.Sheaf.ModuleCoefficients

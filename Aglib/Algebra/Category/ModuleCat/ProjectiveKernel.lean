/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Kernels of surjections onto projective modules

In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of modules over a commutative ring with `M₃`
projective, the sequence splits (`ShortComplex.ShortExact.splittingOfProjective`), so `M₁` is a
direct summand of `M₂`. Hence `M₁` is finite and projective when `M₂` is
(`ModuleCat.finite_projective_X₁_of_shortExact`).

This is the module-theoretic step of the finite local freeness of kernels of epimorphisms between
finite locally free sheaves (`Aglib.AlgebraicGeometry.Modules.LocallyFree.Kernel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- In a short exact sequence of modules whose last term is projective, the first term is a direct
summand of the middle term; so it is finite and projective when the middle term is. -/
theorem ModuleCat.finite_projective_X₁_of_shortExact {R : Type u} [CommRing R]
    {T : ShortComplex (ModuleCat.{u} R)} (hT : T.ShortExact) [Module.Finite R T.X₂]
    [Module.Projective R T.X₂] [Module.Projective R T.X₃] :
    Module.Finite R T.X₁ ∧ Module.Projective R T.X₁ := by
  have : Projective T.X₃ := ModuleCat.projective_of_categoryTheory_projective T.X₃
  let split := hT.splittingOfProjective
  have hr : split.r.hom ∘ₗ T.f.hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom split.f_r
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact ⟨Module.Finite.of_surjective split.r.hom (fun x ↦ ⟨T.f.hom x, LinearMap.congr_fun hr x⟩),
    Module.Projective.of_split T.f.hom split.r.hom hr⟩

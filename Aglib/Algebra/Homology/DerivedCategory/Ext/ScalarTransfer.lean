/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Injectivity of original Ext restriction from a scalar transfer

The transfer identity is retained on the actual source morphisms. Invertibility
of the same scalar on the actual coefficient makes precomposition injective,
without an equivalence to another cohomology theory or a direct-image theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe r c h e

namespace CategoryTheory.Abelian.Ext

variable {R : Type r} [Ring R] {C : Type c} [Category.{h} C] [Abelian C]
  [Linear R C] [HasExt.{e} C]

/-- A literal scalar transfer makes original Ext restriction injective if that
scalar is invertible on the coefficient object. -/
theorem precomp_injective_of_scalar_transfer {P Q A : C}
    (f : P ⟶ Q) (τ : Q ⟶ P) (r : R) (hτ : τ ≫ f = r • 𝟙 Q)
    [IsIso (r • 𝟙 A)] (q : ℕ) :
    Function.Injective (fun x : Ext Q A q => (mk₀ f).comp x (Nat.zero_add q)) := by
  intro x y hxy
  have h := congrArg (fun z : Ext P A q => (mk₀ τ).comp z (Nat.zero_add q)) hxy
  simp only [mk₀_comp_mk₀_assoc, hτ, mk₀_smul, smul_comp, mk₀_id_comp] at h
  let E : Ext Q A q ≃+ Ext Q A q :=
    (((extFunctor q).obj (op Q)).mapIso (asIso (r • 𝟙 A))).addCommGroupIsoToAddEquiv
  apply E.injective
  change x.comp (mk₀ (r • 𝟙 A)) (Nat.add_zero q) =
    y.comp (mk₀ (r • 𝟙 A)) (Nat.add_zero q)
  simpa only [← smul_eq_comp_mk₀] using h

end CategoryTheory.Abelian.Ext

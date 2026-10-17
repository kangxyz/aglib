/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Aglib.RingTheory.Descent.FinitePresentation

/-!
# Invertibility of modules descends along faithfully flat ring maps

For a faithfully flat `A`-algebra `B`, an `A`-module `M` is invertible (Mathlib's
`Module.Invertible`: the contraction `Mᵛ ⊗[A] M → A` is bijective) if and only if
`B ⊗[A] M` is an invertible `B`-module. Compare Stacks Project, Tag 05B2 (fpqc descent of
finite local freeness of quasi-coherent sheaves); the proof here does not use it, but descends
finite presentation and the bijectivity of the contraction.
Mathlib supplies the base-change direction; this file proves descent. The descended module is
finitely presented
(`Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`), so its dual
commutes with the flat base change (`Module.FinitePresentation.isBaseChange_map`),
and the base change of the contraction is the contraction of `B ⊗[A] M`.
-/

@[expose] public section

open TensorProduct

namespace Module.Invertible

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (M : Type*) [AddCommGroup M]
  [Module A M]

/-- The dual `Module.Dual A M` with only its additive-group and module structures registered.
Mathlib's faithfully flat criteria are stated for additive groups, whereas `contractLeft` is
stated with the semimodule structure `LinearMap.addCommMonoid`; this synonym lets instance
search find `TensorProduct.addCommGroup` for its tensor product with `M`. -/
def DualAddCommGroup : Type _ := Module.Dual A M

instance : AddCommGroup (DualAddCommGroup A M) :=
  inferInstanceAs (AddCommGroup (Module.Dual A M))

instance : Module A (DualAddCommGroup A M) :=
  inferInstanceAs (Module A (Module.Dual A M))

/-- The identity of the dual, between the synonym and `Module.Dual A M`. -/
def dualAddCommGroupEquiv : DualAddCommGroup A M ≃ₗ[A] Module.Dual A M where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Invertibility descends along a faithfully flat ring map. -/
theorem of_invertible_tensorProduct_of_faithfullyFlat [Module.FaithfullyFlat A B]
    [Module.Invertible B (B ⊗[A] M)] : Module.Invertible A M := by
  have : Module.FinitePresentation B (B ⊗[A] M) := Module.finitePresentation_of_projective _ _
  have : Module.FinitePresentation A M :=
    Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat A B M
  let φ : B ⊗[A] Module.Dual A M ≃ₗ[B] Module.Dual B (B ⊗[A] M) :=
    (Module.FinitePresentation.isBaseChange_map A M A B).equiv ≪≫ₗ
      LinearEquiv.congrRight (AlgebraTensorModule.rid A B B)
  let Ψ : B ⊗[A] (Module.Dual A M ⊗[A] M) ≃ₗ[B]
      Module.Dual B (B ⊗[A] M) ⊗[B] (B ⊗[A] M) :=
    AlgebraTensorModule.distribBaseChange A B (Module.Dual A M) M ≪≫ₗ
      AlgebraTensorModule.congr φ (LinearEquiv.refl B _)
  have key : ∀ x, AlgebraTensorModule.rid A B B ((contractLeft A M).lTensor B x) =
      contractLeft B (B ⊗[A] M) (Ψ x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul b y =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
      | tmul ℓ m =>
        simp [Ψ, φ, IsBaseChange.equiv_tmul, contractLeft_apply, LinearMap.baseChange_tmul]
  have hb : Function.Bijective (fun x ↦ contractLeft B (B ⊗[A] M) (Ψ x)) :=
    (Module.Invertible.bijective (R := B) (M := B ⊗[A] M)).comp Ψ.bijective
  rw [← funext key] at hb
  have h₂ : Function.Bijective ((contractLeft A M).lTensor B) :=
    (Function.Bijective.of_comp_iff' (AlgebraTensorModule.rid A B B).bijective _).mp hb
  let e := TensorProduct.congr (dualAddCommGroupEquiv A M) (LinearEquiv.refl A M)
  let c' := contractLeft A M ∘ₗ e.toLinearMap
  have h₃ : Function.Bijective (c'.lTensor B) := by
    rw [LinearMap.lTensor_comp, LinearMap.coe_comp]
    exact h₂.comp (LinearEquiv.lTensor B e).bijective
  have hc' : Function.Bijective c' :=
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B c').mp h₃
  have hc : Function.Bijective (contractLeft A M) := by
    have : ⇑(contractLeft A M) = ⇑c' ∘ ⇑e.symm := by
      funext x
      simp [c']
    rw [this]
    exact hc'.comp e.symm.bijective
  exact ⟨hc⟩

/-- Over a faithfully flat `A`-algebra `B`, `M` is invertible if and only if `B ⊗[A] M` is. -/
theorem iff_invertible_tensorProduct_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Module.Invertible B (B ⊗[A] M) ↔ Module.Invertible A M :=
  ⟨fun _ ↦ of_invertible_tensorProduct_of_faithfullyFlat A B M, fun _ ↦ inferInstance⟩

end Module.Invertible

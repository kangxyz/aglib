/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The linear cokernel presentation of degree-one Ext

For a short exact sequence with projective middle object in an R-linear
abelian category, the original connecting map presents degree-one Ext as the
cokernel of restriction on Hom. All objects, scalar actions, and extension
classes are native. The Ext universe is independent of the category universes.
-/

@[expose] public section

noncomputable section

universe t w v u

open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type t} [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
    [Linear R C] [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) (N : C)

/-- The native extension-class connecting map, with Hom as its source. -/
def homConnectingLinearMap : (S.X₁ ⟶ N) →ₗ[R] Ext.{w} S.X₃ N 1 :=
  (hS.extClass.precompOfLinear R N (by decide : 1 + 0 = 1)).comp
    (Ext.linearEquiv₀ (R := R)).symm.toLinearMap

/-- The map uses the original extension class and the original morphism. -/
@[simp]
theorem homConnectingLinearMap_apply (f : S.X₁ ⟶ N) :
    hS.homConnectingLinearMap (R := R) N f =
      hS.extClass.comp (Ext.mk₀ f) (by decide : 1 + 0 = 1) := rfl

/-- The kernel of the connecting map consists exactly of morphisms that
extend across the middle object. -/
theorem ker_homConnectingLinearMap :
    LinearMap.ker (hS.homConnectingLinearMap (R := R) N) =
      LinearMap.range (Linear.leftComp R N S.f) := by
  ext f
  constructor
  · intro hf
    obtain ⟨ξ, hξ⟩ := Ext.contravariant_sequence_exact₁ hS N (Ext.mk₀ f)
      (by decide : 1 + 0 = 1) hf
    obtain ⟨g, hg⟩ := (Ext.mk₀_bijective S.X₂ N).surjective ξ
    rw [← hg, Ext.mk₀_comp_mk₀] at hξ
    exact ⟨g, (Ext.mk₀_bijective S.X₁ N).injective hξ⟩
  · rintro ⟨g, rfl⟩
    change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (by decide : 1 + 0 = 1) = 0
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ g)

/-- Without a projectivity assumption, the Hom cokernel still maps naturally
and injectively into degree-one Ext by the original connecting map. -/
def homCokernelExtOneLinearMap :
    ((S.X₁ ⟶ N) ⧸ LinearMap.range (Linear.leftComp R N S.f)) →ₗ[R]
      Ext.{w} S.X₃ N 1 :=
  (LinearMap.range (Linear.leftComp R N S.f)).liftQ
    (hS.homConnectingLinearMap (R := R) N)
    (hS.ker_homConnectingLinearMap (R := R) N).symm.le

/-- Exactness, not projectivity, gives injectivity of the cokernel map. -/
theorem homCokernelExtOneLinearMap_injective :
    Function.Injective (hS.homCokernelExtOneLinearMap (R := R) N) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _
    (hS.ker_homConnectingLinearMap (R := R) N).le

/-- The injective cokernel map preserves the native extension-class formula. -/
@[simp]
theorem homCokernelExtOneLinearMap_mk (f : S.X₁ ⟶ N) :
    hS.homCokernelExtOneLinearMap (R := R) N (Submodule.Quotient.mk f) =
      hS.extClass.comp (Ext.mk₀ f) (by decide : 1 + 0 = 1) := rfl

/-- Projectivity of the middle object makes the original connecting map
surjective, without an enough-projectives assumption on the category. -/
theorem homConnectingLinearMap_surjective [Projective S.X₂] :
    Function.Surjective (hS.homConnectingLinearMap (R := R) N) := by
  intro ξ
  obtain ⟨η, hη⟩ := Ext.contravariant_sequence_exact₃ hS N ξ
    (Ext.eq_zero_of_projective _) (by decide : 1 + 0 = 1)
  refine ⟨Ext.linearEquiv₀ (R := R) η, ?_⟩
  simpa only [homConnectingLinearMap_apply, Ext.mk₀_linearEquiv₀_apply] using hη

/-- The actual R-linear cokernel presentation of degree-one Ext from a short
exact sequence with projective middle object. -/
def homCokernelExtOneLinearEquiv [Projective S.X₂] :
    ((S.X₁ ⟶ N) ⧸ LinearMap.range (Linear.leftComp R N S.f)) ≃ₗ[R]
      Ext.{w} S.X₃ N 1 :=
  (Submodule.quotEquivOfEq _ _ (hS.ker_homConnectingLinearMap (R := R) N).symm).trans
    ((hS.homConnectingLinearMap (R := R) N).quotKerEquivOfSurjective
      (hS.homConnectingLinearMap_surjective (R := R) N))

/-- A quotient representative maps by the original extension-class formula. -/
@[simp]
theorem homCokernelExtOneLinearEquiv_mk [Projective S.X₂] (f : S.X₁ ⟶ N) :
    hS.homCokernelExtOneLinearEquiv (R := R) N (Submodule.Quotient.mk f) =
      hS.extClass.comp (Ext.mk₀ f) (by decide : 1 + 0 = 1) := rfl

end CategoryTheory.ShortComplex.ShortExact

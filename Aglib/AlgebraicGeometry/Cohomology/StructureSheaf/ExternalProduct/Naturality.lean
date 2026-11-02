/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Naturality of the original external cohomology product

Flat geometric pullback preserves the literal external cup product. The
whole tensor and finite-antidiagonal maps retain their original source
cohomology groups and the actual product of the two morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The original product of flat morphisms is flat, by the actual two base changes. -/
theorem structureProduct_map_flat {X₀ X₁ Y₀ Y₁ : FScheme k}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) [Flat f.left] [Flat g.left] :
    Flat (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance f.w.symm g.w.symm

/-- Pullback of the original external cup along any flat map to the product. -/
theorem structureExternalCup_pullback_of_flat {X Y Z : FScheme k}
    (f : Z ⟶ X ⊗ Y) [Flat f.left] {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureCohomologyPullbackLinear f n (structureExternalCup X Y h x y) =
      structureCup Z h
        (structureCohomologyPullbackLinear (f ≫ fst X Y) p x)
        (structureCohomologyPullbackLinear (f ≫ snd X Y) q y) := by
  rw [structureExternalCup_apply, structureCup_pullback_of_flat]
  simp only [structureCohomologyPullbackLinear_comp, LinearMap.comp_apply]

/-- Whole flat naturality on the original homogeneous bilinear product. -/
theorem structureExternalCup_naturality {X₀ X₁ Y₀ Y₁ : FScheme k}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) [Flat f.left] [Flat g.left]
    {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X₁ p) (y : structureCohomology k Y₁ q) :
    structureCohomologyPullbackLinear (f ⊗ₘ g) n (structureExternalCup X₁ Y₁ h x y) =
      structureExternalCup X₀ Y₀ h (structureCohomologyPullbackLinear f p x)
        (structureCohomologyPullbackLinear g q y) := by
  have : Flat (f ⊗ₘ g).left := structureProduct_map_flat f g
  rw [structureExternalCup_pullback_of_flat, tensorHom_fst, tensorHom_snd,
    structureExternalCup_apply]
  simp only [structureCohomologyPullbackLinear_comp, LinearMap.comp_apply]

/-- Whole naturality of the original linear tensor map. -/
theorem structureExternalTensor_naturality {X₀ X₁ Y₀ Y₁ : FScheme k}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) [Flat f.left] [Flat g.left]
    {p q n : ℕ} (h : p + q = n) :
    structureCohomologyPullbackLinear (f ⊗ₘ g) n ∘ₗ structureExternalTensor X₁ Y₁ h =
      structureExternalTensor X₀ Y₀ h ∘ₗ TensorProduct.map
        (structureCohomologyPullbackLinear f p) (structureCohomologyPullbackLinear g q) := by
  apply TensorProduct.ext'
  intro x y
  simpa only [LinearMap.comp_apply, TensorProduct.map_tmul, structureExternalTensor_tmul]
    using structureExternalCup_naturality f g h x y

/-- The native antidiagonal map induced by the original two cohomology pullbacks. -/
def structureKunnethSumPullback {X₀ X₁ Y₀ Y₁ : FScheme k}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (n : ℕ) :
    structureKunnethSum X₁ Y₁ n →ₗ[k] structureKunnethSum X₀ Y₀ n :=
  DirectSum.lmap (fun s : HomologicalComplex₂.TotalDegree n => TensorProduct.map
    (structureCohomologyPullbackLinear f s.val.1) (structureCohomologyPullbackLinear g s.val.2))

@[simp]
theorem structureKunnethSumPullback_lof {X₀ X₁ Y₀ Y₁ : FScheme k}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (n : ℕ) (s : HomologicalComplex₂.TotalDegree n)
    (z : structureCohomology k X₁ s.val.1 ⊗[k] structureCohomology k Y₁ s.val.2) :
    structureKunnethSumPullback f g n (DirectSum.lof k _ _ s z) =
      DirectSum.lof k _ _ s (TensorProduct.map (structureCohomologyPullbackLinear f s.val.1)
        (structureCohomologyPullbackLinear g s.val.2) z) :=
  DirectSum.lmap_lof _ _ _

/-- Whole flat naturality of the original finite-antidiagonal Künneth map. -/
theorem structureKunnethMap_naturality {X₀ X₁ Y₀ Y₁ : FScheme k}
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) [Flat f.left] [Flat g.left] (n : ℕ) :
    structureCohomologyPullbackLinear (f ⊗ₘ g) n ∘ₗ structureKunnethMap X₁ Y₁ n =
      structureKunnethMap X₀ Y₀ n ∘ₗ structureKunnethSumPullback f g n := by
  apply DirectSum.linearMap_ext k
  intro s
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, structureKunnethMap_lof, structureKunnethSumPullback_lof]
  exact LinearMap.congr_fun (structureExternalTensor_naturality f g s.property) z

end AlgebraicGeometry.Scheme.Cohomology

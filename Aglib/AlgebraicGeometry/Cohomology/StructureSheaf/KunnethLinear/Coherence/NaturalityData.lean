/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Values
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup.PullbackLinear
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Coherence
public import Aglib.Algebra.Graded.TensorProduct.NaturalityMaps

/-!
# Data for naturality of the original total Kunneth operator

The chosen native operator has the original homogeneous values, product
naturality and associativity. Original unrestricted pullback laws are imported
from their lower owner before group coalgebra assembly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The original cup families, pullbacks and flat compatibility supplied as one typed input. -/
def structureExternalNaturalityInputs
    {X₀ X₁ Y₀ Y₁ : FScheme k} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    [Flat f.left] [Flat g.left] :
    @DirectSum.NaturalityInputs k
      ‹Field k›
      (structureCohomology k X₁) (structureCohomology k Y₁)
      (structureCohomology k (X₁ ⊗ Y₁))
      (structureCohomology k X₀) (structureCohomology k Y₀)
      (structureCohomology k (X₀ ⊗ Y₀))
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k X₁ n)).toAddCommMonoid)
      (structureCohomologyModule X₁)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k Y₁ n)).toAddCommMonoid)
      (structureCohomologyModule Y₁)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k (X₁ ⊗ Y₁) n)).toAddCommMonoid)
      (structureCohomologyModule (X₁ ⊗ Y₁))
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k X₀ n)).toAddCommMonoid)
      (structureCohomologyModule X₀)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k Y₀ n)).toAddCommMonoid)
      (structureCohomologyModule Y₀)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k (X₀ ⊗ Y₀) n)).toAddCommMonoid)
      (structureCohomologyModule (X₀ ⊗ Y₀)) where
  cup := @structureExternalCup k ‹Field k› X₁ Y₁
  cup' := @structureExternalCup k ‹Field k› X₀ Y₀
  leftPullback := @structureCohomologyPullbackLinear k ‹Field k› X₀ X₁ f
  rightPullback := @structureCohomologyPullbackLinear k ‹Field k› Y₀ Y₁ g
  productPullback :=
    @structureCohomologyPullbackLinear k ‹Field k› (X₀ ⊗ Y₀) (X₁ ⊗ Y₁) (f ⊗ₘ g)
  compatibility := by
    as_aux_lemma =>
      let kField : Field k := ‹Field k›
      have hFlatF : Flat f.left := ‹Flat f.left›
      have hFlatG : Flat g.left := ‹Flat g.left›
      exact fun (i j d : ℕ) (h : i + j = d)
          (x : structureCohomology k X₁ i) (y : structureCohomology k Y₁ j) =>
        @structureExternalCup_naturality k kField X₀ X₁ Y₀ Y₁ f g
          hFlatF hFlatG i j d h x y

/-- The product pullback assembled from its original degreewise components. -/
theorem structureExternalNaturalityInputs_totalPullback
    {X₀ X₁ Y₀ Y₁ : FScheme k} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    [Flat f.left] [Flat g.left] :
    structureCohomologyAlgebraPullbackLinear (f ⊗ₘ g) =
      DirectSum.lmap (structureExternalNaturalityInputs f g).productPullback := rfl

/-- The left pullback assembled from its original degreewise components. -/
theorem structureExternalNaturalityInputs_totalLeftPullback
    {X₀ X₁ Y₀ Y₁ : FScheme k} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    [Flat f.left] [Flat g.left] :
    structureCohomologyAlgebraPullbackLinear f =
      DirectSum.lmap (structureExternalNaturalityInputs f g).leftPullback := rfl

/-- The right pullback assembled from its original degreewise components. -/
theorem structureExternalNaturalityInputs_totalRightPullback
    {X₀ X₁ Y₀ Y₁ : FScheme k} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    [Flat f.left] [Flat g.left] :
    structureCohomologyAlgebraPullbackLinear g =
      DirectSum.lmap (structureExternalNaturalityInputs f g).rightPullback := rfl

/-- Identify the total maps with the maps of the given degreewise families. -/
theorem structureExternalNaturalityInputs_mapIdentifications
    {X₀ X₁ Y₀ Y₁ : FScheme k} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    [Flat f.left] [Flat g.left] :
    (structureExternalNaturalityInputs f g).MapIdentifications
      (structureExternalLinearMap X₁ Y₁) (structureExternalLinearMap X₀ Y₀)
      (structureCohomologyAlgebraPullbackLinear (f ⊗ₘ g))
      (structureCohomologyAlgebraPullbackLinear f) (structureCohomologyAlgebraPullbackLinear g) :=
  ⟨rfl, rfl, structureExternalNaturalityInputs_totalPullback f g,
    structureExternalNaturalityInputs_totalLeftPullback f g,
    structureExternalNaturalityInputs_totalRightPullback f g⟩

end AlgebraicGeometry.Scheme.Cohomology

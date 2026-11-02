/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Composition
public import Aglib.Algebra.Homology.TotalComplex.FirstQuadrant
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# External product on the original structure-sheaf cohomology

The map is literally first-projection pullback followed by the original
Yoneda cup with second-projection pullback. Its target is the selected
native relative product. The finite antidiagonal map sums these original
homogeneous maps; no comparison cohomology or resolution is a public input.
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

variable {k : Type u} [Field k] (X Y : FScheme k)

/-- The actual first projection of the selected native product is flat over a field. -/
theorem structureProduct_fst_flat : Flat (fst X Y).left :=
  inferInstanceAs (Flat (Limits.pullback.fst X.hom Y.hom))

/-- The actual second projection of the selected native product is flat over a field. -/
theorem structureProduct_snd_flat : Flat (snd X Y).left :=
  inferInstanceAs (Flat (Limits.pullback.snd X.hom Y.hom))

/-- The original external cup product, in the specified first-then-second order. -/
def structureExternalCup {p q n : ℕ} (h : p + q = n) :
    structureCohomology k X p →ₗ[k] structureCohomology k Y q →ₗ[k]
      structureCohomology k (X ⊗ Y) n :=
  (structureCup (X ⊗ Y) h).compl₁₂
    (structureCohomologyPullbackLinear (fst X Y) p)
    (structureCohomologyPullbackLinear (snd X Y) q)

/-- Its formula is the literal original pair of pullbacks followed by cup. -/
theorem structureExternalCup_apply {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureExternalCup X Y h x y = structureCup (X ⊗ Y) h
      (structureCohomologyPullbackLinear (fst X Y) p x)
      (structureCohomologyPullbackLinear (snd X Y) q y) := rfl

/-- The left external cup unit is the original second-projection pullback. -/
@[simp]
theorem structureExternalCup_unit_left {n : ℕ} (y : structureCohomology k Y n) :
    structureExternalCup X Y (Nat.zero_add n) (structureCupUnit X) y =
      structureCohomologyPullbackLinear (snd X Y) n y := by
  rw [structureExternalCup_apply, structureCohomologyPullbackLinear_cupUnit,
    structureCup_unit_left]

/-- The right external cup unit is the original first-projection pullback. -/
@[simp]
theorem structureExternalCup_unit_right {n : ℕ} (x : structureCohomology k X n) :
    structureExternalCup X Y (Nat.add_zero n) x (structureCupUnit Y) =
      structureCohomologyPullbackLinear (fst X Y) n x := by
  rw [structureExternalCup_apply, structureCohomologyPullbackLinear_cupUnit,
    structureCup_unit_right]

/-- The canonical map from the tensor of the original cohomology groups. -/
def structureExternalTensor {p q n : ℕ} (h : p + q = n) :
    structureCohomology k X p ⊗[k] structureCohomology k Y q →ₗ[k]
      structureCohomology k (X ⊗ Y) n :=
  TensorProduct.lift (structureExternalCup X Y h)

@[simp]
theorem structureExternalTensor_tmul {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureExternalTensor X Y h (x ⊗ₜ[k] y) = structureExternalCup X Y h x y := rfl

/-- The native finite antidiagonal of original cohomology tensor products. -/
abbrev structureKunnethSum (n : ℕ) : Type (u + 1) :=
  DirectSum (HomologicalComplex₂.TotalDegree n)
    (fun s => structureCohomology k X s.val.1 ⊗[k] structureCohomology k Y s.val.2)

/-- The canonical graded Künneth map, defined by the original external products.
Bijectivity is a separate genuine geometric theorem. -/
def structureKunnethMap (n : ℕ) : structureKunnethSum X Y n →ₗ[k]
    structureCohomology k (X ⊗ Y) n :=
  DirectSum.toModule k _ _
    (fun s : HomologicalComplex₂.TotalDegree n => structureExternalTensor X Y s.property)

/-- Each original antidiagonal summand keeps the original external tensor map. -/
@[simp]
theorem structureKunnethMap_lof (n : ℕ) (s : HomologicalComplex₂.TotalDegree n)
    (z : structureCohomology k X s.val.1 ⊗[k] structureCohomology k Y s.val.2) :
    structureKunnethMap X Y n (DirectSum.lof k _ _ s z) =
      structureExternalTensor X Y s.property z := by
  unfold structureKunnethMap
  exact DirectSum.toModule_lof
    (φ := fun t : HomologicalComplex₂.TotalDegree n => structureExternalTensor X Y t.property) k s z

end AlgebraicGeometry.Scheme.Cohomology

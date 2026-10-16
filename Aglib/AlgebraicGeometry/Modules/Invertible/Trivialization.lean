/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic

/-!
# Actual unit-chart coordinates and generators

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/Picard/RationalTrivialization.lean`, SHA-256
  `b1d35c6a55a09b4c5bbe7d5e391e85cb0afbbfaa5041df39d6e71808ece303ea`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u}) (M : SheafOfModules.{u} X.ringCatSheaf)

/-- Section coordinates in the specified actual unit chart, without an integral-scheme premise. -/
def chartSectionEquiv (W : X.Opens)
    (e : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (U : X.Opens) (h : U ≤ W) : M.val.obj (op U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  ((PresheafOfModules.evaluation (X.ringCatSheaf.over W).obj (op (Over.mk (homOfLE h)))).mapIso
    ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

/-- The section corresponding to one in the specified actual unit chart. -/
def chartGenerator (W : X.Opens)
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) : M.val.obj (op W) :=
  (chartSectionEquiv X M W d W le_rfl).symm 1

theorem chartGenerator_restrict (W : X.Opens)
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (V : X.Opens) (h : V ≤ W) :
    M.val.map (homOfLE h).op (chartGenerator X M W d) =
      (chartSectionEquiv X M W d V h).symm 1 := by
  let i : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 W) := Over.homMk (homOfLE h)
  have hn := PresheafOfModules.naturality_apply d.inv.val i.op (1 : Γ(X, W))
  change (chartSectionEquiv X M W d V h).symm (X.presheaf.map (homOfLE h).op 1) =
    M.val.map (homOfLE h).op (chartGenerator X M W d) at hn
  rw [map_one] at hn
  exact hn.symm

end AlgebraicGeometry.Scheme.Modules.Invertible
end

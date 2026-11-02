/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct

/-! The original finite antidiagonal map and the original cup units are
used without supplying an arbitrary cohomology comparison. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

example (p q n : ℕ) (h : p + q = n)
    (x : Scheme.structureCohomology k X p) (y : Scheme.structureCohomology k Y q) :
    structureKunnethMap X Y n
      (DirectSum.lof k _ _ (⟨(p, q), h⟩ : HomologicalComplex₂.TotalDegree n) (x ⊗ₜ[k] y)) =
      structureCup (X ⊗ Y) h
        (structureCohomologyPullbackLinear (fst X Y) p x)
        (structureCohomologyPullbackLinear (snd X Y) q y) := by
  rw [structureKunnethMap_lof]
  change structureExternalTensor X Y h (x ⊗ₜ[k] y) = _
  exact (structureExternalTensor_tmul X Y h x y).trans
    (structureExternalCup_apply X Y h x y)

example (n : ℕ) (x : Scheme.structureCohomology k X n) :
    structureExternalTensor X Y (Nat.add_zero n) (x ⊗ₜ[k] structureCupUnit Y) =
      structureCohomologyPullbackLinear (fst X Y) n x := by
  rw [structureExternalTensor_tmul, structureExternalCup_unit_right]

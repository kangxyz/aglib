/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.GrpObjShear
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Flat multiplication of a flat group scheme

The original multiplication is the existing shear automorphism's inverse
followed by the original first projection. Flatness follows from the
structural morphism by actual base change and composition. No reducedness,
smoothness, properness, finite type, or field hypothesis is required.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} (G : Over S) [Flat G.hom]

/-- The original first projection of the native relative square is flat. -/
theorem flat_fst : Flat (fst G G).left :=
  inferInstanceAs (Flat (CategoryTheory.Limits.pullback.fst G.hom G.hom))

/-- The original second projection of the native relative square is flat. -/
theorem flat_snd : Flat (snd G G).left :=
  inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd G.hom G.hom))

variable [GrpObj G]

/-- Multiplication of a flat group scheme is flat, through the original
shear isomorphism and the original projection. -/
theorem flat_mul : Flat (μ[G]).left := by
  have hm : (GrpObj.shearIso G).inv ≫ fst G G = μ[G] := by
    rw [MonObj.mul_eq_mul]
    exact lift_fst _ _
  have : Flat (fst G G).left := flat_fst G
  have : IsIso (GrpObj.shearIso G).inv.left :=
    inferInstanceAs (IsIso (((Over.forget S).mapIso (GrpObj.shearIso G)).inv))
  rw [← hm, Over.comp_left]
  infer_instance

end AlgebraicGeometry.Scheme.Group

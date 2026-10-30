/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientClosure
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Finite powers of actual finite locally constant coefficients

A single original trivializing family simultaneously trivializes any finite
power. Both the sheaf product and the finite constant value are native
categorical products; no finiteness of arbitrary scheme sections is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u

attribute [local instance] hasSheafifyLarge Fintype.ofFinite

variable {X : Scheme.{u}} {F : AbelianSheaf.{u, u + 1} X}

/-- A finite product of finite additive values has a finite underlying carrier,
using the original product projections rather than a replacement product. -/
theorem finite_product_value (I : Type u) [Finite I]
    (A : AddCommGrpCat.{u + 1}) [Finite A] :
    Finite (∏ᶜ (fun _ : I => A) : AddCommGrpCat.{u + 1}) :=
  AddCommGrpCat.finite_power_value I A

/-- The same actual local charts trivialize every finite power of a finite
locally constant coefficient. -/
def finitePowerTrivialization (t : FiniteLocalTrivialization F)
    (I : Type u) [Finite I] : FiniteLocalTrivialization (∏ᶜ fun _ : I => F) :=
  t.finitePower I

/-- Finite powers preserve actual finite local constancy. -/
theorem isFiniteLocallyConstant_finitePower (I : Type u) [Finite I]
    (hF : IsFiniteLocallyConstant F) :
    IsFiniteLocallyConstant (∏ᶜ fun _ : I => F) :=
  AlgebraicGeometry.Scheme.EtaleCohomology.isFiniteLocallyConstant_finitePower I hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields

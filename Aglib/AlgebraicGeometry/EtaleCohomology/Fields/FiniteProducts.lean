/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

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
    Finite (∏ᶜ (fun _ : I => A) : AddCommGrpCat.{u + 1}) := by
  apply Finite.of_injective (fun x : (∏ᶜ (fun _ : I => A) : AddCommGrpCat.{u + 1}) =>
    fun i : I => (Pi.π (fun _ : I => A) i) x)
  intro x y h
  exact Concrete.limit_ext (Discrete.functor (fun _ : I => A)) x y
    (fun i => congrFun h i.as)

/-- The same actual local charts trivialize every finite power of a finite
locally constant coefficient. -/
def finitePowerTrivialization (t : FiniteLocalTrivialization F)
    (I : Type u) [Finite I] : FiniteLocalTrivialization (∏ᶜ fun _ : I => F) where
  index := t.index
  chart := t.chart
  covers := t.covers
  value j := ∏ᶜ fun _ : I => t.value j
  finite_value j := by
    let := t.finite_value j
    exact finite_product_value I (t.value j)
  trivialization j :=
    PreservesProduct.iso (inverseImage (t.chart j).hom) (fun _ : I => F) ≪≫
      Pi.mapIso (fun _ : I => t.trivialization j) ≪≫
        (PreservesProduct.iso
          (constantSheaf (Scheme.smallEtaleTopology (t.chart j).left)
            AddCommGrpCat.{u + 1}) (fun _ : I => t.value j)).symm

/-- Finite powers preserve actual finite local constancy. -/
theorem isFiniteLocallyConstant_finitePower (I : Type u) [Finite I]
    (hF : IsFiniteLocallyConstant F) :
    IsFiniteLocallyConstant (∏ᶜ fun _ : I => F) := by
  obtain ⟨t⟩ := hF
  exact ⟨finitePowerTrivialization t I⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields

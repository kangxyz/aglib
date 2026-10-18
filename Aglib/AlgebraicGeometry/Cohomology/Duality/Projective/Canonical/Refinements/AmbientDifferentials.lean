/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Original affine differential maps after ambient scalar extension

The original native Kähler map is transposed through the original scalar
adjunction. Its unit-tensor formula and extensionality retain the actual
differentials, including for a principal localization or a ring isomorphism.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {R A A' : CommRingCat.{u}} (α : R ⟶ A) (φ : A ⟶ A')

/-- The actual scalar extension of the original native ambient differential map. -/
def canonicalAmbientDifferentialMap :
    (ModuleCat.extendScalars φ.hom).obj (CommRingCat.KaehlerDifferential α) ⟶
      CommRingCat.KaehlerDifferential (α ≫ φ) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map
      (f := α) (f' := α ≫ φ) (g := 𝟙 R) (g' := φ) (by simp))

/-- The original unit tensor of a differential goes to the differential of its actual image. -/
theorem canonicalAmbientDifferentialMap_one_tmul (a : A) :
    canonicalAmbientDifferentialMap α φ
        ((1 : A') ⊗ₜ[A,φ.hom] CommRingCat.KaehlerDifferential.d (f := α) a) =
      CommRingCat.KaehlerDifferential.d (f := α ≫ φ) (φ a) := by
  let adj := ModuleCat.extendRestrictScalarsAdj φ.hom
  let κ := CommRingCat.KaehlerDifferential.map
    (f := α) (f' := α ≫ φ) (g := 𝟙 R) (g' := φ) (by simp)
  have h := (adj.homEquiv _ _).apply_symm_apply κ
  have he := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (canonicalAmbientDifferentialMap α φ) (CommRingCat.KaehlerDifferential.d (f := α) a)
  exact he.symm.trans ((ConcreteCategory.congr_hom h _).trans
    (CommRingCat.KaehlerDifferential.map_d (by simp) a))

/-- Original unit tensors of differentials determine every map from this actual extension. -/
theorem canonicalAmbientDifferentialMap_ext {M : ModuleCat.{u} A'}
    {f g : (ModuleCat.extendScalars φ.hom).obj (CommRingCat.KaehlerDifferential α) ⟶ M}
    (h : ∀ a : A,
      f ((1 : A') ⊗ₜ[A,φ.hom] CommRingCat.KaehlerDifferential.d (f := α) a) =
        g ((1 : A') ⊗ₜ[A,φ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)) : f = g := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  exact h a

end AlgebraicGeometry.Scheme.Modules

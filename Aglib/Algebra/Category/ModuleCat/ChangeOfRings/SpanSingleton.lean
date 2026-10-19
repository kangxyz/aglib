/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.KernelBaseChange

/-!
# Scalar extension of maps out of the ring

For a map of commutative rings `φ : A' ⟶ B'`, an `A'`-module `P` with an element `x` and a
`B'`-module `Q` with an element `y`, extension of scalars of `a ↦ a • x`, followed by a map
`e : B' ⊗_{A'} P ⟶ Q` with `e (1 ⊗ x) = y`, is `b ↦ b • y` after the unit comparison
`scalarExtensionUnit φ : B' ⊗_{A'} A' ⟶ B'` (`extendScalars_map_toSpanSingleton_comp`). The
hypothesis on `e` is stated through the scalar-extension adjunction, so no tensor elements in two
presentations are compared.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace ModuleCat

/-- Extension of scalars of `a ↦ a • x`, followed by a map `e`, is `b ↦ b • y` after the unit
comparison, when `e (1 ⊗ x) = y`. -/
theorem extendScalars_map_toSpanSingleton_comp {A' B' : CommRingCat.{u}} (φ : A' ⟶ B')
    {P : ModuleCat.{u} A'} {Q : ModuleCat.{u} B'} (x : P) (y : Q)
    (e : (ModuleCat.extendScalars φ.hom).obj P ⟶ Q)
    (he : (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _ e x = y) :
    (ModuleCat.extendScalars φ.hom).map (ModuleCat.ofHom (LinearMap.toSpanSingleton A' P x)) ≫
      e = ModuleCat.scalarExtensionUnit φ ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton B' Q y) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    ModuleCat.scalarExtensionUnit, Equiv.apply_symm_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.restrictScalars.map_apply]
  rw [he]
  change y = φ.hom 1 • y
  rw [map_one, one_smul]

end ModuleCat

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct

/-!
# The degree-zero external factor is the original section action

The native H0 comparison identifies a degree-zero cup factor with the
actual multiplication endomorphism of the structure module. Its action on
higher cohomology is the original coefficient map. These equations retain
all global sections, rather than restricting to structural field constants.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X : FScheme k)

/-- The original H0 class corresponds to multiplication by its actual global section. -/
theorem structureExtLinearEquiv_symm_zero_unitMul (y : structureCohomology k X 0) :
    (structureExtLinearEquiv X 0).symm y =
      Ext.mk₀ (unitMul X.left (structureH0Equiv X y)) := by
  apply (structureExtLinearEquiv X 0).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (structureH0Equiv X).injective
  change structureH0Equiv X y =
    Sheaf.H.equiv₀ (moduleAddSheaf X.left (SheafOfModules.unit X.left.ringCatSheaf))
      isTerminalTop (moduleExtCohomologyMap X.left (SheafOfModules.unit X.left.ringCatSheaf)
        0 (Ext.mk₀ (unitMul X.left (structureH0Equiv X y))))
  rw [moduleExtCohomologyMap_mk₀_sections, unitHomGlobalSectionsEquiv_apply, unitMul_app,
    one_mul]
  change structureH0Equiv X y =
    (X.left.presheaf.map (𝟙 (op ⊤))).hom (structureH0Equiv X y)
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Original left cup by H0 is the original global-section coefficient action. -/
theorem structureCup_zero_left {n : ℕ}
    (y : structureCohomology k X 0) (x : structureCohomology k X n) :
    structureCup X (Nat.zero_add n) y x =
      Sheaf.H.map (moduleScalarOfGlobal X.left (SheafOfModules.unit X.left.ringCatSheaf)
        (structureH0Equiv X y)) n x := by
  obtain ⟨x, rfl⟩ := (structureExtLinearEquiv X n).surjective x
  rw [structureCup_apply, structureExtLinearEquiv_symm_zero_unitMul,
    LinearEquiv.symm_apply_apply]
  exact moduleExtCohomologyMap_unitMul X.left (SheafOfModules.unit X.left.ringCatSheaf)
    n (structureH0Equiv X y) x

/-- The same original section action is also right cup by H0. -/
theorem structureCup_zero_right {n : ℕ}
    (x : structureCohomology k X n) (y : structureCohomology k X 0) :
    structureCup X (Nat.add_zero n) x y =
      Sheaf.H.map (moduleScalarOfGlobal X.left (SheafOfModules.unit X.left.ringCatSheaf)
        (structureH0Equiv X y)) n x := by
  obtain ⟨x, rfl⟩ := (structureExtLinearEquiv X n).surjective x
  rw [structureCup_apply, structureExtLinearEquiv_symm_zero_unitMul,
    LinearEquiv.symm_apply_apply]
  have h := moduleExt_scalar_precomp_eq_postcomp X.left (RingHom.id Γ(X.left, ⊤))
    (SheafOfModules.unit X.left.ringCatSheaf) (SheafOfModules.unit X.left.ringCatSheaf)
    n (structureH0Equiv X y) x
  simp only [RingHom.id_apply, globalScalarEndomorphism_unit] at h
  rw [← h]
  exact moduleExtCohomologyMap_unitMul X.left (SheafOfModules.unit X.left.ringCatSheaf)
    n (structureH0Equiv X y) x

/-- The native field-linear H0 comparison retains the actual map on global sections. -/
theorem structureH0Equiv_pullback {Y : FScheme k} (f : X ⟶ Y)
    (y : structureCohomology k Y 0) :
    structureH0Equiv X (structureCohomologyPullbackLinear f 0 y) =
      f.left.appTop (structureH0Equiv Y y) :=
  structureCohomologyPullback_equiv₀ f.left y

/-- The affine-factor normalization of the original external map: its
right degree-zero factor acts by its pulled-back global section. -/
theorem structureExternalCup_zero_right (Y : FScheme k) {n : ℕ}
    (x : structureCohomology k X n) (y : structureCohomology k Y 0) :
    structureExternalCup X Y (Nat.add_zero n) x y =
      Sheaf.H.map
        (moduleScalarOfGlobal (X ⊗ Y).left (SheafOfModules.unit (X ⊗ Y).left.ringCatSheaf)
          ((snd X Y).left.appTop (structureH0Equiv Y y))) n
        (structureCohomologyPullbackLinear (fst X Y) n x) := by
  rw [structureExternalCup_apply, structureCup_zero_right, structureH0Equiv_pullback]

end AlgebraicGeometry.Scheme.Cohomology

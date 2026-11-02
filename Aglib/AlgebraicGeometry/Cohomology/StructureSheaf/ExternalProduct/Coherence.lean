/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Ext
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Naturality

/-!
# Associativity and signed symmetry of the original external product

The equations use the actual associator and swap of the selected native
relative products. Their underlying morphisms are isomorphisms, so the
proved flat pullback law applies. No diagonal or unit section is assumed flat.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y Z : FScheme k)

/-- Associativity through the original geometric product associator. -/
theorem structureExternalCup_assoc {p q r pq qr n : ℕ}
    (hpq : p + q = pq) (hqr : q + r = qr) (h : p + q + r = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q)
    (z : structureCohomology k Z r) :
    structureCohomologyPullbackLinear (α_ X Y Z).hom n
        (structureExternalCup X (Y ⊗ Z) (show p + qr = n by omega) x
          (structureExternalCup Y Z hqr y z)) =
      structureExternalCup (X ⊗ Y) Z (show pq + r = n by omega)
        (structureExternalCup X Y hpq x y) z := by
  have : IsIso (α_ X Y Z).hom.left :=
    inferInstanceAs (IsIso (((Over.forget (Spec (.of k))).mapIso (α_ X Y Z)).hom))
  have : Flat (α_ X Y Z).hom.left := inferInstance
  have : Flat (snd X (Y ⊗ Z)).left := structureProduct_snd_flat X (Y ⊗ Z)
  have : Flat ((α_ X Y Z).hom ≫ snd X (Y ⊗ Z)).left := by
    rw [Over.comp_left]
    infer_instance
  have : Flat (fst (X ⊗ Y) Z).left := structureProduct_fst_flat (X ⊗ Y) Z
  rw [structureExternalCup_pullback_of_flat, structureExternalCup_pullback_of_flat,
    structureExternalCup_apply, structureExternalCup_pullback_of_flat]
  simp only [Category.assoc, associator_hom_fst, associator_hom_snd_fst,
    associator_hom_snd_snd]
  exact (structureCup_assoc ((X ⊗ Y) ⊗ Z) hpq hqr h _ _ _).symm

/-- The original external product has the Koszul symmetry under the actual
geometric swap, including in characteristic two. -/
theorem structureExternalCup_symmetry {p q n : ℕ} (h : p + q = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y q) :
    structureExternalCup X Y h x y = ((-1 : ℤ) ^ (p * q)) •
      structureCohomologyPullbackLinear (β_ X Y).hom n
        (structureExternalCup Y X ((Nat.add_comm q p).trans h) y x) := by
  have : IsIso (β_ X Y).hom.left :=
    inferInstanceAs (IsIso (((Over.forget (Spec (.of k))).mapIso (β_ X Y)).hom))
  have : Flat (β_ X Y).hom.left := inferInstance
  rw [structureExternalCup_pullback_of_flat, braiding_hom_fst, braiding_hom_snd,
    structureExternalCup_apply]
  exact structureCup_fst_snd_comm X Y h x y

/-- Whole tensor-map version of the same original Koszul symmetry. -/
theorem structureExternalTensor_symmetry {p q n : ℕ} (h : p + q = n) :
    structureExternalTensor X Y h = ((-1 : ℤ) ^ (p * q)) •
      (structureCohomologyPullbackLinear (β_ X Y).hom n ∘ₗ
        structureExternalTensor Y X ((Nat.add_comm q p).trans h) ∘ₗ
          (TensorProduct.comm k (structureCohomology k X p)
            (structureCohomology k Y q)).toLinearMap) := by
  apply TensorProduct.ext'
  intro x y
  simpa only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.comm_tmul,
    structureExternalTensor_tmul]
    using structureExternalCup_symmetry X Y h x y

end AlgebraicGeometry.Scheme.Cohomology

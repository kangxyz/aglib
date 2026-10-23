/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.AffineMorphism
public import Aglib.RingTheory.Ideal.SquareZeroUnits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Intrinsic square-zero closed immersions and affine line-bundle lifting

The intrinsic hypothesis is the square-zero identity for the original
kernel ideal sheaf. It gives the corresponding square-zero ring kernels on
affine opens and is preserved by actual open pullback. Closed immersions
supply section surjectivity; it is not an additional lifting premise.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

private theorem square_zero_comap_of_injective {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f)
    (I : Ideal S) (hI : I ^ 2 = ⊥) : (I.comap f) ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  apply Ideal.mem_bot.mpr
  apply hf
  rw [map_mul, map_zero]
  exact I.mul_eq_zero_of_mem_of_square_zero hI hx hy

/-- The intrinsic square-zero kernel gives the original square-zero ring
kernel on every affine target open. -/
theorem ker_app_sq_of_kernel_sq {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [QuasiCompact i]
    (hi : i.ker ^ 2 = ⊥) (U : X.affineOpens) :
    RingHom.ker (i.app U).hom ^ 2 = ⊥ := by
  have hU : i.ker.ideal U ^ 2 = ⊥ := by
    change (i.ker ^ 2).ideal U = (⊥ : X.IdealSheafData).ideal U
    rw [hi]
  simpa only [Scheme.Hom.ker_apply] using hU

/-- The intrinsic square-zero kernel is preserved on the actual open
base-change square, without a flat coefficient identification. -/
theorem kernel_sq_of_open_pullback {X₀ X U₀ U : Scheme.{u}}
    (i : X₀ ⟶ X) (j : U₀ ⟶ U) (a : U₀ ⟶ X₀) (b : U ⟶ X)
    [QuasiCompact i] [IsOpenImmersion b] (H : IsPullback j a b i)
    (hi : i.ker ^ 2 = ⊥) : j.ker ^ 2 = ⊥ := by
  ext V : 2
  change j.ker.ideal V ^ 2 = ⊥
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i j a b H V]
  apply square_zero_comap_of_injective _
    (ConcreteCategory.bijective_of_isIso (b.appIso V).inv).injective
  change (i.ker ^ 2).ideal _ = (⊥ : X.IdealSheafData).ideal _
  rw [hi]

/-- Affine line bundles lift across an intrinsic square-zero closed
immersion, using its original pullback and original section map. -/
theorem exists_lineBundle_lift_affine_closed_of_square_zero
    {X₀ X : Scheme.{u}} [IsAffine X₀] [IsAffine X]
    (i : X₀ ⟶ X) [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥) (L : LineBundle X₀) :
    ∃ L' : LineBundle X, Nonempty ((pullback i).obj L'.val ≅ L.val) :=
  exists_lineBundle_lift_affine_of_square_zero i (i.app_surjective ⊤ (isAffineOpen_top X))
    (ker_app_sq_of_kernel_sq i hi ⟨⊤, isAffineOpen_top X⟩) L

/-- A specified isomorphism of affine line bundles lifts across an
intrinsic square-zero closed immersion with the exact original forward map. -/
theorem exists_lineBundle_iso_lift_affine_closed_of_square_zero
    {X₀ X : Scheme.{u}} [IsAffine X₀] [IsAffine X]
    (i : X₀ ⟶ X) [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥)
    (L M : LineBundle X)
    (e : (pullback i).obj L.val ≅ (pullback i).obj M.val) :
    ∃ e' : L.val ≅ M.val, (pullback i).map e'.hom = e.hom :=
  exists_lineBundle_iso_lift_affine_of_square_zero i
    (i.app_surjective ⊤ (isAffineOpen_top X))
    (ker_app_sq_of_kernel_sq i hi ⟨⊤, isAffineOpen_top X⟩) L M e

end AlgebraicGeometry.Scheme.Modules.Invertible

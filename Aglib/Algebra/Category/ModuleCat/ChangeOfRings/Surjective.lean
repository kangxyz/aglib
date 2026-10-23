/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Quotient.Unit
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Original scalar units for a surjective ring homomorphism

The original scalar-extension unit is the quotient by the scalar kernel.
In particular it is surjective, and scalar extension is full on morphisms
whose source is projective. No nilpotence or finiteness is required here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original scalar extension along a surjection, after scalar restriction,
is the original module quotient by the scalar kernel. -/
def extensionUnitQuotientEquiv (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) :
    (restrictScalars f).obj ((extendScalars f).obj M) ≃ₗ[R]
      M ⧸ (RingHom.ker f • (⊤ : Submodule R M)) := by
  let := f.toAlgebra
  let e : (R ⧸ RingHom.ker f) ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := f.quotientKerEquivOfSurjective hf)
      (fun r => f.quotientKerEquivOfSurjective_apply_mk hf r)
  exact TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl R M) ≪≫ₗ
    TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker f)

@[simp]
private theorem extensionUnitQuotientEquiv_one_tmul
    (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) (m : M) :
    extensionUnitQuotientEquiv f hf M ((1 : S) ⊗ₜ[R, f] m) =
      Submodule.Quotient.mk m := by
  let := f.toAlgebra
  change TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker f)
    ((TensorProduct.congr
      (AlgEquiv.ofRingEquiv (f := f.quotientKerEquivOfSurjective hf)
        (fun r => f.quotientKerEquivOfSurjective_apply_mk hf r)).symm.toLinearEquiv
      (LinearEquiv.refl R M)) ((1 : S) ⊗ₜ[R] m)) = _
  simp

/-- The quotient comparison sends the original scalar-adjunction unit to
the original quotient projection. -/
theorem extensionUnitQuotientEquiv_unit (f : R →+* S) (hf : Function.Surjective f)
    (M : ModuleCat.{u} R) (m : M) :
    extensionUnitQuotientEquiv f hf M ((extendRestrictScalarsAdj f).unit.app M m) =
      Submodule.Quotient.mk m :=
  extensionUnitQuotientEquiv_one_tmul f hf M m

/-- The kernel of the native scalar unit is exactly the original scalar
kernel acting on the original module. No flatness is assumed. -/
theorem ker_extendRestrictScalarsAdj_unit (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{u} R) :
    LinearMap.ker ((extendRestrictScalarsAdj f).unit.app M).hom =
      RingHom.ker f • (⊤ : Submodule R M) := by
  ext m
  change (extendRestrictScalarsAdj f).unit.app M m = 0 ↔ _
  rw [← (extensionUnitQuotientEquiv f hf M).map_eq_zero_iff,
    extensionUnitQuotientEquiv_unit, Submodule.Quotient.mk_eq_zero]

/-- A map between original scalar extensions lifts whenever its original
source is projective and the scalar map is surjective. -/
theorem extendScalars_map_surjective_of_projective (f : R →+* S)
    (hf : Function.Surjective f) (M N : ModuleCat.{u} R) [Module.Projective R M] :
    Function.Surjective (fun g : M ⟶ N => (extendScalars f).map g) := by
  intro g
  obtain ⟨h, hh⟩ := Module.projective_lifting_property
    ((extendRestrictScalarsAdj f).unit.app N).hom
    (((extendRestrictScalarsAdj f).homEquiv M _ g).hom)
    (extendRestrictScalarsAdj_unit_surjective f hf N)
  refine ⟨ModuleCat.ofHom h, ?_⟩
  apply ((extendRestrictScalarsAdj f).homEquiv M _).injective
  ext m
  exact LinearMap.congr_fun hh m

end ModuleCat

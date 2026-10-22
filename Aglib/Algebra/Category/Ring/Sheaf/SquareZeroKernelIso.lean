/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Sheaf.SquareZeroKernel

/-!
# The original additive and multiplicative kernel sheaves are isomorphic

The forward map is the original one-plus map. Its inverse subtracts one from
the original unit-kernel inclusion. Both comparison equations retain native
categorical kernel maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)

/-- The original unit-kernel inclusion in sectionwise kernel coordinates. -/
def unitsKernelSectionHom (U : Cᵒᵖ) :
    (kernel (unitsMap f)).obj.obj U →+
      Additive (Units.map ((f.hom.app U).hom : R.obj.obj U →* S.obj.obj U)).ker where
  toFun x := Additive.ofMul ⟨((kernel.ι (unitsMap f)).hom.app U x).toMul, by
    have h := congrArg (fun q : kernel (unitsMap f) ⟶ S.units => q.hom.app U x)
      (kernel.condition (unitsMap f))
    exact congrArg Additive.toMul h⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Additive.toMul (map_zero ((kernel.ι (unitsMap f)).hom.app U).hom)
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Additive.toMul (map_add ((kernel.ι (unitsMap f)).hom.app U).hom x y)

/-- The value of the original unit-kernel inclusion in the original ring. -/
def unitsKernelValue (U : Cᵒᵖ) (x : (kernel (unitsMap f)).obj.obj U) : R.obj.obj U :=
  (show (R.obj.obj U)ˣ from ((kernel.ι (unitsMap f)).hom.app U x).toMul).val

/-- The sectionwise subtraction-of-one map, before its naturality is bundled. -/
def unitsKernelSubOneApp
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (U : Cᵒᵖ) :
    (kernel (unitsMap f)).obj.obj U →+ R.obj.obj U :=
  (RingHom.ker (f.hom.app U).hom).subtype.toAddMonoidHom.comp
    (((f.hom.app U).hom.unitsKerSubOneHom (hf U)).comp (unitsKernelSectionHom f U))

@[simp]
theorem unitsKernelSubOneApp_apply
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥)
    (U : Cᵒᵖ) (x : (kernel (unitsMap f)).obj.obj U) :
    unitsKernelSubOneApp f hf U x =
      unitsKernelValue f U x - 1 :=
  (f.hom.app U).hom.coe_unitsKerSubOneHom (hf U) (unitsKernelSectionHom f U x)

variable [UnivLE.{max u v, w}]

/-- Subtraction of one on the original unit kernel is a morphism of sheaves. -/
def unitsKernelSubOne
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    kernel (unitsMap f) ⟶ R.additive where
  hom := {
    app U := AddCommGrpCat.ofHom (unitsKernelSubOneApp f hf U)
    naturality {U V} g := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      change unitsKernelSubOneApp f hf V ((kernel (unitsMap f)).obj.map g x) =
        (R.obj.map g).hom (unitsKernelSubOneApp f hf U x)
      rw [unitsKernelSubOneApp_apply, unitsKernelSubOneApp_apply, map_sub, map_one]
      have h := NatTrans.naturality_apply (kernel.ι (unitsMap f)).hom g x
      have h' := congrArg (fun q : R.units.obj.obj V =>
        (show R.obj.obj V from (show (R.obj.obj V)ˣ from q.toMul).val)) h
      exact congrArg (fun r : R.obj.obj V => r - 1) h' }

@[simp]
theorem unitsKernelSubOne_apply
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥)
    (U : Cᵒᵖ) (x : (kernel (unitsMap f)).obj.obj U) :
    (show R.obj.obj U from (unitsKernelSubOne f hf).hom.app U x) =
      unitsKernelValue f U x - 1 :=
  unitsKernelSubOneApp_apply f hf U x

/-- Subtraction of one lands in the original additive kernel. -/
@[reassoc (attr := simp)]
theorem unitsKernelSubOne_additiveMap
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    unitsKernelSubOne f hf ≫ additiveMap f = 0 := by
  ext U x
  change (f.hom.app U).hom (unitsKernelSubOneApp f hf U x) = 0
  exact ((f.hom.app U).hom.unitsKerSubOneHom (hf U)
    (unitsKernelSectionHom f U x)).property

/-- The inverse comparison into the native additive kernel. -/
def unitsKernelSubOneKernelMap
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    kernel (unitsMap f) ⟶ additiveKernel f :=
  kernel.lift (additiveMap f) (unitsKernelSubOne f hf)
    (unitsKernelSubOne_additiveMap f hf)

@[reassoc (attr := simp)]
theorem unitsKernelSubOneKernelMap_ι
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    unitsKernelSubOneKernelMap f hf ≫ kernel.ι (additiveMap f) =
      unitsKernelSubOne f hf := kernel.lift_ι _ _ _

/-- The actual one-plus and subtraction-of-one maps identify the original
categorical kernel sheaves. -/
def oneAddUnitsKernelIso
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    additiveKernel f ≅ kernel (unitsMap f) where
  hom := oneAddUnitsKernelMap f hf
  inv := unitsKernelSubOneKernelMap f hf
  hom_inv_id := by
    apply (cancel_mono (kernel.ι (additiveMap f))).mp
    simp only [Category.assoc, unitsKernelSubOneKernelMap_ι, Category.id_comp]
    ext U x
    change (show R.obj.obj U from (unitsKernelSubOne f hf).hom.app U
        ((oneAddUnitsKernelMap f hf).hom.app U x)) =
      (additiveKernelSectionHom f U x).val
    rw [unitsKernelSubOne_apply f hf U]
    dsimp only [unitsKernelValue]
    have h := congrArg (fun q : additiveKernel f ⟶ R.units => q.hom.app U x)
      (oneAddUnitsKernelMap_ι f hf)
    change (kernel.ι (unitsMap f)).hom.app U
        ((oneAddUnitsKernelMap f hf).hom.app U x) =
      (oneAddUnits f hf).hom.app U x at h
    rw [h, coe_oneAddUnits f hf U]
    change (1 + (additiveKernelSectionHom f U x).val) - 1 =
      (additiveKernelSectionHom f U x).val
    ring
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (unitsMap f))).mp
    simp only [Category.assoc, oneAddUnitsKernelMap_ι, Category.id_comp]
    ext U x
    change (oneAddUnits f hf).hom.app U
        ((unitsKernelSubOneKernelMap f hf).hom.app U x) =
      (kernel.ι (unitsMap f)).hom.app U x
    apply Additive.toMul.injective
    apply Units.ext
    rw [coe_oneAddUnits f hf U]
    have h := congrArg (fun q : kernel (unitsMap f) ⟶ R.additive => q.hom.app U x)
      (unitsKernelSubOneKernelMap_ι f hf)
    change (kernel.ι (additiveMap f)).hom.app U
        ((unitsKernelSubOneKernelMap f hf).hom.app U x) =
      (unitsKernelSubOne f hf).hom.app U x at h
    change 1 + (show R.obj.obj U from (kernel.ι (additiveMap f)).hom.app U
      ((unitsKernelSubOneKernelMap f hf).hom.app U x)) = _
    rw [h, unitsKernelSubOne_apply f hf U]
    dsimp only [unitsKernelValue]
    ring

end CategoryTheory.Sheaf

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Sheaf.SquareZeroUnits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# The one-plus map from the actual additive kernel sheaf

The source is the native categorical kernel of scalar forgetting applied to
the original ring-sheaf map. Its one-plus map is constructed on the original
sections, with the original kernel inclusion and quotient map retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [UnivLE.{max u v, w}]
variable {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)

/-- The original additive kernel sheaf of a ring-sheaf map. -/
abbrev additiveKernel : Sheaf J AddCommGrpCat.{w} := kernel (additiveMap f)

/-- The original kernel inclusion, valued in the actual sectionwise ring kernel. -/
def additiveKernelSectionHom (U : Cᵒᵖ) :
    (additiveKernel f).obj.obj U →+ RingHom.ker (f.hom.app U).hom where
  toFun x := ⟨(kernel.ι (additiveMap f)).hom.app U x, by
    have h := congrArg (fun q : additiveKernel f ⟶ S.additive => q.hom.app U x)
      (kernel.condition (additiveMap f))
    exact h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

/-- The actual one-plus map from the original additive kernel to ring units. -/
def oneAddUnits (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    additiveKernel f ⟶ R.units where
  hom := {
    app U := AddCommGrpCat.ofHom
      (((RingHom.ker (f.hom.app U).hom).oneAddUnitsHom (hf U)).toAdditiveRight.comp
        (additiveKernelSectionHom f U))
    naturality {U V} g := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      apply Additive.toMul.injective
      apply Units.ext
      change 1 + (additiveKernelSectionHom f V ((additiveKernel f).obj.map g x)).val =
        (R.obj.map g).hom (1 + (additiveKernelSectionHom f U x).val)
      rw [map_add, map_one]
      have h : (additiveKernelSectionHom f V ((additiveKernel f).obj.map g x)).val =
          (R.obj.map g).hom (additiveKernelSectionHom f U x).val :=
        NatTrans.naturality_apply (kernel.ι (additiveMap f)).hom g x
      exact congrArg (fun r : R.obj.obj V => 1 + r) h }

@[simp]
theorem coe_oneAddUnits (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥)
    (U : Cᵒᵖ) (x : (additiveKernel f).obj.obj U) :
    (((oneAddUnits f hf).hom.app U x).toMul : (R.obj.obj U)ˣ).val =
      1 + (additiveKernelSectionHom f U x).val := rfl

/-- The one-plus map lands in the kernel of the original map on units. -/
@[reassoc (attr := simp)]
theorem oneAddUnits_unitsMap
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    oneAddUnits f hf ≫ unitsMap f = 0 := by
  ext U x
  apply Additive.toMul.injective
  apply Units.ext
  change (f.hom.app U).hom
    (1 + (additiveKernelSectionHom f U x).val) = 1
  rw [map_add, map_one, show (f.hom.app U).hom
    (additiveKernelSectionHom f U x).val = 0 from
      (additiveKernelSectionHom f U x).property, add_zero]

/-- The canonical comparison into the actual categorical unit kernel. -/
def oneAddUnitsKernelMap
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    additiveKernel f ⟶ kernel (unitsMap f) :=
  kernel.lift (unitsMap f) (oneAddUnits f hf) (oneAddUnits_unitsMap f hf)

@[reassoc (attr := simp)]
theorem oneAddUnitsKernelMap_ι
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    oneAddUnitsKernelMap f hf ≫ kernel.ι (unitsMap f) = oneAddUnits f hf :=
  kernel.lift_ι _ _ _

end CategoryTheory.Sheaf

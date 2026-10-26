/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.PresheafSource
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Actual ring-linear internal Hom on a site

The internal Hom is the sheaf of componentwise linear additive natural transformations
on slices. Its sections are actual morphisms of the restricted module sheaves. The
construction is the presheaf-source Hom specialized to the underlying source presheaf.

For site-object, site-morphism, ring and module universes `uC`, `vC`, `uR`, `uM`,
the output carrier has universe `max uC vC uM`. No arbitrary same-universe closure
is asserted. The ring parent is the native forgetful image of the given commutative
ring sheaf, so its scalar structures agree with the original module structures.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

universe uC vC uR uM

namespace SheafOfModules.InternalHom

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR})

variable (M N : SheafOfModules.{uM} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- Additive natural transformations between the restrictions to the slice over `U`. -/
abbrev RawHom (U : C) := PresheafSource.RawHom R M.val N U

/-- The scalar action restricts the ring section and acts in the target. -/
abbrev smulRawHom (U : C) (r : R.obj.obj (op U)) (f : RawHom R M N U) :
    RawHom R M N U := PresheafSource.smulRawHom R M.val N U r f

/-- The module presheaf of additive maps on slices. -/
abbrev rawPresheaf : PresheafOfModules.{max uC vC uM}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj :=
  PresheafSource.rawPresheaf R M.val N

/-- The sheaf of additive maps on slices. -/
abbrev rawSheaf : SheafOfModules.{max uC vC uM}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  PresheafSource.rawSheaf R M.val N

/-- Componentwise linearity over the original ring on each object of the slice. -/
abbrev IsLinear (U : C) (f : RawHom R M N U) : Prop :=
  PresheafSource.IsLinear R M.val N U f

/-- The submodule of componentwise linear transformations. -/
abbrev linearSubmodule (U : C) : _root_.Submodule (R.obj.obj (op U)) (RawHom R M N U) :=
  PresheafSource.linearSubmodule R M.val N U

/-- The subpresheaf of componentwise linear transformations. -/
abbrev linearPresheaf : (rawPresheaf R M N).Submodule :=
  PresheafSource.linearPresheaf R M.val N

/-- Componentwise linearity is local for the topology. -/
theorem linearity_isLocal {U : Cᵒᵖ} (f : (rawSheaf R M N).val.obj U)
    (hf : (linearPresheaf R M N).toSubfunctor.sieveOfSection f ∈ J U.unop) :
    f ∈ (linearPresheaf R M N).obj U :=
  PresheafSource.linearity_isLocal R M.val N f hf

/-- The actual sheaf of ring-linear maps on slices, in its natural carrier universe. -/
abbrev sheaf : SheafOfModules.{max uC vC uM}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  PresheafSource.sheaf R M.val N

/-- Sections are actual morphisms of module sheaves on the slice. -/
def sectionHomEquiv (U : C) :
    (sheaf R M N).val.obj (op U) ≃ (M.over U ⟶ N.over U) where
  toFun s := ⟨PresheafOfModules.homMk s.val (by
    intro V r m
    exact s.property V r m)⟩
  invFun f := ⟨(PresheafOfModules.toPresheaf
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U).obj).map f.val, by
    intro V r m
    exact (f.val.app V).hom.map_smul r m⟩
  left_inv s := by apply Subtype.ext; rfl
  right_inv f := by ext V m; rfl

/-- The section-to-morphism comparison retains every original component. -/
theorem sectionHomEquiv_apply_app (U : C) (s : (sheaf R M N).val.obj (op U))
    (V : (Over U)ᵒᵖ) (m : M.val.obj (op V.unop.left)) :
    (sectionHomEquiv R M N U s).val.app V m = s.val.app V m := rfl

/-- The inverse comparison forgets the same actual restricted linear morphism. -/
theorem sectionHomEquiv_symm_apply_val (U : C) (f : M.over U ⟶ N.over U) :
    ((sectionHomEquiv R M N U).symm f).val =
      (PresheafOfModules.toPresheaf
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U).obj).map f.val := rfl

/-- Restriction is actual whiskering on the slice. -/
theorem sheaf_map_val {U V : Cᵒᵖ} (i : U ⟶ V) (s : (sheaf R M N).val.obj U) :
    ((sheaf R M N).val.map i s).val = Functor.whiskerLeft (Over.map i.unop).op s.val := rfl

/-- Section restriction agrees with the native restriction functor and its comparison. -/
theorem sectionHomEquiv_map {U V : Cᵒᵖ} (i : U ⟶ V)
    (s : (sheaf R M N).val.obj U) :
    sectionHomEquiv R M N V.unop ((sheaf R M N).val.map i s) =
      (SheafOfModules.overFunctorMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) i.unop).inv.app M ≫
        (SheafOfModules.overMap
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) i.unop).map
            (sectionHomEquiv R M N U.unop s) ≫
        (SheafOfModules.overFunctorMap
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) i.unop).hom.app N := by
  ext W m
  rfl

end SheafOfModules.InternalHom

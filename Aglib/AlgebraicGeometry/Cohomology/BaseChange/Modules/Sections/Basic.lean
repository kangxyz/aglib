/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Canonical scalar extension of actual module sections

The section transformation is the scalar-adjunction transpose of an actual
module coefficient arrow. Geometric pullback specializes that arrow to the
original module adjunction unit. No quasicoherence or flatness is needed for
these constructions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
  (p : Y ⟶ X) (α : A →+* Γ(X, ⊤)) (β : B →+* Γ(Y, ⊤)) (σ : A →+* B)
  (hσ : p.appTop.hom.comp α = β.comp σ)

/-- An actual coefficient arrow induces the structural-ring map on native section presheaves. -/
def moduleSectionsMapAlong {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) :
    moduleSectionsPresheaf X α M ⟶
      ((Opens.map p.base).op ⋙ moduleSectionsPresheaf Y β N) ⋙
        ModuleCat.restrictScalars σ where
  app U := ModuleCat.ofHom
    (X := (moduleSectionsPresheaf X α M).obj U)
    (Y := (ModuleCat.restrictScalars σ).obj
      (((Opens.map p.base).op ⋙ moduleSectionsPresheaf Y β N).obj U)) {
    toFun := fun x => (φ.val.app U).hom x
    map_add' := map_add _
    map_smul' := fun a x => by
      change M.val.obj U at x
      change (φ.val.app U).hom (globalRestriction X U.unop (α a) • x) =
        globalRestriction Y (p ⁻¹ᵁ U.unop) (β (σ a)) •
          (show N.val.obj (op (p ⁻¹ᵁ U.unop)) from (φ.val.app U).hom x)
      rw [(φ.val.app U).hom.map_smul]
      change p.app U.unop (globalRestriction X U.unop (α a)) •
        (show N.val.obj (op (p ⁻¹ᵁ U.unop)) from (φ.val.app U).hom x) = _
      have h := congrArg (fun q : Γ(X, ⊤) ⟶ Γ(Y, p ⁻¹ᵁ U.unop) => q.hom (α a))
        (p.naturality (homOfLE (show U.unop ≤ ⊤ from le_top)).op)
      change p.app U.unop (globalRestriction X U.unop (α a)) =
        globalRestriction Y (p ⁻¹ᵁ U.unop) (p.appTop (α a)) at h
      rw [h, show p.appTop (α a) = β (σ a) from DFunLike.congr_fun hσ a] }
  naturality U V i := by
    ext x
    exact PresheafOfModules.naturality_apply φ.val i x

/-- Canonical scalar extension of the native section map induced by an actual coefficient arrow. -/
def moduleSectionsTensorMapAlong {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) :
    moduleSectionsPresheaf X α M ⋙ ModuleCat.extendScalars σ ⟶
      (Opens.map p.base).op ⋙ moduleSectionsPresheaf Y β N :=
  (((ModuleCat.extendRestrictScalarsAdj σ).whiskerRight X.Opensᵒᵖ).homEquiv _ _).symm
    (moduleSectionsMapAlong p α β σ hσ φ)

/-- The original section tensor map is normalized by the original scalar adjunction unit. -/
theorem moduleSectionsTensorMapAlong_unit {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : X.Opensᵒᵖ) :
    (ModuleCat.extendRestrictScalarsAdj σ).unit.app
        ((moduleSectionsPresheaf X α M).obj U) ≫
      (ModuleCat.restrictScalars σ).map
        ((moduleSectionsTensorMapAlong p α β σ hσ φ).app U) =
      (moduleSectionsMapAlong p α β σ hσ φ).app U := by
  have h := Equiv.apply_symm_apply
    (((ModuleCat.extendRestrictScalarsAdj σ).whiskerRight X.Opensᵒᵖ).homEquiv _ _)
    (moduleSectionsMapAlong p α β σ hσ φ)
  rw [Adjunction.homEquiv_apply] at h
  have hu := congrArg (fun q => q.app U) h
  simpa only [moduleSectionsTensorMapAlong, NatTrans.comp_app,
    Adjunction.whiskerRight_unit_app_app, Functor.id_obj,
    Functor.whiskeringRight_obj_map, Functor.whiskeringRight_obj_obj,
    Functor.whiskerRight_app] using hu

/-- The unit pure tensor is sent by the original coefficient arrow on the actual open. -/
theorem moduleSectionsTensorMapAlong_one_tmul {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : X.Opens)
    (m : (moduleSectionsPresheaf X α M).obj (op U)) :
    (moduleSectionsTensorMapAlong p α β σ hσ φ).app (op U) ((1 : B) ⊗ₜ[A,σ] m) =
      φ.app U m := by
  exact congrArg (fun q => q m) (moduleSectionsTensorMapAlong_unit p α β σ hσ φ (op U))

/-- The actual presheaf tensor map uses the original geometric pullback unit. -/
def moduleSectionsTensorComparison (M : X.Modules) :
    moduleSectionsPresheaf X α M ⋙ ModuleCat.extendScalars σ ⟶
      (Opens.map p.base).op ⋙
        moduleSectionsPresheaf Y β ((Scheme.Modules.pullback p).obj M) :=
  moduleSectionsTensorMapAlong p α β σ hσ
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)

/-- The pullback comparison has its original geometric-unit formula on every open. -/
theorem moduleSectionsTensorComparison_one_tmul (M : X.Modules) (U : X.Opens)
    (m : (moduleSectionsPresheaf X α M).obj (op U)) :
    (moduleSectionsTensorComparison p α β σ hσ M).app (op U) ((1 : B) ⊗ₜ[A,σ] m) =
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U) m :=
  moduleSectionsTensorMapAlong_one_tmul p α β σ hσ _ U m

end AlgebraicGeometry.Scheme.Cohomology

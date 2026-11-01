/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Open
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric
public import Aglib.AlgebraicGeometry.Modules.Generators.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Original open-module Ext and geometric pullback

The original integer and module open-free generators commute with the actual
module pullback comparison. This gives the whole original open-cohomology
operator square for flat pullback, with its original coefficient map.
Generator and top-unit normalization require no flatness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u v u' v' u'' v'' u''' v''' w₁ w₂ w₃ w₄

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w₁} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w₂} D]
    {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w₃} E]
    {F : Type u'''} [Category.{v'''} F] [Abelian F] [HasExt.{w₄} F]
    (FX : C ⥤ E) [FX.Additive] [PreservesFiniteLimits FX] [PreservesFiniteColimits FX]
    (FY : D ⥤ F) [FY.Additive] [PreservesFiniteLimits FY] [PreservesFiniteColimits FY]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : E ⥤ F) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

/-- A whole original Ext-comparison square from its actual source-arrow square.
The four genuine categories retain independent Ext worlds. -/
theorem Functor.extPrecompMap_naturality_square (τ : FX ⋙ Q ⟶ P ⋙ FY)
    {UX : C} {UY : D} {IX : E} {IY : F}
    (a : IX ⟶ FX.obj UX) (b : IY ⟶ FY.obj UY)
    (α : IY ⟶ Q.obj IX) (β : UY ⟶ P.obj UX)
    (hsource : α ≫ Q.map a ≫ τ.app UX = b ≫ FY.map β) (M : C) (n : ℕ) :
    ((Ext.mk₀ (τ.app M)).postcomp IY (add_zero n)).comp
        ((Q.extPrecompMap α (FX.obj M) n).comp (FX.extPrecompMap a M n)) =
      (FY.extPrecompMap b (P.obj M) n).comp (P.extPrecompMap β M n) := by
  ext x
  let fx : Ext.{w₃} (FX.obj UX) (FX.obj M) n := x.mapExactFunctor FX
  let px : Ext.{w₂} (P.obj UX) (P.obj M) n := x.mapExactFunctor P
  have hnat :
      (fx.mapExactFunctor Q).comp (Ext.mk₀ (τ.app M)) (add_zero n) =
        (Ext.mk₀ (τ.app UX)).comp (px.mapExactFunctor FY) (zero_add n) := by
    have hh := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
    have hf : x.mapExactFunctor (FX ⋙ Q) = fx.mapExactFunctor Q :=
      Ext.comp_mapExactFunctor x FX Q
    have hp : x.mapExactFunctor (P ⋙ FY) = px.mapExactFunctor FY :=
      Ext.comp_mapExactFunctor x P FY
    rw [hf, hp] at hh
    exact hh
  change ((Ext.mk₀ α).comp
      (((Ext.mk₀ a).comp fx (zero_add n)).mapExactFunctor Q) (zero_add n)).comp
        (Ext.mk₀ (τ.app M)) (add_zero n) =
    (Ext.mk₀ b).comp
      (((Ext.mk₀ β).comp px (zero_add n)).mapExactFunctor FY) (zero_add n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]
  rw [hnat]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc,
    hsource, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry TopologicalSpace

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The original integer-generator maps, natural in the entire open variable. -/
def moduleOpenIntegerNatTrans (X : Scheme.{u}) :
    additiveOpenFreeFunctor X ⟶
      Scheme.Modules.openFreeFunctor X ⋙ SheafOfModules.toSheaf.{u} X.ringCatSheaf where
  app U := moduleOpenIntegerMap X U
  naturality {_U _V} i := moduleOpenIntegerMap_naturality X i

/-- The whole original integer/module Hom comparison retains represented sections. -/
theorem moduleOpenIntegerHomEquiv_sections (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) :
    (additiveOpenHomEquiv X U (moduleAddSheaf X M)) ∘ moduleOpenIntegerHomEquiv X U M =
      Scheme.Modules.openFreeHomEquiv X U M := by
  funext f
  exact Equiv.apply_symm_apply _ _

/-- The original integer-open and module-open generators commute with the
actual pullback comparison, before choosing any Ext degree or class. -/
theorem moduleOpenIntegerMap_pullback (U : X.Opens) :
    (additiveOpenPullbackIso p).inv.app U ≫
        (zariskiPullback p).map (moduleOpenIntegerMap X U) ≫
          (modulePullbackAdditiveComparison p).app (Scheme.Modules.openFree X U) =
      moduleOpenIntegerMap Y (p ⁻¹ᵁ U) ≫
        (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map
          (Scheme.Modules.openFreePullbackIso p U).inv := by
  apply (cancel_mono ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map
    (Scheme.Modules.openFreePullbackIso p U).hom)).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  let N : Y.Modules := Scheme.Modules.openFree Y (p ⁻¹ᵁ U)
  let f : Scheme.Modules.openFree X U ⟶ (Scheme.Modules.pushforward p).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _
      (Scheme.Modules.openFreePullbackIso p U).hom
  have hf : (modulePullbackAdditiveComparison p).app (Scheme.Modules.openFree X U) ≫
      (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map
        (Scheme.Modules.openFreePullbackIso p U).hom = moduleCoefficientPullback p f := by
    rw [modulePullbackAdditiveComparison, ← moduleCoefficientPullback_postcomp]
    dsimp only [f]
    rw [Adjunction.homEquiv_apply]
  rw [hf]
  apply (TopCat.Sheaf.openFreeAbelianHomEquiv Y.toTopCat
    (p ⁻¹ᵁ U) (moduleAddSheaf Y N)).injective
  change TopCat.Sheaf.openFreeAbelianHomEquiv Y.toTopCat (p ⁻¹ᵁ U) (moduleAddSheaf Y N)
      ((TopCat.Sheaf.openFreeAbelianPullbackObjIso p.base U).inv ≫
        (zariskiPullback p).map (moduleOpenIntegerMap X U) ≫ moduleCoefficientPullback p f) =
    additiveOpenHomEquiv Y (p ⁻¹ᵁ U) (moduleAddSheaf Y N) (moduleOpenIntegerMap Y (p ⁻¹ᵁ U))
  rw [← TopCat.Sheaf.openFreeAbelianPullbackHomEquiv_eq]
  erw [TopCat.Sheaf.openFreeAbelianPullbackHomEquiv_sections]
  erw [moduleOpenIntegerMap_sections Y (p ⁻¹ᵁ U)]
  erw [Adjunction.homEquiv_naturality_left, moduleCoefficientPullback_homEquiv p f]
  change additiveOpenHomEquiv X U
      (moduleAddSheaf X ((Scheme.Modules.pushforward p).obj N))
        (moduleOpenIntegerMap X U ≫
          (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map f) =
    Scheme.Modules.openFreeHomEquiv Y (p ⁻¹ᵁ U) N (𝟙 N)
  rw [← moduleOpenIntegerHomEquiv_apply]
  have hsections := congrFun
    (moduleOpenIntegerHomEquiv_sections X U ((Scheme.Modules.pushforward p).obj N)) f
  have hgenerator := Scheme.Modules.openFreePullbackIso_generator p U
  have hfinal := hsections.trans hgenerator
  exact hfinal

/-- The whole original source-generator square over all opens. -/
theorem moduleOpenIntegerNatTrans_pullback :
    (additiveOpenPullbackIso p).inv ≫
        Functor.whiskerRight (moduleOpenIntegerNatTrans X) (zariskiPullback p) ≫
          Functor.whiskerLeft (Scheme.Modules.openFreeFunctor X)
            (modulePullbackAdditiveComparison p) =
      Functor.whiskerLeft (Opens.map p.base) (moduleOpenIntegerNatTrans Y) ≫
        Functor.whiskerRight (Scheme.Modules.openFreePullbackNatIso p).inv
          (SheafOfModules.toSheaf.{u} Y.ringCatSheaf) := by
  apply NatTrans.ext
  funext U
  exact moduleOpenIntegerMap_pullback p U

/-- Any-p pullback of the original top universal map agrees with the original
unit-module pullback normalization. No Flat hypothesis is used. -/
theorem moduleOpenTopUnitMap_pullback :
    (Scheme.Modules.openFreePullbackIso p ⊤).hom ≫ moduleOpenTopUnitMap Y =
      (Scheme.Modules.pullback p).map (moduleOpenTopUnitMap X) ≫
        (Scheme.Modules.pullbackUnitIso p).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  apply (Scheme.Modules.openFreeHomEquiv X ⊤ _).injective
  rw [Scheme.Modules.openFreePullbackIso_homEquiv]
  rw [Adjunction.homEquiv_naturality_left, Scheme.Modules.openFreeHomEquiv_comp]
  have hu := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    p.toRingCatSheafHom
  change (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _
    (Scheme.Modules.pullbackUnitIso p).hom = _ at hu
  rw [hu]
  change (Scheme.Modules.openFreeHomEquiv Y ⊤
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
      ((Scheme.Modules.openFreeHomEquiv Y ⊤
        (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)).symm (1 : Γ(Y, ⊤))) =
    (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (op ⊤)
      ((Scheme.Modules.openFreeHomEquiv X ⊤
        (SheafOfModules.unit X.ringCatSheaf : X.Modules))
        ((Scheme.Modules.openFreeHomEquiv X ⊤
          (SheafOfModules.unit X.ringCatSheaf : X.Modules)).symm (1 : Γ(X, ⊤))))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change (1 : Γ(Y, ⊤)) = p.app ⊤ (1 : Γ(X, ⊤))
  simp only [map_one]

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry TopologicalSpace

/-- The original open-free source comparisons respect native pullback composition. -/
theorem openFreePullbackIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) :
    (pullbackComp f g).hom.app (openFree Z U) ≫ (openFreePullbackIso (f ≫ g) U).hom =
      (pullback f).map (openFreePullbackIso g U).hom ≫
        (openFreePullbackIso f (g ⁻¹ᵁ U)).hom := by
  let N : X.Modules := openFree X ((f ≫ g) ⁻¹ᵁ U)
  have hh : (pullbackComp f g).inv.app (openFree Z U) ≫
      ((pullback f).map (openFreePullbackIso g U).hom ≫
        (openFreePullbackIso f (g ⁻¹ᵁ U)).hom) =
      (openFreePullbackIso (f ≫ g) U).hom := by
    apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
    rw [homEquiv_conjugate, conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv]
    change (pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackPushforwardAdjunction f).homEquiv _ _
          ((pullback f).map (openFreePullbackIso g U).hom ≫
            (openFreePullbackIso f (g ⁻¹ᵁ U)).hom)) ≫
        (pushforwardComp f g).hom.app N =
      (pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
        (openFreePullbackIso (f ≫ g) U).hom
    rw [Adjunction.homEquiv_naturality_left]
    apply (openFreeHomEquiv Z U _).injective
    rw [openFreeHomEquiv_comp]
    change openFreeHomEquiv Z U ((pushforward g).obj ((pushforward f).obj N))
        ((pullbackPushforwardAdjunction g).homEquiv _ _
          ((openFreePullbackIso g U).hom ≫
            (pullbackPushforwardAdjunction f).homEquiv _ _
              (openFreePullbackIso f (g ⁻¹ᵁ U)).hom)) = _
    rw [openFreePullbackIso_homEquiv]
    have hf := openFreePullbackIso_generator f (g ⁻¹ᵁ U)
    have hfg := openFreePullbackIso_generator (f ≫ g) U
    exact hf.trans hfg.symm
  rw [← hh, Iso.hom_inv_id_app_assoc]

/-- The original open-free source comparison at the identity is native pullbackId. -/
theorem openFreePullbackIso_id (X : Scheme.{u}) (U : X.Opens) :
    (pullbackId X).hom.app (openFree X U) = (openFreePullbackIso (𝟙 X) U).hom := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  have hid : (pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
      ((pullbackId X).hom.app (openFree X U)) =
      (pushforwardId X).inv.app (openFree X U) := by
    calc
      _ = (conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 X))
          (pullbackId X).hom).app (openFree X U) := homEquiv_to_identity _ _ _
      _ = _ := congrArg (fun η => η.app (openFree X U))
        (conjugateEquiv_pullbackId_hom X)
  rw [hid]
  apply (openFreeHomEquiv X U _).injective
  have he := openFreeHomEquiv_comp X U (𝟙 (openFree X U))
    ((pushforwardId X).inv.app (openFree X U))
  simp only [Category.id_comp] at he
  rw [he, pushforwardId_inv_app_app]
  have h := openFreePullbackIso_homEquiv (𝟙 X) U (openFree X U) (𝟙 _)
  simp only [Category.comp_id] at h
  exact h.symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry TopologicalSpace

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

variable [Flat p]

/-- The whole original native open-cohomology operator is exact module
pullback on Ext followed by the original inverse open-free comparison. -/
theorem moduleOpenExtCohomologyMap_pullback_hom (U : X.Opens) (M : X.Modules) (n : ℕ) :
    (((zariskiCohomologyOpenMap p (moduleAddSheaf X M)
        (moduleAddSheaf Y ((Scheme.Modules.pullback p).obj M))
          ((modulePullbackAdditiveComparison p).app M) n).app (op U)).hom).comp
        (moduleOpenExtCohomologyMap X U M n) =
      (moduleOpenExtCohomologyMap Y (p ⁻¹ᵁ U) ((Scheme.Modules.pullback p).obj M) n).comp
        ((Scheme.Modules.pullback p).extPrecompMap
          (Scheme.Modules.openFreePullbackIso p U).inv M n) := by
  let FX : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : FX.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits FX :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let : PreservesFiniteColimits FX :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  let FY : Y.Modules ⥤ Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} Y.ringCatSheaf
  let : FY.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteLimits FY :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} Y.ringCatSheaf))
  let : PreservesFiniteColimits FY :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} Y.ringCatSheaf))
  let P : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback p
  let : P.Additive := inferInstanceAs ((Scheme.Modules.pullback p).Additive)
  let : PreservesFiniteLimits P :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pullback p))
  let : PreservesFiniteColimits P :=
    inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.pullback p))
  let Q := zariskiPullback p
  let τ : FX ⋙ Q ⟶ P ⋙ FY := modulePullbackAdditiveComparison p
  have hh := Functor.extPrecompMap_naturality_square FX FY P Q τ
    (moduleOpenIntegerMap X U) (moduleOpenIntegerMap Y (p ⁻¹ᵁ U))
    ((additiveOpenPullbackIso p).inv.app U)
    (Scheme.Modules.openFreePullbackIso p U).inv
    (moduleOpenIntegerMap_pullback p U) M n
  exact hh

/-- Evaluation of the already proved whole operator square is the literal
original H' geometric pullback formula, for arbitrary modules on schemes. -/
theorem moduleOpenExtCohomologyMap_pullback (U : X.Opens) (M : X.Modules) (n : ℕ)
    (x : Ext.{u + 1} (Scheme.Modules.openFree X U) M n) :
    (zariskiCohomologyOpenMap p (moduleAddSheaf X M)
        (moduleAddSheaf Y ((Scheme.Modules.pullback p).obj M))
          ((modulePullbackAdditiveComparison p).app M) n).app (op U)
        (moduleOpenExtCohomologyMap X U M n x) =
      moduleOpenExtCohomologyMap Y (p ⁻¹ᵁ U) ((Scheme.Modules.pullback p).obj M) n
        ((Ext.mk₀ (Scheme.Modules.openFreePullbackIso p U).inv).comp
          (x.mapExactFunctor (Scheme.Modules.pullback p)) (zero_add n)) :=
  DFunLike.congr_fun (moduleOpenExtCohomologyMap_pullback_hom p U M n) x

end AlgebraicGeometry.Scheme.Cohomology

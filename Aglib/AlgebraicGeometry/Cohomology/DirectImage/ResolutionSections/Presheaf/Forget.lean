/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Aglib.Algebra.Category.ModuleCat.Presheaf.ForgetToModuleCat
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Homology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Additive

/-!
# Actual variable-ring presheaf homology and structural-ring sections

The original initial-ring functor and native scalar restriction give an exact
functor on module presheaves. The sole structural-ring section functor is its
composition with the original sheaf-forgetting functor. Their native complex
and homology comparisons retain those exact functors.

For any actual module complex, the original presheaf-homology reflection unit
therefore gives a linear map from homology of actual sections to sections of
the actual homology sheaf. Sheaf forgetting is not assumed to preserve homology.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u w

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

/-- The original sheaf-forgetting functor with its actual scheme-module source pinned. -/
abbrev moduleUnderlyingPresheafFunctor :
    X.Modules ⥤ _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  SheafOfModules.forget.{u} X.ringCatSheaf

instance moduleUnderlyingPresheafFunctor_additive :
    (moduleUnderlyingPresheafFunctor X).Additive where
  map_add := by intros; rfl

/-- The exact original structural-ring conversion on actual variable-ring module presheaves. -/
abbrev modulePresheafSectionsFunctorOfHom :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  PresheafOfModules.forgetToPresheafModuleCat.{u} (R := X.ringCatSheaf.obj) (op ⊤)
      (isTerminalTop (α := X.Opens)).op ⋙
    (Functor.whiskeringRight X.Opensᵒᵖ (ModuleCat.{u} Γ(X, ⊤)) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars α)

instance modulePresheafSectionsFunctorOfHom_additive :
    (modulePresheafSectionsFunctorOfHom X α).Additive := by infer_instance

instance modulePresheafSectionsFunctorOfHom_preservesFiniteLimits :
    PreservesFiniteLimits (modulePresheafSectionsFunctorOfHom X α) := by
  let G := (Functor.whiskeringRight X.Opensᵒᵖ
    (ModuleCat.{u} Γ(X, ⊤)) (ModuleCat.{u} R)).obj (ModuleCat.restrictScalars α)
  let : PreservesFiniteLimits G := ⟨fun _ ↦ inferInstance⟩
  exact comp_preservesFiniteLimits
    (PresheafOfModules.forgetToPresheafModuleCat.{u} (R := X.ringCatSheaf.obj) (op ⊤)
      (isTerminalTop (α := X.Opens)).op) G

instance modulePresheafSectionsFunctorOfHom_preservesFiniteColimits :
    PreservesFiniteColimits (modulePresheafSectionsFunctorOfHom X α) := by
  let G := (Functor.whiskeringRight X.Opensᵒᵖ
    (ModuleCat.{u} Γ(X, ⊤)) (ModuleCat.{u} R)).obj (ModuleCat.restrictScalars α)
  let : PreservesFiniteColimits G := ⟨fun _ ↦ inferInstance⟩
  exact comp_preservesFiniteColimits
    (PresheafOfModules.forgetToPresheafModuleCat.{u} (R := X.ringCatSheaf.obj) (op ⊤)
      (isTerminalTop (α := X.Opens)).op) G

instance modulePresheafSectionsFunctorOfHom_preservesHomology :
    (modulePresheafSectionsFunctorOfHom X α).PreservesHomology := by infer_instance

/-- The sole original structural-ring section functor is actual sheaf forgetting followed by
the exact original module-presheaf conversion. -/
def moduleSectionsPresheafFunctorIsoForget :
    moduleSectionsPresheafFunctor X α ≅
      moduleUnderlyingPresheafFunctor X ⋙ modulePresheafSectionsFunctorOfHom X α :=
  Iso.refl _

variable {ι : Type w} {d : ComplexShape ι} (K : HomologicalComplex X.Modules d)

/-- The original termwise structural sections are the exact conversion of the original
underlying variable-ring module-presheaf complex. -/
def moduleComplexPresheafSectionsIso :
    ((modulePresheafSectionsFunctorOfHom X α).mapHomologicalComplex d).obj
        (((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).obj K) ≅
      ((moduleSectionsPresheafFunctor X α).mapHomologicalComplex d).obj K :=
  (Functor.mapHomologicalComplexCompIso (moduleSectionsPresheafFunctorIsoForget X α).symm d).app K

theorem moduleComplexPresheafSectionsIso_hom_f_app_apply (n : ι) (U : X.Opensᵒᵖ)
    (x : ((((modulePresheafSectionsFunctorOfHom X α).mapHomologicalComplex d).obj
      (((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).obj K)).X n).obj U) :
    ((moduleComplexPresheafSectionsIso X α K).hom.f n).app U x = x := rfl

/-- Exact native conversion identifies actual variable-ring presheaf homology with native
homology of the actual structural-ring sections. -/
def moduleComplexPresheafSectionsHomologyIso (n : ι) :
    (modulePresheafSectionsFunctorOfHom X α).obj
        ((((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).obj K).homology n) ≅
      (((moduleSectionsPresheafFunctor X α).mapHomologicalComplex d).obj K).homology n :=
  (ShortComplex.mapHomologyIso
    ((((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).obj K).sc n)
      (modulePresheafSectionsFunctorOfHom X α)).symm ≪≫
      (homologyFunctor (X.Opensᵒᵖ ⥤ ModuleCat.{u} R) d n).mapIso
        (moduleComplexPresheafSectionsIso X α K)

/-- Original reflection of native presheaf homology gives the canonical linear arrow from
homology of sections to the actual sections of the original homology sheaf. -/
def moduleComplexSectionsHomologyUnit (n : ι) :
    (((moduleSectionsPresheafFunctor X α).mapHomologicalComplex d).obj K).homology n ⟶
      moduleSectionsPresheaf X α (K.homology n) :=
  (moduleComplexPresheafSectionsHomologyIso X α K n).inv ≫
    (modulePresheafSectionsFunctorOfHom X α).map
      (SheafOfModules.homologyPresheafUnit X.ringCatSheaf K n) ≫
    (moduleSectionsPresheafFunctorIsoForget X α).inv.app (K.homology n)

theorem moduleComplexSectionsHomologyUnit_eq (n : ι) :
    moduleComplexSectionsHomologyUnit X α K n =
      (moduleComplexPresheafSectionsHomologyIso X α K n).inv ≫
        (modulePresheafSectionsFunctorOfHom X α).map
          (SheafOfModules.homologyPresheafUnit X.ringCatSheaf K n) ≫
        (moduleSectionsPresheafFunctorIsoForget X α).inv.app (K.homology n) := rfl

/-- The native homology comparison is natural for every actual module chain map. -/
@[reassoc]
theorem moduleComplexPresheafSectionsHomologyIso_hom_naturality
    {K L : HomologicalComplex X.Modules d} (φ : K ⟶ L) (n : ι) :
    (modulePresheafSectionsFunctorOfHom X α).map
        (homologyMap (((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).map φ) n) ≫
        (moduleComplexPresheafSectionsHomologyIso X α L n).hom =
      (moduleComplexPresheafSectionsHomologyIso X α K n).hom ≫
        homologyMap (((moduleSectionsPresheafFunctor X α).mapHomologicalComplex d).map φ) n := by
  have he := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor _ d n).map
      (((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).map φ))
    (modulePresheafSectionsFunctorOfHom X α)
  change (modulePresheafSectionsFunctorOfHom X α).map
      (homologyMap (((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).map φ) n) ≫
      (((((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).obj L).sc n).mapHomologyIso
        (modulePresheafSectionsFunctorOfHom X α)).inv =
    (((((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).obj K).sc n).mapHomologyIso
        (modulePresheafSectionsFunctorOfHom X α)).inv ≫
      homologyMap (((modulePresheafSectionsFunctorOfHom X α).mapHomologicalComplex d).map
        (((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).map φ)) n at he
  have hc := (Functor.mapHomologicalComplexCompIso
    (moduleSectionsPresheafFunctorIsoForget X α).symm d).hom.naturality φ
  have hh := congrArg ((homologyFunctor _ d n).map) hc
  simp only [Functor.map_comp] at hh
  change homologyMap (((modulePresheafSectionsFunctorOfHom X α).mapHomologicalComplex d).map
      (((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).map φ)) n ≫
      homologyMap (moduleComplexPresheafSectionsIso X α L).hom n =
    homologyMap (moduleComplexPresheafSectionsIso X α K).hom n ≫
      homologyMap (((moduleSectionsPresheafFunctor X α).mapHomologicalComplex d).map φ) n at hh
  dsimp only [moduleComplexPresheafSectionsHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, he, Category.assoc]
  exact (congrArg
    ((((((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).obj K).sc n).mapHomologyIso
        (modulePresheafSectionsFunctorOfHom X α)).inv ≫ ·) hh).trans
    (Category.assoc _ _ _).symm

/-- The canonical arrow to sections of actual sheaf homology preserves original chain maps. -/
@[reassoc]
theorem moduleComplexSectionsHomologyUnit_naturality
    {K L : HomologicalComplex X.Modules d} (φ : K ⟶ L) (n : ι) :
    homologyMap (((moduleSectionsPresheafFunctor X α).mapHomologicalComplex d).map φ) n ≫
        moduleComplexSectionsHomologyUnit X α L n =
      moduleComplexSectionsHomologyUnit X α K n ≫
        (moduleSectionsPresheafFunctor X α).map (homologyMap φ n) := by
  apply (cancel_epi (moduleComplexPresheafSectionsHomologyIso X α K n).hom).mp
  rw [← moduleComplexPresheafSectionsHomologyIso_hom_naturality_assoc X α φ n]
  simp only [moduleComplexSectionsHomologyUnit, Category.assoc, Iso.hom_inv_id_assoc]
  change (modulePresheafSectionsFunctorOfHom X α).map
      (homologyMap (((moduleUnderlyingPresheafFunctor X).mapHomologicalComplex d).map φ) n) ≫
      (modulePresheafSectionsFunctorOfHom X α).map
        (SheafOfModules.homologyPresheafUnit X.ringCatSheaf L n) ≫
      (moduleSectionsPresheafFunctorIsoForget X α).inv.app (L.homology n) = _
  rw [← Functor.map_comp_assoc, SheafOfModules.homologyPresheafUnit_naturality,
    Functor.map_comp, Category.assoc]
  exact congrArg ((modulePresheafSectionsFunctorOfHom X α).map
      (SheafOfModules.homologyPresheafUnit X.ringCatSheaf K n) ≫ ·)
    ((moduleSectionsPresheafFunctorIsoForget X α).inv.naturality (homologyMap φ n))

end AlgebraicGeometry.Scheme.Cohomology

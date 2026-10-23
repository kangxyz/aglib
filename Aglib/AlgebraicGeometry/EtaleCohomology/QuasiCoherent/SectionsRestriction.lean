/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.SectionsNaturality

/-! # Original pullback coherence in section restrictions -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite Bicategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- Forgetting the full-subcategory wrapper retains the original pseudofunctor restriction. -/
theorem homPresheaf_map_hom {T U : Over X} (f : U ⟶ T)
    (h : (homPresheaf X F).obj (op T)) :
    ((homPresheaf X F).map f.op h).hom =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor) h.hom f.left U.hom U.hom := rfl

/-- Native restriction coherence, proved before instantiating full-subcategory objects. -/
theorem nativePullHom_eq {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (c : Z ⟶ X) (w : b ≫ a = c) (M N : X.Modules)
    (φ : (pullback a).obj M ⟶ (pullback a).obj N) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := pullbackPseudofunctor) φ b c c w w =
      (pullbackCongr w.symm).hom.app M ≫ (pullbackComp b a).inv.app M ≫
        (pullback b).map φ ≫ (pullbackComp b a).hom.app N ≫
          (pullbackCongr w).hom.app N := by
  have h₁ := pullbackPseudofunctor_mapComp'_hom_app a b c w M
  have h₂ := pullbackPseudofunctor_mapComp'_inv_app a b c w N
  refine (congrArg₂ (fun p q => p ≫ (pullback b).map φ ≫ q) h₁ h₂).trans ?_
  simp only [Category.assoc]

/-- The section restriction uses the literal pullback, composition, and equality maps. -/
theorem homPresheaf_map_hom_eq {T U : Over X} (f : U ⟶ T)
    (h : (homPresheaf X F).obj (op T)) :
    ((homPresheaf X F).map f.op h).hom =
      (pullbackCongr (Over.w f).symm).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (pullbackComp f.left T.hom).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (pullback f.left).map h.hom ≫
        (pullbackComp f.left T.hom).hom.app F ≫
        (pullbackCongr (Over.w f)).hom.app F := by
  exact (homPresheaf_map_hom X F f h).trans
    (nativePullHom_eq T.hom f.left U.hom (Over.w f)
      (SheafOfModules.unit X.ringCatSheaf) F h.hom)

/-- The inverse unit comparison also retains the original equality transport. -/
theorem pullbackUnitIso_inv_congr {U V : Scheme.{u}} {f g : U ⟶ V} (h : f = g) :
    (pullbackUnitIso f).inv ≫
        (pullbackCongr h).hom.app (SheafOfModules.unit V.ringCatSheaf) =
      (pullbackUnitIso g).inv := by
  subst g
  simp [pullbackCongr]

/-- The native section restriction, including the original over-map coherence. -/
theorem sectionsEquiv_map {T U : Over X} (f : U ⟶ T)
    (h : (homPresheaf X F).obj (op T)) :
    sectionsEquiv X F U ((homPresheaf X F).map f.op h) =
      Scheme.Modules.Hom.app
        ((pullbackComp f.left T.hom).hom.app F ≫
          (pullbackCongr (Over.w f)).hom.app F) ⊤
        (nativeSectionPullback f.left ((pullback T.hom).obj F)
          (sectionsEquiv X F T h)) := by
  rw [sectionsEquiv_apply, homPresheaf_map_hom_eq]
  simp only [nativeSectionPullback, sectionsEquiv_apply, Equiv.symm_apply_apply,
    Functor.map_comp]
  refine Eq.trans ?_ (unitHomGlobalSectionsEquiv_naturality U.left
    ((pullbackUnitIso f.left).inv ≫
      (pullback f.left).map (pullbackUnitIso T.hom).inv ≫ (pullback f.left).map h.hom)
    ((pullbackComp f.left T.hom).hom.app F ≫ (pullbackCongr (Over.w f)).hom.app F))
  apply congrArg (unitHomGlobalSectionsEquiv U.left ((pullback U.hom).obj F))
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    pullbackUnitIso_inv_congr, pullbackUnitIso_inv_comp]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

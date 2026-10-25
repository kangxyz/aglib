/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeHorizontalUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback

/-! # Original exchange and actual global-section pullback

The horizontal adjunction-unit equation and native direct-image composition
identify the ordinary exchange on global sections. This equality is then
available termwise on actual resolution complexes; it is not an assumption
about higher cohomology or a degree-zero uniqueness certificate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

private theorem map_path_iso_paste {C D : Type*} [Category* C] [Category* D]
    (E : C ⥤ D) {T : Type*} (P : T → C) (Z : D)
    (e : ∀ t, E.obj (P t) ⟶ Z) (k l : T) (h : k = l)
    {A B : C} (a : A ≅ P k) (b : B ≅ P l) (δ : A ≅ B)
    (hδ : δ = a ≪≫ eqToIso (congrArg P h) ≪≫ b.symm) :
    E.map δ.hom ≫ E.map b.hom ≫ e l =
      E.map a.hom ≫ e k := by
  subst δ
  subst l
  simp only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Iso.symm_hom,
    Category.id_comp, E.map_comp, Category.assoc]
  have hc : E.map b.inv ≫ E.map b.hom = 𝟙 _ := by
    rw [← E.map_comp, Iso.inv_hom_id, E.map_id]
  rw [reassoc_of% hc]

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem directImageGlobalSectionsIso_comp_app {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (F : AbelianSheaf.{u, u + 1} T) :
    (directImageGlobalSectionsIso f).hom.app ((directImage g).obj F) ≫
        (directImageGlobalSectionsIso g).hom.app F =
      (globalSections X).map ((directImageCompIso f g).hom.app F) ≫
        (directImageGlobalSectionsIso (g ≫ f)).hom.app F := by
  have h := congrArg (fun e => e.hom.app F) (directImageGlobalSectionsIso_comp f g)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] using h

variable {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
  (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)

/-- The original direct-image square preserves the fixed-terminal section comparisons. -/
theorem directImageSquareIso_globalSections (F : AbelianSheaf.{u, u + 1} X') :
    (globalSections S).map ((directImageSquareIso f f' g g' h).hom.app F) ≫
        (directImageGlobalSectionsIso g).hom.app ((directImage f').obj F) ≫
        (directImageGlobalSectionsIso f').hom.app F =
      (directImageGlobalSectionsIso f).hom.app ((directImage g').obj F) ≫
        (directImageGlobalSectionsIso g').hom.app F := by
  rw [directImageGlobalSectionsIso_comp_app g f',
    directImageGlobalSectionsIso_comp_app f g']
  exact map_path_iso_paste
    ((CategoryTheory.evaluation (AbelianSheaf.{u, u + 1} X')
      (AbelianSheaf.{u, u + 1} S)).obj F ⋙ globalSections S)
    (fun k : X' ⟶ S => directImage k) ((globalSections X').obj F)
    (fun k => (directImageGlobalSectionsIso k).hom.app F)
    (g' ≫ f) (f' ≫ g) h.symm (directImageCompIso f g') (directImageCompIso g f')
    (directImageSquareIso f f' g g' h) rfl

/-- Ordinary exchange followed by target terminal transport is exactly the
original pullback of sections on the total spaces. -/
theorem baseChangeMap_globalSections (F : AbelianSheaf.{u, u + 1} X) :
    globalSectionsPullback g ((directImage f).obj F) ≫
        (globalSections S').map ((baseChangeMap f f' g g' h).app F) ≫
        (directImageGlobalSectionsIso f').hom.app ((inverseImage g').obj F) =
      (directImageGlobalSectionsIso f).hom.app F ≫ globalSectionsPullback g' F := by
  have hn := (directImageGlobalSectionsIso g).hom.naturality
    ((baseChangeMap f f' g g' h).app F)
  simp only [Functor.comp_map] at hn
  have hu := congrArg (globalSections S).map
    (baseChangeMap_horizontal_unit f f' g g' h F)
  simp only [Functor.map_comp] at hu
  dsimp only [globalSectionsPullback]
  rw [Category.assoc, ← reassoc_of% hn, ← reassoc_of% hu,
    directImageSquareIso_globalSections f f' g g' h]
  have hf := (directImageGlobalSectionsIso f).hom.naturality
    ((inverseImageAdjunction g').unit.app F)
  simp only [Functor.comp_map] at hf
  rw [reassoc_of% hf]

end AlgebraicGeometry.Scheme.EtaleCohomology

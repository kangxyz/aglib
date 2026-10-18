/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GoodDiagram
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.DirectedSectionGluing

/-!
# GluedUniversalSection

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (toEtale)
namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation
universe u
variable {X : Scheme.{u}} {F : Scheme.EtaleH1.SetSheaf X} (t :
  Scheme.EtaleH1.FiniteSetLocalTrivialization F)

/-- The étale-site isomorphism from a chart of the glued cover to its selected local
representative. -/
def localSiteIso (U : GoodOpen (F := F)) :
    DirectedSectionGluing.site (cover t).obj.hom (datum t).cover U ≅ (representative U).site :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ ((representative U).cover.obj.hom ≫ U.1.ι) =
      colimit.ι (datum t).functor U ≫ (cover t).obj.hom
    rw [Category.id_comp]
    exact ((datum t).ι_toBase U).symm)

/-- The section on a chart of the glued cover transported from the selected representative
section. -/
def localSection (U : GoodOpen (F := F)) :
    F.obj.obj (op (DirectedSectionGluing.site (cover t).obj.hom (datum t).cover U)) :=
  F.obj.map (localSiteIso t U).hom.op (representative U).section_

lemma localSection_compatible {U V : GoodOpen (F := F)} (h : U ⟶ V) :
    F.obj.map (DirectedSectionGluing.trans (cover t).obj.hom (datum t).cover h).op
      (localSection t V) = localSection t U := by
  have hh : DirectedSectionGluing.trans (cover t).obj.hom (datum t).cover h ≫
      (localSiteIso t V).hom = (localSiteIso t U).hom ≫
        (representative U).transition (representative V) (leOfHom h) := by
    apply MorphismProperty.Over.Hom.ext
    change (datum t).functor.map h ≫ 𝟙 _ = 𝟙 _ ≫
      ((representative U).transition (representative V) (leOfHom h)).left
    simp only [Category.comp_id, Category.id_comp]
    rfl
  change F.obj.map _ (F.obj.map _ _) = F.obj.map _ _
  rw [← Functor.map_comp_apply, ← op_comp, hh]
  simp [op_comp, Functor.map_comp]

/-- Glue the actual local universal sections of the original sheaf. -/
def universalSection : F.obj.obj (op ((toEtale X).obj (cover t))) :=
  Classical.choose (DirectedSectionGluing.existsUnique_glue
    (cover t).obj.hom (datum t).cover F (localSection t) (localSection_compatible t))

@[simp] lemma universalSection_restrict (U : GoodOpen (F := F)) :
    F.obj.map (inclusion t U).op (universalSection t) = (representative U).section_ := by
  have hh : (localSiteIso t U).hom ≫ inclusion t U =
      DirectedSectionGluing.inclusion (cover t).obj.hom (datum t).cover U := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 _ ≫ colimit.ι (datum t).functor U = colimit.ι (datum t).functor U
    exact Category.id_comp _
  apply ((CategoryTheory.isIso_iff_bijective (F.obj.map (localSiteIso t U).hom.op)).1
    inferInstance).1
  rw [← Functor.map_comp_apply, ← op_comp, hh]
  exact (Classical.choose_spec (DirectedSectionGluing.existsUnique_glue
    (cover t).obj.hom (datum t).cover F (localSection t) (localSection_compatible t))).1 U

/-- The universal section produces a map from the represented sheaf to the original one. -/
def representingMap : Scheme.EtaleH1.finiteRepresentedSetSheaf (cover t) ⟶ F :=
  finiteRepresentedSectionMap (cover t) (universalSection t)

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 2b19cec64f50d726994ef1e5762afe0d212e2aba2c0a0531e68833e78d0652a3.
Definitions, hypotheses and universes are retained modulo native names. -/

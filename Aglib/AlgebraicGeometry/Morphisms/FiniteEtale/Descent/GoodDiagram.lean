/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GoodOpenCover
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.OpenTransitions

/-!
# GoodDiagram

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

/-- The diagram of finite etale representatives over good opens, with their transition
morphisms. -/
def diagram : (goodOpenCover t).I₀ ⥤ Scheme.{u} where
  obj U := (representative U).cover.obj.left
  map {U V} h := ((representative U).transition (representative V) (leOfHom h)).left
  map_id U := by
    exact congrArg (fun f => f.left) ((representative U).transition_id)
  map_comp {U V W} f g := by
    exact (congrArg (fun f => f.left)
      ((representative U).transition_comp (representative V) (representative W)
        (leOfHom f) (leOfHom g))).symm

/-- The natural structural maps from the representative schemes to the good-open diagram. -/
def diagramToBase : diagram t ⟶ (goodOpenCover t).functorOfLocallyDirected where
  app U := by
    change (representative U).cover.obj.left ⟶ U.1.toScheme
    exact (representative U).cover.obj.hom
  naturality U V h := by
    exact (representative U).transition_w (representative V) (leOfHom h)

/-- All gluing data, including the pullback squares, are produced from the given sheaf. -/
def datum : Scheme.Cover.RelativeGluingData (goodOpenCover t) where
  functor := diagram t
  natTrans := diagramToBase t
  equifibered {U V} h := by
    exact (representative U).transition_isPullback (representative V) (leOfHom h)

instance (U : (goodOpenCover t).I₀) : IsFinite ((datum t).natTrans.app U) :=
  inferInstanceAs (IsFinite (representative U).cover.obj.hom)

instance (U : (goodOpenCover t).I₀) : Etale ((datum t).natTrans.app U) :=
  inferInstanceAs (Etale (representative U).cover.obj.hom)

/-- The actual globally glued finite etale scheme. -/
def cover : Scheme.FiniteEtale X :=
  Scheme.FiniteEtale.RelativeGluing.gluedCover.{u, u, u}
    (X := X) (𝒰 := goodOpenCover t) (datum t)

/-- The canonical gluing inclusion of a good-open representative into the resulting finite etale
cover. -/
def inclusion (U : GoodOpen (F := F)) :
    (representative U).site ⟶ (toEtale X).obj (cover t) :=
  MorphismProperty.Over.homMk (colimit.ι (datum t).functor U) (by
    exact (datum t).ι_toBase U) (by trivial)

-- Keep the original indexed transition/inclusion simp rule for explicit categorical rewriting.
@[simp, nolint simpNF] lemma transition_inclusion {U V : GoodOpen (F := F)} (h : U ⟶ V) :
    (representative U).transition (representative V) (leOfHom h) ≫ inclusion t V =
      inclusion t U := by
  apply MorphismProperty.Over.Hom.ext
  exact colimit.w (datum t).functor h

lemma inclusion_isPullback (U : GoodOpen (F := F)) :
    IsPullback (representative U).cover.obj.hom (inclusion t U).left U.1.ι (cover t).obj.hom :=
  (datum t).isPullback_natTrans_ι_toBase U

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 898ad175ba8d306e11c6f0c583786f2f9b0b4b0e833bbe80e100843c2f7ae759.
Definitions, hypotheses and universes are retained modulo native names. -/

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramRelativeTail
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-! # The actual base-change diagram of a fixed stage test object

The original relative tail is base-changed by the native `Over.pullback`.
This is the under-indexed form of `Scheme.baseChangeDiagram`, with the same
pullback orientation used by the relative-chart geometric producers. Native
pullback symmetry identifies its stage charts with `siteBaseChange` objects.
All projection equations are retained. No coefficient continuity is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (i : I) (T : (X.obj i).unop.Etale)

/-- The original tail of schemes, without changing its under-category index. -/
abbrev diagramSchemeTail : Under i ⥤ Scheme.{u}ᵒᵖ := Under.forget i ⋙ X

/-- Native base change of the original relative tail to the specified test object. -/
def diagramEtaleTest : Under i ⥤ Scheme.{u}ᵒᵖ :=
  relativeSchemeTail X i ⋙ (Over.pullback T.hom ⋙ Over.forget T.left).op

/-- The native test chart at a later stage, in the geometric producer's orientation. -/
def diagramEtaleTestChart (a : Under i) : (X.obj a.right).unop.Etale :=
  Scheme.Etale.mk (pullback.fst (X.map a.hom).unop T.hom)

/-- The same chart is the original site base change, by native pullback symmetry. -/
def diagramEtaleTestChartIso (a : Under i) :
    diagramEtaleTestChart X i T a ≅ (siteBaseChange (X.map a.hom).unop).obj T :=
  MorphismProperty.Over.isoMk (pullbackSymmetry (X.map a.hom).unop T.hom)
    (pullbackSymmetry_hom_comp_snd _ _)

/-- Projection from each actual test scheme to its original coefficient scheme. -/
def diagramEtaleTestProjection : diagramSchemeTail X i ⟶ diagramEtaleTest X i T where
  app a := (pullback.fst (X.map a.hom).unop T.hom).op
  naturality {a b} m := by
    apply Quiver.Hom.unop_inj
    change pullback.fst (X.map b.hom).unop T.hom ≫ (X.map m.right).unop =
      pullback.lift (pullback.fst (X.map b.hom).unop T.hom ≫ (X.map m.right).unop)
        (pullback.snd (X.map b.hom).unop T.hom) _ ≫
          pullback.fst (X.map a.hom).unop T.hom
    exact (pullback.lift_fst _ _ _).symm

/-- The structural map of a test transition is its original pullback projection. -/
@[reassoc]
theorem diagramEtaleTest_map_fst {a b : Under i} (m : a ⟶ b) :
    ((diagramEtaleTest X i T).map m).unop ≫
        pullback.fst (X.map a.hom).unop T.hom =
      pullback.fst (X.map b.hom).unop T.hom ≫ (X.map m.right).unop :=
  pullback.lift_fst _ _ _

/-- A test transition retains its original chart coordinate. -/
@[reassoc]
theorem diagramEtaleTest_map_snd {a b : Under i} (m : a ⟶ b) :
    ((diagramEtaleTest X i T).map m).unop ≫
        pullback.snd (X.map a.hom).unop T.hom =
      pullback.snd (X.map b.hom).unop T.hom :=
  pullback.lift_snd _ _ _

variable (c : Cocone X)

/-- The actual test cocone is the native pullback of the original relative tail cocone. -/
def diagramEtaleTestCocone : Cocone (diagramEtaleTest X i T) :=
  (Over.pullback T.hom ⋙ Over.forget T.left).op.mapCocone
    (relativeSchemeTailCocone X c i)

/-- The actual limit test scheme projects to the original limit scheme. -/
def diagramEtaleTestLimitProjection : c.pt ⟶ (diagramEtaleTestCocone X i T c).pt :=
  (pullback.fst (c.ι.app i).unop T.hom).op

/-- The actual diagram map and the two original cocones commute. -/
theorem diagramEtaleTestProjection_cocone (a : Under i) :
    (diagramEtaleTestProjection X i T).app a ≫
        (diagramEtaleTestCocone X i T c).ι.app a =
      c.ι.app a.right ≫ diagramEtaleTestLimitProjection X i T c := by
  apply Quiver.Hom.unop_inj
  change pullback.lift (pullback.fst (c.ι.app i).unop T.hom ≫
      (c.ι.app a.right).unop) (pullback.snd (c.ι.app i).unop T.hom) _ ≫
        pullback.fst (X.map a.hom).unop T.hom =
    pullback.fst (c.ι.app i).unop T.hom ≫ (c.ι.app a.right).unop
  exact pullback.lift_fst _ _ _

/-- The actual limit test chart has the original site-base-change comparison. -/
def diagramEtaleTestLimitChart : c.pt.unop.Etale :=
  Scheme.Etale.mk (pullback.fst (c.ι.app i).unop T.hom)

/-- Only native pullback symmetry changes the geometric orientation to site evaluation. -/
def diagramEtaleTestLimitChartIso : diagramEtaleTestLimitChart X i T c ≅
    (siteBaseChange (c.ι.app i).unop).obj T :=
  MorphismProperty.Over.isoMk (pullbackSymmetry (c.ι.app i).unop T.hom)
    (pullbackSymmetry_hom_comp_snd _ _)

variable [IsFiltered I]

/-- Finality of the original tail and the native under/over equivalence preserve its colimit. -/
def relativeSchemeTailCoconeIsColimit (hc : IsColimit c) :
    IsColimit (relativeSchemeTailCocone X c i) :=
  isColimitOfPreserves (Under.opEquivOpOver (X.obj i).unop).functor (hc.underPost i)

/-- Native pullback preserves the original tail limit; this is the actual test cocone. -/
def diagramEtaleTestCoconeIsColimit (hc : IsColimit c) :
    IsColimit (diagramEtaleTestCocone X i T c) := by
  let b : T.left ⟶ (X.obj i).unop := T.hom
  let B : Over (X.obj i).unop ⥤ Over T.left := Over.pullback b
  have : PreservesLimitsOfShape (Under i)ᵒᵖ B := inferInstance
  have : PreservesLimitsOfShape (Under i)ᵒᵖ (Over.forget T.left) := inferInstance
  have : PreservesColimitsOfShape (Under i) (B ⋙ Over.forget T.left).op :=
    preservesColimitsOfShape_op (Under i) (B ⋙ Over.forget T.left)
  exact isColimitOfPreserves (B ⋙ Over.forget T.left).op
    (relativeSchemeTailCoconeIsColimit X i c hc)

variable [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop]

/-- Native test transitions are base changes of the original affine transitions. -/
instance diagramEtaleTest_map_isAffineHom {a b : Under i} (m : a ⟶ b) :
    IsAffineHom ((diagramEtaleTest X i T).map m).unop :=
  MorphismProperty.overPullbackMap (P := @IsAffineHom) T.hom
    (((relativeSchemeTail X i).map m).unop)
    (inferInstanceAs (IsAffineHom (X.map m.right).unop))

/-- A qc stage test gives qc test schemes at every later stage. -/
instance diagramEtaleTest_obj_compactSpace [CompactSpace T.left] (a : Under i) :
    CompactSpace ((diagramEtaleTest X i T).obj a).unop := by
  let f : (X.obj a.right).unop ⟶ (X.obj i).unop := (X.map a.hom).unop
  let g : T.left ⟶ (X.obj i).unop := T.hom
  have : IsAffineHom f := inferInstanceAs (IsAffineHom (X.map a.hom).unop)
  have h : CompactSpace (pullback f g : Scheme.{u}) := inferInstance
  exact h

/-- A quasi-separated stage test gives quasi-separated test schemes at every later stage. -/
instance diagramEtaleTest_obj_quasiSeparatedSpace [QuasiSeparatedSpace T.left] (a : Under i) :
    QuasiSeparatedSpace ((diagramEtaleTest X i T).obj a).unop := by
  let f : (X.obj a.right).unop ⟶ (X.obj i).unop := (X.map a.hom).unop
  let g : T.left ⟶ (X.obj i).unop := T.hom
  have : IsAffineHom f := inferInstanceAs (IsAffineHom (X.map a.hom).unop)
  have : QuasiSeparated (pullback.snd f g) := inferInstance
  exact @quasiSeparatedSpace_of_quasiSeparated (pullback f g) T.left
    (pullback.snd f g) inferInstance inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

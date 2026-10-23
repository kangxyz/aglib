/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StageSupport.Objects
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes

/-!
# Common actual stage models of finite supported families

The finite-presentation Hom descent theorem descends the original structural
arrows, not merely the objects. The comparison equations remain equations in
the original small étale site. There is no covering assumption on the family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.StageSupport

variable {I : Type u} [Category.{u} I]
  {X : I ⥤ Scheme.{u}ᵒᵖ} {c : Cocone X}

/-- The existing geometric finite-presentation model supplied by an actual
small-site model. Quasi-compactness uses quasi-separatedness of the stage. -/
def Model.finitePresentationModel {i : I} {W : c.pt.unop.Etale}
    [QuasiSeparatedSpace (X.obj i).unop] (M : Model X c i W) :
    Scheme.FinitePresentationDescent.Model (c.ι.app i).unop W.hom := by
  let f : M.obj.left ⟶ (X.obj i).unop := M.obj.hom
  let : CompactSpace M.obj.left := M.compactSpace
  let : QuasiSeparatedSpace M.obj.left := M.quasiSeparatedSpace
  let : Etale f := inferInstanceAs (Etale M.obj.hom)
  let : QuasiCompact f := quasiCompact_of_compactSpace f
  let : QuasiSeparated f := QuasiSeparated.of_quasiSeparatedSpace f
  let e : (Over.pullback (c.ι.app i).unop).obj (Over.mk f) ≅
      Over.mk W.hom := (Scheme.Etale.forget c.pt.unop).mapIso M.iso
  exact Scheme.FinitePresentationDescent.Model.ofOverIso f e

/-- A geometric model which is étale at the specified stage is a model in the
actual small étale site. Its comparison is the existing cartesian comparison. -/
def ofFinitePresentation {i : I} {W : c.pt.unop.Etale}
    [CompactSpace (X.obj i).unop] [QuasiSeparatedSpace (X.obj i).unop]
    (M : Scheme.FinitePresentationDescent.Model (c.ι.app i).unop W.hom)
    [Etale M.f] : Model X c i W where
  obj := Scheme.Etale.mk M.f
  compactSpace := @QuasiCompact.compactSpace_of_compactSpace M.X (X.obj i).unop M.f
    M.quasiCompact (inferInstanceAs (CompactSpace (X.obj i).unop))
  quasiSeparatedSpace := @quasiSeparatedSpace_of_quasiSeparated M.X (X.obj i).unop M.f
    (inferInstanceAs (QuasiSeparatedSpace (X.obj i).unop)) M.quasiSeparated
  iso := MorphismProperty.Over.isoMk
    ((Over.forget c.pt.unop).mapIso M.overIso) (Over.w M.overIso.hom)

/-- Lift a map of the existing geometric models to the original small site,
retaining its original base-change comparison equation. -/
theorem ofFinitePresentation_map {i : I} {V W : c.pt.unop.Etale}
    [CompactSpace (X.obj i).unop] [QuasiSeparatedSpace (X.obj i).unop]
    (M : Scheme.FinitePresentationDescent.Model (c.ι.app i).unop V.hom)
    (N : Scheme.FinitePresentationDescent.Model (c.ι.app i).unop W.hom)
    [Etale M.f] [Etale N.f] (m : V ⟶ W)
    (a : Scheme.FinitePresentationDescent.Model.Map M N
      ((Scheme.Etale.forget c.pt.unop).map m)) :
    ∃ b : (ofFinitePresentation M).obj ⟶ (ofFinitePresentation N).obj,
      (siteBaseChange (c.ι.app i).unop).map b ≫ (ofFinitePresentation N).iso.hom =
        (ofFinitePresentation M).iso.hom ≫ m := by
  refine ⟨MorphismProperty.Over.homMk a.hom.left (Over.w a.hom), ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact congrArg (fun f => f.left) a.overIso_naturality

/-- Actual qcqs stage models for a finite family and its target, including
all specified original arrows and their base-change triangles. -/
structure FamilyModel (i : I) {W : c.pt.unop.Etale} {J : Type v}
    (U : J → Over W) where
  /-- A model of the original target. -/
  target : Model X c i W
  /-- Models of the original family sources. -/
  source : ∀ j, Model X c i (U j).left
  /-- The actual arrows in the original stage small étale site. -/
  hom : ∀ j, (source j).obj ⟶ target.obj
  /-- The original structural arrow agrees with the base-changed stage arrow. -/
  comm : ∀ j,
    (siteBaseChange (c.ι.app i).unop).map (hom j) ≫ target.iso.hom =
      (source j).iso.hom ≫ (U j).hom

/-- The literal stage family in the original slice category. -/
def FamilyModel.family {i : I} {W : c.pt.unop.Etale} {J : Type v}
    {U : J → Over W} (M : FamilyModel (X := X) (c := c) i U) :
    J → Over M.target.obj := fun j => Over.mk (M.hom j)

/-- Descend every arrow of any finite supported family to a common actual
stage. In particular this applies to noncovering families required by the
supported Čech-acyclicity interface. -/
theorem exists_familyModel [IsFiltered I]
    [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
    (hc : IsColimit c) {W : c.pt.unop.Etale}
    (hW : stageDescendedQcqsObjects X c W) {J : Type v} [Finite J]
    (U : J → Over W) (hU : ∀ j, stageDescendedQcqsObjects X c (U j).left) :
    ∃ i : I, Nonempty (FamilyModel (X := X) (c := c) i U) := by
  classical
  let Z : Option J → c.pt.unop.Etale := fun o => o.elim W (fun j => (U j).left)
  have hZ : ∀ o, stageDescendedQcqsObjects X c (Z o) := by
    rintro (_ | j)
    · exact hW
    · exact hU j
  obtain ⟨i, ⟨M⟩⟩ := exists_common_stage_models X c Z hZ
  let D : Iᵒᵖ ⥤ Scheme.{u} := X.leftOp
  let C : Cone D := coneLeftOpOfCocone c
  let hC : IsLimit C := isLimitConeLeftOpOfCocone X hc
  let {j k : Iᵒᵖ} (a : j ⟶ k) : IsAffineHom (D.map a) :=
    inferInstanceAs (IsAffineHom (X.map a.unop).unop)
  let (j : Iᵒᵖ) : CompactSpace (D.obj j) :=
    inferInstanceAs (CompactSpace (X.obj j.unop).unop)
  let (j : Iᵒᵖ) : QuasiSeparatedSpace (D.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (X.obj j.unop).unop)
  let N (o : Option J) : Scheme.FinitePresentationDescent.Model
      (C.π.app (op i)) (Z o).hom := (M o).finitePresentationModel
  obtain ⟨k, hk⟩ := Scheme.FinitePresentationDescent.Model.exists_common_maps
    D C hC (op i) (fun j : J => some j) (fun _ => none)
    (fun o => (Z o).left) (fun o => (Z o).hom) N
    (fun j => (Scheme.Etale.forget c.pt.unop).map (U j).hom)
  let R (o : Option J) := (N o).rebase D C (op i) k
  let (o : Option J) : Etale (R o).f := by
    change Etale (pullback.snd (M o).obj.hom (D.map k.hom))
    infer_instance
  let target : Model X c k.left.unop W := ofFinitePresentation (R none)
  let source (j : J) : Model X c k.left.unop (U j).left :=
    ofFinitePresentation (R (some j))
  have hm (j : J) : ∃ b : (source j).obj ⟶ target.obj,
      (siteBaseChange (c.ι.app k.left.unop).unop).map b ≫ target.iso.hom =
        (source j).iso.hom ≫ (U j).hom :=
    ofFinitePresentation_map (R (some j)) (R none) (U j).hom (Classical.choice (hk j))
  choose b hb using hm
  exact ⟨k.left.unop, ⟨⟨target, source, b, hb⟩⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.StageSupport

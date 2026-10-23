/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Filtered.Small
public import Mathlib.CategoryTheory.Limits.Opposites

/-!
# Actual stage-descended objects of the limit small étale site

A model consists of a qcqs object of an original stage small étale site and
an isomorphism from its actual base change to the specified limit object.
No cohomological or model-existence hypothesis is part of the support predicate.
The intended consumer is higher scheme-limit continuity via supported families.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

namespace StageSupport

/-- Affine base change preserves qcqsness of the underlying étale object. -/
theorem qcqs_baseChange {S T : Scheme.{u}} (f : T ⟶ S) [IsAffineHom f]
    (U : S.Etale) (hU : CompactSpace U.left ∧ QuasiSeparatedSpace U.left) :
    CompactSpace ((siteBaseChange f).obj U).left ∧
      QuasiSeparatedSpace ((siteBaseChange f).obj U).left := by
  let : CompactSpace U.left := hU.1
  let : QuasiSeparatedSpace U.left := hU.2
  let g : U.left ⟶ S := U.hom
  change CompactSpace (pullback g f : Scheme.{u}) ∧
    QuasiSeparatedSpace (pullback g f : Scheme.{u})
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (pullback.fst g f),
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst g f)⟩

/-- Transport qcqsness along an isomorphism of the original small étale site. -/
theorem qcqs_of_iso {S : Scheme.{u}} {U V : S.Etale} (e : U ≅ V)
    (hU : CompactSpace U.left ∧ QuasiSeparatedSpace U.left) :
    CompactSpace V.left ∧ QuasiSeparatedSpace V.left := by
  let d : U.left ≅ V.left := ((Scheme.Etale.forget S) ⋙ Over.forget S).mapIso e
  let : CompactSpace U.left := hU.1
  exact ⟨d.hom.homeomorph.compactSpace,
    (quasiSeparatedSpace_congr d.hom.homeomorph).mp hU.2⟩

variable {I : Type u} [Category.{u} I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)

/-- The projection from an actual affine-transition inverse limit is affine. -/
theorem projection_isAffine [IsFiltered I] (hc : IsColimit c)
    [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop] (i : I) :
    IsAffineHom (c.ι.app i).unop := by
  let {j k : Iᵒᵖ} (a : j ⟶ k) : IsAffineHom (X.leftOp.map a) :=
    inferInstanceAs (IsAffineHom (X.map a.unop).unop)
  exact isAffineHom_π_app X.leftOp (coneLeftOpOfCocone c)
    (isLimitConeLeftOpOfCocone X hc) (op i)

/-- A specified qcqs stage object and its actual small-site comparison. -/
structure Model (i : I) (W : c.pt.unop.Etale) where
  /-- The actual object of the original stage small étale site. -/
  obj : (X.obj i).unop.Etale
  /-- Quasi-compactness of its underlying scheme. -/
  compactSpace : CompactSpace obj.left
  /-- Quasi-separatedness of its underlying scheme. -/
  quasiSeparatedSpace : QuasiSeparatedSpace obj.left
  /-- The comparison is in the actual limit small étale site. -/
  iso : (siteBaseChange (c.ι.app i).unop).obj obj ≅ W

attribute [instance] Model.compactSpace Model.quasiSeparatedSpace

variable {X c}

/-- The composition comparison dictated by the original cone equation. -/
def reindexIso {i j : I} (a : i ⟶ j) (U : (X.obj i).unop.Etale) :
    (siteBaseChange (c.ι.app j).unop).obj ((siteBaseChange (X.map a).unop).obj U) ≅
      (siteBaseChange (c.ι.app i).unop).obj U :=
  ((siteBaseChangeComp (X.map a).unop (c.ι.app j).unop).app U).symm ≪≫
    eqToIso (congrArg (fun f => (siteBaseChange f).obj U)
      (congrArg (fun f : X.obj i ⟶ c.pt => f.unop) (c.w a)))

/-- Transport the specified model to a later stage by actual base change. -/
def Model.reindex {i j : I} {W : c.pt.unop.Etale} (M : Model X c i W)
    (a : i ⟶ j) [IsAffineHom (X.map a).unop] : Model X c j W where
  obj := (siteBaseChange (X.map a).unop).obj M.obj
  compactSpace := (qcqs_baseChange (X.map a).unop M.obj
    ⟨M.compactSpace, M.quasiSeparatedSpace⟩).1
  quasiSeparatedSpace := (qcqs_baseChange (X.map a).unop M.obj
    ⟨M.compactSpace, M.quasiSeparatedSpace⟩).2
  iso := reindexIso a M.obj ≪≫ M.iso

/-- A modeled limit object is genuinely qcqs. -/
theorem Model.qcqs [IsFiltered I] (hc : IsColimit c)
    [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
    {i : I} {W : c.pt.unop.Etale} (M : Model X c i W) :
    CompactSpace W.left ∧ QuasiSeparatedSpace W.left := by
  let : IsAffineHom (c.ι.app i).unop := projection_isAffine X c hc i
  exact qcqs_of_iso M.iso (qcqs_baseChange (c.ι.app i).unop M.obj
    ⟨M.compactSpace, M.quasiSeparatedSpace⟩)

/-- The identity étale object has its specified identity stage model. -/
def terminalModel (i : I) [CompactSpace (X.obj i).unop]
    [QuasiSeparatedSpace (X.obj i).unop] : Model X c i (etaleTerminal c.pt.unop) where
  obj := etaleTerminal (X.obj i).unop
  compactSpace := inferInstanceAs (CompactSpace (X.obj i).unop)
  quasiSeparatedSpace := inferInstanceAs (QuasiSeparatedSpace (X.obj i).unop)
  iso := siteBaseChangeTerminalIso (c.ι.app i).unop

end StageSupport

variable {I : Type u} [Category.{u} I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)

/-- Objects isomorphic in the original limit small étale site to the actual
base change of a qcqs object at some stage. This is only geometric data. -/
def stageDescendedQcqsObjects (W : c.pt.unop.Etale) : Prop :=
  ∃ i : I, Nonempty (StageSupport.Model X c i W)

/-- The support predicate is stable under actual small-site isomorphisms. -/
theorem stageDescendedQcqsObjects_of_iso {U V : c.pt.unop.Etale}
    (e : U ≅ V) (hU : stageDescendedQcqsObjects X c U) :
    stageDescendedQcqsObjects X c V := by
  obtain ⟨i, ⟨M⟩⟩ := hU
  exact ⟨i, ⟨{ M with iso := M.iso ≪≫ e }⟩⟩

/-- Every supported object is qcqs on the actual limit scheme. -/
theorem stageDescendedQcqsObjects_qcqs [IsFiltered I] (hc : IsColimit c)
    [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
    {W : c.pt.unop.Etale} (hW : stageDescendedQcqsObjects X c W) :
    CompactSpace W.left ∧ QuasiSeparatedSpace W.left := by
  obtain ⟨i, ⟨M⟩⟩ := hW
  exact M.qcqs hc

/-- The literal terminal object belongs to the geometric support class. -/
theorem stageDescendedQcqsObjects_terminal [IsFiltered I]
    [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop] :
    stageDescendedQcqsObjects X c (etaleTerminal c.pt.unop) := by
  obtain ⟨i⟩ := IsFiltered.nonempty (C := I)
  exact ⟨i, ⟨StageSupport.terminalModel i⟩⟩

/-- Finitely many supported objects have actual qcqs étale models at one
common stage. No arrows or covering relation are assumed or asserted here. -/
theorem exists_common_stage_models [IsFiltered I]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
    {J : Type v} [Finite J] (W : J → c.pt.unop.Etale)
    (hW : ∀ j, stageDescendedQcqsObjects X c (W j)) :
    ∃ i : I, Nonempty (∀ j, StageSupport.Model X c i (W j)) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  choose i M using hW
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let q (j : J) : i j ⟶ k := (hk (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  exact ⟨k, ⟨fun j => (Classical.choice (M j)).reindex (q j)⟩⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

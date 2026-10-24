/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Composition

/-!
# Actual common refinements of compactified composition towers

Take the common target compactification and the common composite compactification.
Schematic density lifts the latter's pair of structural maps through the closed
image defining the former. This constructs a compatible proper tower over both
original towers, without assuming a common tower as additional data.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.CompactifiedComposition

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Actual proper refinements at both levels, preserving the intermediate base square. -/
structure Refinement (C D : CompactifiedComposition f g) where
  /-- The refinement of the middle-scheme compactifications. -/
  target : C.targetCompactification ⟶ D.targetCompactification
  /-- The refinement of the compactifications of the composite. -/
  source : C.composite ⟶ D.composite
  /-- The source refinement lies over the target refinement. -/
  comm : source.hom ≫ D.sourceCompactification.p = C.sourceCompactification.p ≫ target.hom

instance (C D : CompactifiedComposition f g) : Subsingleton (Refinement C D) where
  allEq a b := by
    cases a with
    | mk aTarget aSource aComm =>
      cases b with
      | mk bTarget bSource bComm =>
        have ht : aTarget = bTarget := Subsingleton.elim _ _
        have hs : aSource = bSource := Subsingleton.elim _ _
        cases ht
        cases hs
        rfl

variable [QuasiCompact f] [QuasiCompact g] (C D : CompactifiedComposition f g)

/-- The actual common compactification of the middle scheme. -/
abbrev commonTarget :=
  DenseCompactification.common C.targetCompactification D.targetCompactification

/-- The actual common compactification of the composite source over the final base. -/
abbrev commonAmbient := DenseCompactification.common C.composite D.composite

/-- Pair the original proper structural maps of the two source ambients. -/
def commonBasePair : (commonAmbient C D).Xbar ⟶
    pullback C.targetCompactification.p D.targetCompactification.p :=
  pullback.lift
    ((DenseCompactification.commonToLeft C.composite D.composite).hom ≫
      C.sourceCompactification.p)
    ((DenseCompactification.commonToRight C.composite D.composite).hom ≫
      D.sourceCompactification.p) (by
        calc
          _ = (DenseCompactification.commonToLeft C.composite D.composite).hom ≫
              (C.sourceCompactification.p ≫ C.targetCompactification.p) := Category.assoc _ _ _
          _ = (commonAmbient C D).p :=
            (DenseCompactification.commonToLeft C.composite D.composite).base_fac
          _ = (DenseCompactification.commonToRight C.composite D.composite).hom ≫
              (D.sourceCompactification.p ≫ D.targetCompactification.p) :=
            (DenseCompactification.commonToRight C.composite D.composite).base_fac.symm
          _ = _ := (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
lemma commonBasePair_fst :
    commonBasePair C D ≫ pullback.fst C.targetCompactification.p D.targetCompactification.p =
      (DenseCompactification.commonToLeft C.composite D.composite).hom ≫
        C.sourceCompactification.p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma commonBasePair_snd :
    commonBasePair C D ≫ pullback.snd C.targetCompactification.p D.targetCompactification.p =
      (DenseCompactification.commonToRight C.composite D.composite).hom ≫
        D.sourceCompactification.p := pullback.lift_snd _ _ _

/-- On the original source, the ambient pair is the original map to the middle scheme
followed by its original pair of open embeddings. -/
lemma commonBasePair_open :
    (commonAmbient C D).j ≫ commonBasePair C D =
      f ≫ DenseCompactification.pair C.targetCompactification D.targetCompactification := by
  apply pullback.hom_ext
  · calc
      _ = (commonAmbient C D).j ≫
          (commonBasePair C D ≫ pullback.fst _ _) := Category.assoc _ _ _
      _ = (commonAmbient C D).j ≫
          ((DenseCompactification.commonToLeft C.composite D.composite).hom ≫
            C.sourceCompactification.p) := congrArg _ (commonBasePair_fst C D)
      _ = ((commonAmbient C D).j ≫
          (DenseCompactification.commonToLeft C.composite D.composite).hom) ≫
            C.sourceCompactification.p := (Category.assoc _ _ _).symm
      _ = C.sourceCompactification.j ≫ C.sourceCompactification.p :=
        congrArg (fun k => k ≫ C.sourceCompactification.p)
          (DenseCompactification.commonToLeft C.composite D.composite).open_fac
      _ = f ≫ C.targetCompactification.j := C.sourceCompactification.fac
      _ = f ≫ (DenseCompactification.pair C.targetCompactification D.targetCompactification ≫
          pullback.fst _ _) := congrArg (fun k => f ≫ k)
            (DenseCompactification.pair_fst C.targetCompactification D.targetCompactification).symm
      _ = _ := (Category.assoc _ _ _).symm
  · calc
      _ = (commonAmbient C D).j ≫
          (commonBasePair C D ≫ pullback.snd _ _) := Category.assoc _ _ _
      _ = (commonAmbient C D).j ≫
          ((DenseCompactification.commonToRight C.composite D.composite).hom ≫
            D.sourceCompactification.p) := congrArg _ (commonBasePair_snd C D)
      _ = ((commonAmbient C D).j ≫
          (DenseCompactification.commonToRight C.composite D.composite).hom) ≫
            D.sourceCompactification.p := (Category.assoc _ _ _).symm
      _ = D.sourceCompactification.j ≫ D.sourceCompactification.p :=
        congrArg (fun k => k ≫ D.sourceCompactification.p)
          (DenseCompactification.commonToRight C.composite D.composite).open_fac
      _ = f ≫ D.targetCompactification.j := D.sourceCompactification.fac
      _ = f ≫ (DenseCompactification.pair C.targetCompactification D.targetCompactification ≫
          pullback.snd _ _) := congrArg (fun k => f ≫ k)
            (DenseCompactification.pair_snd C.targetCompactification D.targetCompactification).symm
      _ = _ := (Category.assoc _ _ _).symm

/-- The proper structural map to the common target is obtained by actual closed-target lifting. -/
def commonSourceMap : (commonAmbient C D).Xbar ⟶
    (DenseCompactification.pair C.targetCompactification D.targetCompactification).image :=
  Scheme.QuasiDomination.closedTargetLift (commonAmbient C D).j
    (DenseCompactification.pair C.targetCompactification D.targetCompactification).imageι
    (commonBasePair C D) (f ≫ (commonTarget C D).j) (by
      calc
        _ = f ≫ DenseCompactification.pair C.targetCompactification D.targetCompactification :=
          commonBasePair_open C D
        _ = _ := ((Category.assoc _ _ _).trans
          (congrArg (fun k => f ≫ k)
            (DenseCompactification.pair C.targetCompactification
              D.targetCompactification).toImage_imageι)).symm)

@[reassoc (attr := simp)]
lemma commonSourceMap_imageι :
    commonSourceMap C D ≫
        (DenseCompactification.pair C.targetCompactification D.targetCompactification).imageι =
      commonBasePair C D :=
  Scheme.QuasiDomination.closedTargetLift_comp _ _ _ _ _

@[reassoc (attr := simp)]
lemma commonSourceMap_open :
    (commonAmbient C D).j ≫ commonSourceMap C D = f ≫ (commonTarget C D).j :=
  Scheme.QuasiDomination.comp_closedTargetLift _ _ _ _ _

/-- The common structural map retains its original first projection. -/
@[reassoc]
lemma commonSourceMap_left :
    commonSourceMap C D ≫
        (DenseCompactification.commonToLeft C.targetCompactification D.targetCompactification).hom =
      (DenseCompactification.commonToLeft C.composite D.composite).hom ≫
        C.sourceCompactification.p := by
  change commonSourceMap C D ≫
    ((DenseCompactification.pair C.targetCompactification D.targetCompactification).imageι ≫
      pullback.fst _ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.fst _ _) (commonSourceMap_imageι C D)).trans
      (commonBasePair_fst C D))

/-- The common structural map retains its original second projection. -/
@[reassoc]
lemma commonSourceMap_right :
    commonSourceMap C D ≫
        (DenseCompactification.commonToRight C.targetCompactification
          D.targetCompactification).hom =
      (DenseCompactification.commonToRight C.composite D.composite).hom ≫
        D.sourceCompactification.p := by
  change commonSourceMap C D ≫
    ((DenseCompactification.pair C.targetCompactification D.targetCompactification).imageι ≫
      pullback.snd _ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.snd _ _) (commonSourceMap_imageι C D)).trans
      (commonBasePair_snd C D))

/-- The lifted structural map preserves the actual map to the final base. -/
@[simp, reassoc]
lemma commonSourceMap_p :
    commonSourceMap C D ≫ (commonTarget C D).p = (commonAmbient C D).p := by
  calc
    _ = commonSourceMap C D ≫
        ((DenseCompactification.commonToLeft C.targetCompactification
          D.targetCompactification).hom ≫
          C.targetCompactification.p) := congrArg (fun k => commonSourceMap C D ≫ k)
            (DenseCompactification.commonToLeft C.targetCompactification
              D.targetCompactification).base_fac.symm
    _ = (commonSourceMap C D ≫
        (DenseCompactification.commonToLeft C.targetCompactification
          D.targetCompactification).hom) ≫
          C.targetCompactification.p := (Category.assoc _ _ _).symm
    _ = ((DenseCompactification.commonToLeft C.composite D.composite).hom ≫
        C.sourceCompactification.p) ≫ C.targetCompactification.p :=
      congrArg (fun k => k ≫ C.targetCompactification.p) (commonSourceMap_left C D)
    _ = (DenseCompactification.commonToLeft C.composite D.composite).hom ≫
        (C.sourceCompactification.p ≫ C.targetCompactification.p) := Category.assoc _ _ _
    _ = _ := (DenseCompactification.commonToLeft C.composite D.composite).base_fac

instance commonSourceMap_isProper : IsProper (commonSourceMap C D) := by
  have hTargetProper : IsProper (commonTarget C D).p :=
    (commonTarget C D).toCompactification.isProper_p
  have hTargetSeparated : IsSeparated (commonTarget C D).p := inferInstance
  have hComposite : IsProper (commonSourceMap C D ≫ (commonTarget C D).p) := by
    rw [commonSourceMap_p]
    infer_instance
  exact @IsProper.of_comp _ _ _ (commonSourceMap C D) (commonTarget C D).p
    hComposite hTargetSeparated

/-- An actual common compactified composition tower. -/
def common : CompactifiedComposition f g where
  targetCompactification := commonTarget C D
  sourceCompactification :=
    { Xbar := (commonAmbient C D).Xbar
      j := (commonAmbient C D).j
      p := commonSourceMap C D
      isOpenImmersion_j := inferInstance
      isProper_p := commonSourceMap_isProper C D
      fac := commonSourceMap_open C D
      isSchemeTheoreticallyDominant_j := inferInstance }

/-- The common tower refines the first original tower with both actual maps. -/
def commonToLeft : Refinement (common C D) C where
  target := DenseCompactification.commonToLeft C.targetCompactification D.targetCompactification
  source :=
    { hom := (DenseCompactification.commonToLeft C.composite D.composite).hom
      isProper_hom := inferInstanceAs
        (IsProper (DenseCompactification.commonToLeft C.composite D.composite).hom)
      open_fac := (DenseCompactification.commonToLeft C.composite D.composite).open_fac
      base_fac := (DenseCompactification.commonToLeft C.composite D.composite).base_fac.trans
        (commonSourceMap_p C D).symm }
  comm := (commonSourceMap_left C D).symm

/-- The common tower refines the second original tower with both actual maps. -/
def commonToRight : Refinement (common C D) D where
  target := DenseCompactification.commonToRight C.targetCompactification D.targetCompactification
  source :=
    { hom := (DenseCompactification.commonToRight C.composite D.composite).hom
      isProper_hom := inferInstanceAs
        (IsProper (DenseCompactification.commonToRight C.composite D.composite).hom)
      open_fac := (DenseCompactification.commonToRight C.composite D.composite).open_fac
      base_fac := (DenseCompactification.commonToRight C.composite D.composite).base_fac.trans
        (commonSourceMap_p C D).symm }
  comm := (commonSourceMap_right C D).symm

end AlgebraicGeometry.Scheme.Hom.CompactifiedComposition

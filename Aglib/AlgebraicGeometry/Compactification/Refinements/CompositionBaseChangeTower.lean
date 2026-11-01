/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionBaseChangeGeometry

/-! # Actual dense composition towers after arbitrary base change

Normalize the target first, then pull back and normalize the source over that
actual normalized target. Every map is retained. The resulting proper source
square is not asserted Cartesian: its raw predecessor is Cartesian, while the
normalization is a closed refinement that is Cartesian over the open source.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.CompactifiedComposition

variable {X Y Z X' Y' T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (C : CompactifiedComposition f g)
  (f' : X' ⟶ Y') (g' : Y' ⟶ T) (a : X' ⟶ X) (c : Y' ⟶ Y) (b : T ⟶ Z)
  (sqf : IsPullback a f' f c) (sqg : IsPullback c g' g b)
  [QuasiCompact f'] [QuasiCompact g']

/-- The actual dense target compactification over the arbitrary new base. -/
def baseChangeTarget : DenseCompactification g' :=
  Compactification.normalizedCartesianBaseChange
    C.targetCompactification.toCompactification g' c b sqg

/-- Retain the actual map from the normalized target to the original target. -/
def baseChangeTargetProjection : (baseChangeTarget C g' c b sqg).Xbar ⟶
    C.targetCompactification.Xbar :=
  Compactification.cartesianBaseChangeProjection
    C.targetCompactification.toCompactification g' c b sqg

/-- The actual target normalization is Cartesian over the open middle scheme. -/
lemma isPullback_baseChangeTarget_open :
    IsPullback c (baseChangeTarget C g' c b sqg).j C.targetCompactification.j
      (baseChangeTargetProjection C g' c b sqg) :=
  Compactification.isPullback_normalizedCartesianBaseChange_open
    C.targetCompactification.toCompactification g' c b sqg

include sqf in
omit [QuasiCompact f'] in
/-- Pasting gives the actual source square over the normalized target ambient. -/
lemma isPullback_baseChangeSource :
    IsPullback a (f' ≫ (baseChangeTarget C g' c b sqg).j)
      (f ≫ C.targetCompactification.j) (baseChangeTargetProjection C g' c b sqg) :=
  sqf.paste_vert (isPullback_baseChangeTarget_open C g' c b sqg)

/-- The raw source is a literal proper pullback, with its actual source transport. -/
def baseChangeSourceRaw :
    Compactification (f' ≫ (baseChangeTarget C g' c b sqg).j) :=
  Compactification.cartesianBaseChange C.sourceCompactification.toCompactification
    (f' ≫ (baseChangeTarget C g' c b sqg).j) a
    (baseChangeTargetProjection C g' c b sqg)
    (isPullback_baseChangeSource C f' g' a c b sqf sqg)

/-- The constructed dense tower needs neither Nagata nor qcqs on the new base. -/
def cartesianBaseChange : CompactifiedComposition f' g' where
  targetCompactification := baseChangeTarget C g' c b sqg
  sourceCompactification :=
    Compactification.normalizedCartesianBaseChange C.sourceCompactification.toCompactification
      (f' ≫ (baseChangeTarget C g' c b sqg).j) a
      (baseChangeTargetProjection C g' c b sqg)
      (isPullback_baseChangeSource C f' g' a c b sqf sqg)

/-- The retained source map goes through the closed normalization of the raw pullback. -/
def baseChangeSourceProjection :
    (cartesianBaseChange C f' g' a c b sqf sqg).sourceCompactification.Xbar ⟶
      C.sourceCompactification.Xbar :=
  Compactification.cartesianBaseChangeProjection C.sourceCompactification.toCompactification
    (f' ≫ (baseChangeTarget C g' c b sqg).j) a
    (baseChangeTargetProjection C g' c b sqg)
    (isPullback_baseChangeSource C f' g' a c b sqf sqg)

/-- The actual source square remains Cartesian over the original open source. -/
lemma isPullback_baseChangeSource_open :
    IsPullback a (cartesianBaseChange C f' g' a c b sqf sqg).sourceCompactification.j
      C.sourceCompactification.j (baseChangeSourceProjection C f' g' a c b sqf sqg) :=
  Compactification.isPullback_normalizedCartesianBaseChange_open
    C.sourceCompactification.toCompactification
    (f' ≫ (baseChangeTarget C g' c b sqg).j) a
    (baseChangeTargetProjection C g' c b sqg)
    (isPullback_baseChangeSource C f' g' a c b sqf sqg)

/-- The source projection retains the original proper structural triangle. -/
@[reassoc]
lemma baseChangeSourceProjection_p :
    baseChangeSourceProjection C f' g' a c b sqf sqg ≫ C.sourceCompactification.p =
      (cartesianBaseChange C f' g' a c b sqf sqg).sourceCompactification.p ≫
        baseChangeTargetProjection C g' c b sqg :=
  Compactification.cartesianBaseChangeProjection_p
    C.sourceCompactification.toCompactification
    (f' ≫ (baseChangeTarget C g' c b sqg).j) a
    (baseChangeTargetProjection C g' c b sqg)
    (isPullback_baseChangeSource C f' g' a c b sqf sqg)

include C sqf sqg in
/-- A supplied tower remains compactifiable over an arbitrary Cartesian new base. -/
theorem cartesianBaseChange_nonempty : Nonempty (CompactifiedComposition f' g') :=
  ⟨cartesianBaseChange C f' g' a c b sqf sqg⟩

end AlgebraicGeometry.Scheme.Hom.CompactifiedComposition

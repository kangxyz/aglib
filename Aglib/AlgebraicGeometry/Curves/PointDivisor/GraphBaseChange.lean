/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphLineBundle
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Family
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange

/-! The original positive graph line bundle under field extension. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem graphIdealClass_fieldBaseChange
    (K : Type u) [Field K] [Algebra k K]
    (T : FScheme K) (s : T ⟶ fieldBaseChange K X) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    letI := hX.smooth
    letI := hX.proper
    letI : SmoothOfRelativeDimension 1 (pullback.snd X.hom b) :=
      (curveProperties_baseChange hX K b).smooth
    letI : IsProper (pullback.snd X.hom b) := (curveProperties_baseChange hX K b).proper
    pullbackClass (familyBaseChangeIso X.hom b T).hom
        (classOf _ (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal
          X.hom (T.hom ≫ b) (s.left ≫ pullback.fst X.hom b)
          (by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact congrArg (fun v => v ≫ b)
              (show s.left ≫ pullback.snd X.hom b = T.hom from s.w)))) =
      classOf _ (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal
        (pullback.snd X.hom b) T.hom s.left s.w) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let := hX.smooth
  let := hX.proper
  let : SmoothOfRelativeDimension 1 (pullback.snd X.hom b) :=
    (curveProperties_baseChange hX K b).smooth
  let : IsProper (pullback.snd X.hom b) := (curveProperties_baseChange hX K b).proper
  let e := familyBaseChangeIso X.hom b T
  let Y := pullback X.hom (T.hom ≫ b)
  let Y' := pullback (pullback.snd X.hom b) T.hom
  let i : T.left ⟶ Y := Hom.graph X.hom (T.hom ≫ b)
    (s.left ≫ pullback.fst X.hom b)
    (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun v => v ≫ b)
        (show s.left ≫ pullback.snd X.hom b = T.hom from s.w))
  let i' : T.left ⟶ Y' := Hom.graph (pullback.snd X.hom b) T.hom s.left s.w
  have he : i' ≫ e.hom = i := by
    apply pullback.hom_ext
    · simp only [Category.assoc, e, familyBaseChangeIso_hom_fst,
        i, i', Hom.graph_fst, Hom.graph_fst_assoc]
    · simp only [Category.assoc, e, familyBaseChangeIso_hom_snd,
        i, i', Hom.graph_snd]
  have h : (𝟙 T.left) ≫ i = i' ≫ e.hom := (Category.id_comp i).trans he.symm
  have hfamily : IsPullback e.hom
      (pullback.snd (pullback.snd X.hom b) T.hom)
      (pullback.snd X.hom (T.hom ≫ b)) (𝟙 T.left) :=
    IsPullback.of_horiz_isIso ⟨by
      simpa only [Category.comp_id, e] using familyBaseChangeIso_hom_snd X.hom b T⟩
  have hgraph : IsPullback (𝟙 T.left) i' i e.hom := IsPullback.of_horiz_isIso ⟨h⟩
  have hi : IsClosedImmersion i := by dsimp [i]; infer_instance
  have hrank : IsLocallyRankOne Y (Hom.idealModule i) :=
    Hom.graphIdeal_isLocallyRankOne Hom.smoothRelativeDivisorIdeal X.hom (T.hom ≫ b)
      (s.left ≫ pullback.fst X.hom b) _
  have hflat : Flat (i ≫ pullback.snd X.hom (T.hom ≫ b)) := by
    dsimp [i]
    rw [Hom.graph_snd]
    infer_instance
  have hIso : IsIso (Hom.idealPullbackMap i i' e.hom (𝟙 T.left) h) :=
    Hom.relativeCartierIdealBaseChange T.left T.left Y Y' T.left T.left
      (pullback.snd X.hom (T.hom ≫ b)) (𝟙 T.left)
      (pullback.snd (pullback.snd X.hom b) T.hom) e.hom i i' (𝟙 T.left) h
      hfamily hgraph hi hrank hflat
  let := hIso
  exact Quotient.sound ⟨asIso (Hom.idealPullbackMap i i' e.hom (𝟙 T.left) h)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual positive graph class commutes with the original family
base-change isomorphism, including nonreduced and non-Noetherian tests. -/
theorem positiveGraphClass_fieldBaseChange
    (K : Type u) [Field K] [Algebra k K]
    (T : FScheme K) (s : T ⟶ fieldBaseChange K X) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    letI := hX.smooth
    letI := hX.proper
    letI : SmoothOfRelativeDimension 1 (pullback.snd X.hom b) :=
      (curveProperties_baseChange hX K b).smooth
    letI : IsProper (pullback.snd X.hom b) := (curveProperties_baseChange hX K b).proper
    pullbackClass (familyBaseChangeIso X.hom b T).hom
        (classOf _ (Hom.positiveGraphLineBundle Hom.smoothRelativeDivisorIdeal
          X.hom (T.hom ≫ b) (s.left ≫ pullback.fst X.hom b)
          (by
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact congrArg (fun v => v ≫ b)
              (show s.left ≫ pullback.snd X.hom b = T.hom from s.w)))) =
      classOf _ (Hom.positiveGraphLineBundle Hom.smoothRelativeDivisorIdeal
        (pullback.snd X.hom b) T.hom s.left s.w) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let := hX.smooth
  let := hX.proper
  let : SmoothOfRelativeDimension 1 (pullback.snd X.hom b) :=
    (curveProperties_baseChange hX K b).smooth
  let : IsProper (pullback.snd X.hom b) := (curveProperties_baseChange hX K b).proper
  change pullbackClass (familyBaseChangeIso X.hom b T).hom
      (-classOf _ (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal
        X.hom (T.hom ≫ b) (s.left ≫ pullback.fst X.hom b) _)) =
    -classOf _ (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal
      (pullback.snd X.hom b) T.hom s.left s.w)
  rw [← PullbackTensor.Local.pullbackHom_apply, map_neg,
    PullbackTensor.Local.pullbackHom_apply, graphIdealClass_fieldBaseChange hX K T s]

end AlgebraicGeometry.Scheme.OverField.Curve

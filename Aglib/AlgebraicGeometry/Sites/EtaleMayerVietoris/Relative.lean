/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleMayerVietoris.Opens
public import Aglib.CategoryTheory.Sites.RepresentedTransfer.ProductFamily
public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleProductTests

/-! # Two-open squares of the original relative etale test functors

For `f : X ⟶ S`, the vertex at an open `U` is exactly base change along `f`
followed by the original product test with `U`. Arrows are the original
`productMap` whiskered by base change. On each target test, the resulting
square has a native small-etale Mayer–Vietoris structure, with equality of
underlying squares rather than an unspecified isomorphic replacement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty.Over
open AlgebraicGeometry.Scheme.EtaleCohomology

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

instance etaleProductFamilyEvaluation_continuous (T : X.Etale) :
    (productFamilyEvaluation (@Etale) T).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology := by
  let : (productTest (@Etale) T).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology :=
    inferInstanceAs ((etaleProductTest T).IsContinuous _ _)
  exact Functor.isContinuous_of_iso (productFamilyEvaluationIso (@Etale) T).symm _ _

instance etaleProductFamilyEvaluation_preservesPullbacks (T : X.Etale) :
    PreservesLimitsOfShape WalkingCospan (productFamilyEvaluation (@Etale) T) := by
  let : PreservesLimitsOfShape WalkingCospan (productTest (@Etale) T) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (siteBaseChange T.hom ⋙ siteEtalePostcompose T.hom))
  exact preservesLimitsOfShape_of_natIso (productFamilyEvaluationIso (@Etale) T).symm

/-- Symmetry transports the actual jointly surjective product covers. -/
theorem etaleProductFamilyEvaluation_coverPreserving (T : X.Etale) :
    CoverPreserving X.smallEtaleTopology X.smallEtaleTopology
      (productFamilyEvaluation (@Etale) T) := by
  let e := (productFamilyEvaluationIso (@Etale) T).symm
  have hF : CoverPreserving X.smallEtaleTopology X.smallEtaleTopology
      (productTest (@Etale) T) :=
    CoverPreserving.comp X.smallEtaleTopology T.left.smallEtaleTopology
      (siteBaseChange_coverPreserving T.hom) (siteEtalePostcompose_coverPreserving T.hom)
  constructor
  intro W R hR
  apply X.smallEtaleTopology.superset_covering (S :=
    (R.functorPushforward (productTest (@Etale) T)).pullback (e.inv.app W))
  · intro Z g hg
    obtain ⟨Y, a, b, ha, hfac⟩ := hg
    refine ⟨Y, a, b ≫ e.hom.app Y, ha, ?_⟩
    calc
      g = (g ≫ e.inv.app W) ≫ e.hom.app W := by simp
      _ = (b ≫ (productTest (@Etale) T).map a) ≫ e.hom.app W := by rw [hfac]
      _ = (b ≫ e.hom.app Y) ≫ (productFamilyEvaluation (@Etale) T).map a := by
        rw [Category.assoc, e.hom.naturality]
        simp only [Category.assoc]
  · exact X.smallEtaleTopology.pullback_stable _ (hF.cover_preserve hR)

/-- Products preserve the actual two-open pullback square. -/
theorem etaleOpenProductSquare_isPullback (U V : X.Opens) (T : X.Etale) :
    ((etaleOpenSquare U V).map (productFamilyEvaluation (@Etale) T)).IsPullback := by
  let : PreservesLimitsOfShape WalkingCospan (productFamilyEvaluation (@Etale) T) :=
    etaleProductFamilyEvaluation_preservesPullbacks T
  exact (etaleOpenSquare_isPullback U V).map _

/-- Original product tests preserve a literal two-arrow covering pair. -/
theorem etaleProductSquare_cover (Q : Square X.Etale)
    (hcover : Sieve.ofTwoArrows Q.f₂₄ Q.f₃₄ ∈ X.smallEtaleTopology Q.X₄)
    (T : X.Etale) :
    Sieve.ofTwoArrows ((productMap (@Etale) Q.f₂₄).app T)
      ((productMap (@Etale) Q.f₃₄).app T) ∈
        X.smallEtaleTopology ((productTest (@Etale) Q.X₄).obj T) := by
  have h := (etaleProductFamilyEvaluation_coverPreserving T).cover_preserve hcover
  rw [Sieve.ofTwoArrows, Sieve.functorPushforward_ofArrows] at h
  apply X.smallEtaleTopology.superset_covering ?_ h
  intro W g hg
  obtain ⟨j, a, rfl⟩ := Sieve.ofArrows.exists hg
  cases j
  · exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨WalkingPair.left, a, rfl⟩
  · exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨WalkingPair.right, a, rfl⟩

/-- The two original product-map inclusions cover on every original test. -/
theorem etaleOpenProductSquare_cover (U V : X.Opens) (T : X.Etale) :
    Sieve.ofTwoArrows
      ((productMap (@Etale) (etaleOpenSquare U V).f₂₄).app T)
      ((productMap (@Etale) (etaleOpenSquare U V).f₃₄).app T) ∈
        X.smallEtaleTopology ((productTest (@Etale) (etaleOpenSquare U V).X₄).obj T) :=
  etaleProductSquare_cover (etaleOpenSquare U V) (etaleOpenSquare_cover U V) T

/-- Actual small-etale base change preserves the literal two-arrow covering square. -/
theorem etaleSquare_baseChange_cover {Y : Scheme.{u}} (g : Y ⟶ X)
    (Q : Square X.Etale)
    (hcover : Sieve.ofTwoArrows Q.f₂₄ Q.f₃₄ ∈ X.smallEtaleTopology Q.X₄) :
    Sieve.ofTwoArrows (Q.map (siteBaseChange g)).f₂₄
      (Q.map (siteBaseChange g)).f₃₄ ∈
        Y.smallEtaleTopology (Q.map (siteBaseChange g)).X₄ := by
  have h := (siteBaseChange_coverPreserving g).cover_preserve hcover
  rw [Sieve.ofTwoArrows, Sieve.functorPushforward_ofArrows] at h
  apply Y.smallEtaleTopology.superset_covering ?_ h
  intro W a ha
  obtain ⟨j, b, rfl⟩ := Sieve.ofArrows.exists ha
  cases j
  · exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨WalkingPair.left, b, rfl⟩
  · exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨WalkingPair.right, b, rfl⟩

/-- The actual relative product-test square on an original etale square. -/
def etaleTestSquare (f : X ⟶ S) (Q : Square X.Etale) : Square (S.Etale ⥤ X.Etale) :=
  Q.map (productFamily (@Etale) ⋙
    (Functor.whiskeringLeft S.Etale X.Etale X.Etale).obj (siteBaseChange f))

/-- The square of original test functors for a source two-open cover. -/
abbrev etaleOpenTestSquare (f : X ⟶ S) (U V : X.Opens) : Square (S.Etale ⥤ X.Etale) :=
  etaleTestSquare f (etaleOpenSquare U V)

@[simp]
theorem etaleOpenTestSquare_X₁ (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).X₁ =
      siteBaseChange f ⋙ productTest (@Etale) ((opensToEtale X).obj (U ⊓ V)) := rfl

@[simp]
theorem etaleOpenTestSquare_X₂ (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).X₂ =
      siteBaseChange f ⋙ productTest (@Etale) ((opensToEtale X).obj U) := rfl

@[simp]
theorem etaleOpenTestSquare_X₃ (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).X₃ =
      siteBaseChange f ⋙ productTest (@Etale) ((opensToEtale X).obj V) := rfl

@[simp]
theorem etaleOpenTestSquare_X₄ (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).X₄ =
      siteBaseChange f ⋙ productTest (@Etale) ((opensToEtale X).obj (U ⊔ V)) := rfl

@[simp]
theorem etaleOpenTestSquare_f₁₂ (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).f₁₂ =
      Functor.whiskerLeft (siteBaseChange f)
        (productMap (@Etale) ((opensToEtale X).map (homOfLE inf_le_left))) := rfl

@[simp]
theorem etaleOpenTestSquare_f₁₃ (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).f₁₃ =
      Functor.whiskerLeft (siteBaseChange f)
        (productMap (@Etale) ((opensToEtale X).map (homOfLE inf_le_right))) := rfl

@[simp]
theorem etaleOpenTestSquare_f₂₄ (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).f₂₄ =
      Functor.whiskerLeft (siteBaseChange f)
        (productMap (@Etale) ((opensToEtale X).map (homOfLE le_sup_left))) := rfl

@[simp]
theorem etaleOpenTestSquare_f₃₄ (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).f₃₄ =
      Functor.whiskerLeft (siteBaseChange f)
        (productMap (@Etale) ((opensToEtale X).map (homOfLE le_sup_right))) := rfl

instance etaleOpenTestSquare_X₁_continuous (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).X₁.IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (siteBaseChange f)
    (etaleProductTest ((opensToEtale X).obj (U ⊓ V)))
    S.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology

instance etaleOpenTestSquare_X₂_continuous (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).X₂.IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (siteBaseChange f)
    (etaleProductTest ((opensToEtale X).obj U))
    S.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology

instance etaleOpenTestSquare_X₃_continuous (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).X₃.IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (siteBaseChange f)
    (etaleProductTest ((opensToEtale X).obj V))
    S.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology

instance etaleOpenTestSquare_X₄_continuous (f : X ⟶ S) (U V : X.Opens) :
    (etaleOpenTestSquare f U V).X₄.IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (siteBaseChange f)
    (etaleProductTest ((opensToEtale X).obj (U ⊔ V)))
    S.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology

instance etaleTestSquare_X₁_continuous (f : X ⟶ S) (Q : Square X.Etale) :
    (etaleTestSquare f Q).X₁.IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (siteBaseChange f) (etaleProductTest Q.X₁)
    S.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology

instance etaleTestSquare_X₂_continuous (f : X ⟶ S) (Q : Square X.Etale) :
    (etaleTestSquare f Q).X₂.IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (siteBaseChange f) (etaleProductTest Q.X₂)
    S.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology

instance etaleTestSquare_X₃_continuous (f : X ⟶ S) (Q : Square X.Etale) :
    (etaleTestSquare f Q).X₃.IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (siteBaseChange f) (etaleProductTest Q.X₃)
    S.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology

instance etaleTestSquare_X₄_continuous (f : X ⟶ S) (Q : Square X.Etale) :
    (etaleTestSquare f Q).X₄.IsContinuous S.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_comp (siteBaseChange f) (etaleProductTest Q.X₄)
    S.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology

/-- Each evaluated relative square retains the actual pullback. -/
theorem etaleTestSquare_isPullback (f : X ⟶ S) (Q : Square X.Etale)
    (hQ : Q.IsPullback) (T : S.Etale) :
    ((etaleTestSquare f Q).map ((CategoryTheory.evaluation _ _).obj T)).IsPullback := by
  let : PreservesLimitsOfShape WalkingCospan
      (productFamilyEvaluation (@Etale) ((siteBaseChange f).obj T)) :=
    etaleProductFamilyEvaluation_preservesPullbacks _
  exact hQ.map (productFamilyEvaluation (@Etale) ((siteBaseChange f).obj T))

/-- Each evaluated relative square retains the original covering pair. -/
theorem etaleTestSquare_cover (f : X ⟶ S) (Q : Square X.Etale)
    (hcover : Sieve.ofTwoArrows Q.f₂₄ Q.f₃₄ ∈ X.smallEtaleTopology Q.X₄)
    (T : S.Etale) :
    Sieve.ofTwoArrows ((etaleTestSquare f Q).f₂₄.app T)
      ((etaleTestSquare f Q).f₃₄.app T) ∈
        X.smallEtaleTopology ((etaleTestSquare f Q).X₄.obj T) :=
  etaleProductSquare_cover Q hcover ((siteBaseChange f).obj T)

instance etaleTestSquare_f₂₄_app_mono (f : X ⟶ S) (Q : Square X.Etale)
    [Mono Q.f₂₄] (T : S.Etale) : Mono ((etaleTestSquare f Q).f₂₄.app T) :=
  inferInstanceAs (Mono ((productMap (@Etale) Q.f₂₄).app ((siteBaseChange f).obj T)))

instance etaleTestSquare_f₃₄_app_mono (f : X ⟶ S) (Q : Square X.Etale)
    [Mono Q.f₃₄] (T : S.Etale) : Mono ((etaleTestSquare f Q).f₃₄.app T) :=
  inferInstanceAs (Mono ((productMap (@Etale) Q.f₃₄).app ((siteBaseChange f).obj T)))

/-- Every evaluated relative square is a pullback, in the original orientation. -/
theorem etaleOpenTestSquare_isPullback (f : X ⟶ S) (U V : X.Opens) (T : S.Etale) :
    ((etaleOpenTestSquare f U V).map ((CategoryTheory.evaluation _ _).obj T)).IsPullback :=
  etaleOpenProductSquare_isPullback U V ((siteBaseChange f).obj T)

/-- Every evaluated relative square has its original covering pair. -/
theorem etaleOpenTestSquare_cover (f : X ⟶ S) (U V : X.Opens) (T : S.Etale) :
    Sieve.ofTwoArrows ((etaleOpenTestSquare f U V).f₂₄.app T)
      ((etaleOpenTestSquare f U V).f₃₄.app T) ∈
        X.smallEtaleTopology ((etaleOpenTestSquare f U V).X₄.obj T) :=
  etaleOpenProductSquare_cover U V ((siteBaseChange f).obj T)

instance etaleOpenTestSquare_f₂₄_app_mono (f : X ⟶ S) (U V : X.Opens) (T : S.Etale) :
    Mono ((etaleOpenTestSquare f U V).f₂₄.app T) := by
  let : Mono (etaleOpenSquare U V).f₂₄ := etaleOpenSquare_f₂₄_mono U V
  exact inferInstanceAs (Mono ((productMap (@Etale) (etaleOpenSquare U V).f₂₄).app
    ((siteBaseChange f).obj T)))

instance etaleOpenTestSquare_f₃₄_app_mono (f : X ⟶ S) (U V : X.Opens) (T : S.Etale) :
    Mono ((etaleOpenTestSquare f U V).f₃₄.app T) := by
  let : Mono (etaleOpenSquare U V).f₃₄ := etaleOpenSquare_f₃₄_mono U V
  exact inferInstanceAs (Mono ((productMap (@Etale) (etaleOpenSquare U V).f₃₄).app
    ((siteBaseChange f).obj T)))

end AlgebraicGeometry.Scheme

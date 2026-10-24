/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Canonical compatibility with the bounded-below right-derived functor

The two functors on the native bounded-below derived category are compared
by the uniqueness of right-derived functors. Both use the original cochain
localization units. The defining equation identifies these units, rather than
choosing unrelated isomorphisms of their values.
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]
  (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
  (η : 𝟭 (CochainComplex C ℤ) ⟶ R)
  (hη : ∀ K, QuasiIso (η.app K))
  (hR : ∀ K, (R.obj K).IsKInjective)

/-- The bounded-below derived unit, viewed in the original full derived category. -/
def rightDerivedFunctorPlusFullUnit :
    (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
  whiskerRight F.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι ≫
    (associator _ _ _).hom

/-- The original unbounded unit restricted to bounded-below complexes. The
 native plus/full inclusion squares are definitionally the original squares. -/
def rightDerivedFunctorOfKInjectiveReplacementPlusUnit :
    (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙
        (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR) where
  app K := (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app K.obj
  naturality {_ _} f :=
    (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).naturality f.hom

omit [HasDerivedCategory C] [EnoughInjectives C] in
/-- Bounded-below injectives derive the degreewise functor viewed in the full target. -/
lemma plusFull_derives :
    (CochainComplex.Plus.localizerMorphism C).Derives
      ((F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ DerivedCategory.Plus.ι) :=
  MorphismProperty.IsInvertedBy.of_comp _ _
    (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus F)
    DerivedCategory.Plus.ι

/-- The original bounded-below functor remains right-derived after the full inclusion. -/
lemma plusFull_isRightDerivedFunctor :
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
      F.rightDerivedFunctorPlusFullUnit (CochainComplex.Plus.quasiIso C) := by
  apply (plusFull_derives F).isRightDerivedFunctor_of_isIso
  intro I
  dsimp [rightDerivedFunctorPlusFullUnit]
  infer_instance

/-- The unbounded functor restricted to bounded-below sources has the same derived property. -/
lemma unboundedPlus_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR)
      (F.rightDerivedFunctorOfKInjectiveReplacementPlusUnit R η hη hR)
        (CochainComplex.Plus.quasiIso C) := by
  apply (plusFull_derives F).isRightDerivedFunctor_of_isIso
  intro I
  change IsIso ((F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app
    (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj I.obj))
  infer_instance

/-- The canonical bounded-below/unbounded comparison, determined by the
 original right-derived localization units. -/
def rightDerivedFunctorOfKInjectiveReplacementPlusIso :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR := by
  have := plusFull_isRightDerivedFunctor F
  have := unboundedPlus_isRightDerivedFunctor F R η hη hR
  exact rightDerivedUnique _ _ F.rightDerivedFunctorPlusFullUnit
    (F.rightDerivedFunctorOfKInjectiveReplacementPlusUnit R η hη hR)
    (CochainComplex.Plus.quasiIso C)

/-- The canonical comparison identifies the original two derived units. -/
@[reassoc]
lemma rightDerivedFunctorOfKInjectiveReplacementPlusIso_unit :
    F.rightDerivedFunctorPlusFullUnit ≫
      whiskerLeft DerivedCategory.Plus.Q
        (F.rightDerivedFunctorOfKInjectiveReplacementPlusIso R η hη hR).hom =
      F.rightDerivedFunctorOfKInjectiveReplacementPlusUnit R η hη hR := by
  have := plusFull_isRightDerivedFunctor F
  have := unboundedPlus_isRightDerivedFunctor F R η hη hR
  change F.rightDerivedFunctorPlusFullUnit ≫
    whiskerLeft DerivedCategory.Plus.Q
      (rightDerivedNatTrans _ _ F.rightDerivedFunctorPlusFullUnit
        (F.rightDerivedFunctorOfKInjectiveReplacementPlusUnit R η hη hR)
        (CochainComplex.Plus.quasiIso C) (𝟙 _)) = _
  simp

/-- On every actual bounded-below complex, the comparison carries its native
 bounded-below unit to the same unbounded unit. -/
@[reassoc]
lemma rightDerivedFunctorOfKInjectiveReplacementPlusIso_unit_app
    (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      (F.rightDerivedFunctorOfKInjectiveReplacementPlusIso R η hη hR).hom.app
        (DerivedCategory.Plus.Q.obj K) =
      (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app K.obj := by
  simpa [rightDerivedFunctorPlusFullUnit,
    rightDerivedFunctorOfKInjectiveReplacementPlusUnit] using
    NatTrans.congr_app (F.rightDerivedFunctorOfKInjectiveReplacementPlusIso_unit R η hη hR) K

end CategoryTheory.Functor

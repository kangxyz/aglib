/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Derivability
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-!
# The native unbounded right-derived functor from a supplied replacement

The functor takes values in the existing `DerivedCategory`. Its unit is the
universal localization comparison. Computation by any supplied K-injective
resolution retains the actual augmentation, rather than an arbitrary objectwise
isomorphism. The replacement functor is not assumed additive.

Replacement existence is an explicit input in this leaf.
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]
  (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
  (η : 𝟭 (CochainComplex C ℤ) ⟶ R)
  (hη : ∀ K, QuasiIso (η.app K))
  (hR : ∀ K, (R.obj K).IsKInjective)

/-- The unbounded right-derived functor on the native derived categories,
 constructed from an explicit functorial K-injective replacement. -/
@[no_expose]
def rightDerivedFunctorOfKInjectiveReplacement : DerivedCategory C ⥤ DerivedCategory D :=
  letI := CochainComplex.hasPointwiseRightDerivedFunctor_of_kInjectiveReplacement R η hη hR F
  (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))

/-- The original universal localization unit of the unbounded right-derived functor. -/
@[no_expose]
def rightDerivedFunctorOfKInjectiveReplacementUnit :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR :=
  letI := CochainComplex.hasPointwiseRightDerivedFunctor_of_kInjectiveReplacement R η hη hR F
  (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).totalRightDerivedUnit
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))

instance rightDerivedFunctorOfKInjectiveReplacement_isRightDerivedFunctor :
    (F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR).IsRightDerivedFunctor
      (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR)
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  dsimp only [rightDerivedFunctorOfKInjectiveReplacement,
    rightDerivedFunctorOfKInjectiveReplacementUnit]
  infer_instance

/-- Shift compatibility comes from the universal derived comparison, not from
 additivity or shift compatibility of the replacement functor. -/
noncomputable instance rightDerivedFunctorOfKInjectiveReplacementCommShift :
    (F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR).CommShift ℤ :=
  IsRightDerivedFunctor.commShift _
    (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR)
    (HomologicalComplex.quasiIso C (.up ℤ)) ℤ

instance rightDerivedFunctorOfKInjectiveReplacementUnit_commShift :
    (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).CommShift ℤ :=
  IsRightDerivedFunctor.natTrans_commShift _
    (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR)
    (HomologicalComplex.quasiIso C (.up ℤ)) ℤ

instance isIso_rightDerivedFunctorOfKInjectiveReplacementUnit_app
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app I) := by
  have := CochainComplex.isRightDerivabilityStructure_of_kInjectiveReplacement R η hη hR
  exact (CochainComplex.kInjectiveLocalizerMorphism_derives F).isIso_of_isRightDerivedFunctor
    (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR) ⟨I, inferInstanceAs I.IsKInjective⟩

/-- Computation on a specified original quasi-isomorphism into a K-injective complex. -/
def rightDerivedFunctorOfKInjectiveReplacementObjIso
    {K I : CochainComplex C ℤ} (i : K ⟶ I) [QuasiIso i] [I.IsKInjective] :
    (F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) :=
  (F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR).mapIso
    (asIso (DerivedCategory.Q.map i)) ≪≫
      (asIso ((F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app I)).symm

/-- The computation isomorphism identifies the universal unit with the image
 of the original resolution arrow. -/
@[reassoc]
lemma rightDerivedFunctorOfKInjectiveReplacementUnit_app_comp_objIso_hom
    {K I : CochainComplex C ℤ} (i : K ⟶ I) [QuasiIso i] [I.IsKInjective] :
    (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app K ≫
      (F.rightDerivedFunctorOfKInjectiveReplacementObjIso R η hη hR i).hom =
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map i) := by
  dsimp only [rightDerivedFunctorOfKInjectiveReplacementObjIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  have h := (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).naturality i
  simp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h]
  simp

end CategoryTheory.Functor

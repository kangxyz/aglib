/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Representatives
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Derivability from an explicit functorial K-injective replacement

The full subcategory consists of the original cochain complexes that are
K-injective. An actual replacement functor and its natural quasi-isomorphism
make its inclusion a native right derivability structure. No additivity of
the replacement functor is required. Every additive functor can then be
derived on the existing unbounded derived category.

This leaf is a conditional consumer: it does not prove that replacements exist.
-/

@[expose] public section

universe u v u' v' w'

open CategoryTheory

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The property of being a native K-injective cochain complex. -/
def kInjectiveObjects : ObjectProperty (CochainComplex C ℤ) := IsKInjective

/-- The inclusion of K-injective complexes, with the inherited quasi-isomorphisms. -/
abbrev kInjectiveLocalizerMorphism : LocalizerMorphism
    ((HomologicalComplex.quasiIso C (.up ℤ)).inverseImage (kInjectiveObjects C).ι)
    (HomologicalComplex.quasiIso C (.up ℤ)) where
  functor := (kInjectiveObjects C).ι
  map := by rfl

variable {C}
  (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
  (η : 𝟭 (CochainComplex C ℤ) ⟶ R)
  (hη : ∀ K, QuasiIso (η.app K))
  (hR : ∀ K, (R.obj K).IsKInjective)

include R η hη hR in
/-- An explicit functorial K-injective replacement gives the native right
 derivability structure; its original augmentation is used unchanged. -/
lemma isRightDerivabilityStructure_of_kInjectiveReplacement :
    (kInjectiveLocalizerMorphism C).IsRightDerivabilityStructure :=
  (kInjectiveLocalizerMorphism C).isRightDerivabilityStructure_of_functorial_resolutions
    (ρ := (kInjectiveObjects C).lift R hR) η hη rfl

include R η hη hR in
/-- The same replacement resolves actual arrows functorially. -/
lemma hasRightResolutions_arrow_of_kInjectiveReplacement :
    (kInjectiveLocalizerMorphism C).arrow.HasRightResolutions :=
  (kInjectiveLocalizerMorphism C).hasRightResolutions_arrow_of_functorial_resolutions
    (ρ := (kInjectiveObjects C).lift R hR) η hη

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

/-- Every additive functor inverts quasi-isomorphisms between K-injective
 complexes after the original target localization. -/
lemma kInjectiveLocalizerMorphism_derives :
    (kInjectiveLocalizerMorphism C).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro K L f hf
  have : K.obj.IsKInjective := K.property
  have : L.obj.IsKInjective := L.property
  have : QuasiIso f.hom := hf
  have := quasiIso_map_of_isKInjective F f.hom
  change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

include R η hη hR in
/-- Pointwise right-derived existence obtained from the supplied actual
 replacement, not from an assumed replacement-existence class. -/
lemma hasPointwiseRightDerivedFunctor_of_kInjectiveReplacement :
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseRightDerivedFunctor
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  have := isRightDerivabilityStructure_of_kInjectiveReplacement R η hη hR
  exact (kInjectiveLocalizerMorphism_derives F).hasPointwiseRightDerivedFunctor

end CochainComplex

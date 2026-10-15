/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Equivalence
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Abelian.Transfer
/-!
# Genuine small models of exact categories

Under the explicit `EssentiallySmall` hypothesis, the actual categorical small
model inherits additive, abelian and exact structures. Its chosen equivalence
functors are exact, and actual small presentations admit an exact comparison
that preserves and reflects admissible maps. The small universe is retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' u u'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SmallModel
variable (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C]

instance preadditive [Preadditive C] : Preadditive (SmallModel.{w} C) :=
  Preadditive.ofFullyFaithful (equivSmallModel.{w} C).fullyFaithfulInverse

instance inverseAdditive [Preadditive C] : (equivSmallModel.{w} C).inverse.Additive :=
  (equivSmallModel.{w} C).symm.fullyFaithfulFunctor.additive_ofFullyFaithful

instance symmFunctorAdditive [Preadditive C] :
    (equivSmallModel.{w} C).symm.functor.Additive :=
  inverseAdditive C

instance functorAdditive [Preadditive C] : (equivSmallModel.{w} C).functor.Additive :=
  (equivSmallModel.{w} C).symm.additive_inverse_of_FullyFaithful

instance hasFiniteProducts [HasFiniteProducts C] : HasFiniteProducts (SmallModel.{w} C) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (equivSmallModel.{w} C).inverse

instance hasFiniteBiproducts [Preadditive C] [HasFiniteBiproducts C] :
    HasFiniteBiproducts (SmallModel.{w} C) := .of_hasFiniteProducts

/-- Abelian structure is also transported from the actual original category. -/
instance abelian [Abelian C] : Abelian (SmallModel.{w} C) :=
  abelianOfEquivalence (equivSmallModel.{w} C).inverse

end CategoryTheory.SmallModel

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [EssentiallySmall.{w} C] (E : ExactStructure C)

/-- The exact structure on the actual categorical small model. -/
def smallModel : ExactStructure (SmallModel.{w} C) :=
  E.ofEquivalence (equivSmallModel.{w} C).symm

/-- The small-model realization into the original category is genuinely exact. -/
def smallModelToOriginal : ExactFunctor E.smallModel E :=
  E.equivalenceExactFunctor (equivSmallModel.{w} C).symm

/-- The inverse, from the original category to its small model, is exact. -/
def originalToSmallModel : ExactFunctor E E.smallModel :=
  E.equivalenceInverseExactFunctor (equivSmallModel.{w} C).symm

@[simp]
lemma smallModel_conflation (S : ShortComplex (SmallModel.{w} C)) :
    E.smallModel.conflation S ↔ E.conflation (S.map (equivSmallModel.{w} C).inverse) := Iff.rfl

@[simp]
lemma smallModelToOriginal_toFunctor :
    E.smallModelToOriginal.toFunctor = (equivSmallModel.{w} C).inverse := rfl

@[simp]
lemma originalToSmallModel_toFunctor :
    E.originalToSmallModel.toFunctor = (equivSmallModel.{w} C).functor := rfl

instance smallModelToOriginal_isEquivalence : E.smallModelToOriginal.toFunctor.IsEquivalence :=
  inferInstanceAs (equivSmallModel.{w} C).inverse.IsEquivalence

instance originalToSmallModel_isEquivalence : E.originalToSmallModel.toFunctor.IsEquivalence :=
  inferInstanceAs (equivSmallModel.{w} C).functor.IsEquivalence

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- An exact functor between possibly large categories induces an actual exact
functor between their small models, using the two equivalence functors. -/
def smallModel (F : ExactFunctor EC ED) : ExactFunctor EC.smallModel ED.smallModel :=
  (EC.smallModelToOriginal.comp F).comp ED.originalToSmallModel

end CategoryTheory.ExactCategory.ExactFunctor

namespace CategoryTheory.ExactCategory.ExactStructure
section Presentations
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)
  {S T : Type w} [Category.{w} S] [Category.{w} T]
  [Preadditive S] [Preadditive T] [HasFiniteBiproducts S] [HasFiniteBiproducts T]
  (e : S ≌ C) (f : T ≌ C) [e.functor.Additive] [f.functor.Additive]

/-- The genuine exact comparison between two actual small presentations. -/
def presentationComparison : ExactFunctor (E.ofEquivalence e) (E.ofEquivalence f) :=
  (E.equivalenceExactFunctor e).comp (E.equivalenceInverseExactFunctor f)

instance presentationComparison_isEquivalence :
    (E.presentationComparison e f).toFunctor.IsEquivalence :=
  inferInstanceAs (e.functor ⋙ f.inverse).IsEquivalence

lemma presentationComparison_map_inflation_iff {X Y : S} (i : X ⟶ Y) :
    (E.ofEquivalence f).inflation ((E.presentationComparison e f).toFunctor.map i) ↔
      (E.ofEquivalence e).inflation i := by
  rw [E.ofEquivalence_inflation_iff f, E.ofEquivalence_inflation_iff e]
  change E.inflation (f.functor.map (f.inverse.map (e.functor.map i))) ↔
    E.inflation (e.functor.map i)
  have h := f.counitIso.hom.naturality (e.functor.map i)
  dsimp at h
  constructor
  · intro hi
    have hi' := E.inflation_comp _ _ hi (E.inflation_of_iso (f.counitIso.app _))
    simp only [Iso.app_hom] at hi'
    rw [h] at hi'
    have hi'' := E.inflation_comp _ _ (E.inflation_of_iso (f.counitIso.app _).symm) hi'
    simpa using hi''
  · intro hi
    have hi' := E.inflation_comp _ _ (E.inflation_of_iso (f.counitIso.app _)) hi
    simp only [Iso.app_hom] at hi'
    rw [← h] at hi'
    have hi'' := E.inflation_comp _ _ hi' (E.inflation_of_iso (f.counitIso.app _).symm)
    simpa using hi''

lemma presentationComparison_map_deflation_iff {X Y : S} (p : X ⟶ Y) :
    (E.ofEquivalence f).deflation ((E.presentationComparison e f).toFunctor.map p) ↔
      (E.ofEquivalence e).deflation p := by
  rw [E.ofEquivalence_deflation_iff f, E.ofEquivalence_deflation_iff e]
  change E.deflation (f.functor.map (f.inverse.map (e.functor.map p))) ↔
    E.deflation (e.functor.map p)
  have h := f.counitIso.hom.naturality (e.functor.map p)
  dsimp at h
  constructor
  · intro hp
    have hp' := E.deflation_comp _ _ hp (E.deflation_of_iso (f.counitIso.app _))
    simp only [Iso.app_hom] at hp'
    rw [h] at hp'
    have hp'' := E.deflation_comp _ _ (E.deflation_of_iso (f.counitIso.app _).symm) hp'
    simpa using hp''
  · intro hp
    have hp' := E.deflation_comp _ _ (E.deflation_of_iso (f.counitIso.app _)) hp
    simp only [Iso.app_hom] at hp'
    rw [← h] at hp'
    have hp'' := E.deflation_comp _ _ hp' (E.deflation_of_iso (f.counitIso.app _).symm)
    simpa using hp''

end Presentations
end CategoryTheory.ExactCategory.ExactStructure

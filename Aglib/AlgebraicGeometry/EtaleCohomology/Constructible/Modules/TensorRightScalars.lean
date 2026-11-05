/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Aglib.Algebra.Category.ModuleCat.FunctorTensorRightScalarsAdjunction
public import Aglib.Algebra.Category.ModuleCat.FunctorTensorRightScalarsFinite
public import Aglib.CategoryTheory.Sites.Pullback.SheafifiedLeftAdjointCoefficients

/-! # Constructibility under the original right-factor tensor

The original strata and étale charts are unchanged. Their original finite
constant values are tensored with the given finite-type right module. The
actual sheafified coefficient adjunction supplies all inverse-image and
constant comparisons; finite stalks alone are not used as a criterion.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r l

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R] (Λ : Type l) [Ring Λ]
  (M : ModuleCat.{u + 1} R) [Module Λ M] [SMulCommClass Λ R M]

/-- The actual coefficient tensor followed by the original sheafification. -/
abbrev tensorRightScalarsSheaf (X : Scheme.{u}) : ModuleSheaf R X ⥤ ModuleSheaf Λ X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology
    (ModuleCat.tensorRightScalarsFunctor.{r, l, u + 1, u + 1} R Λ M)

/-- The original inverse images commute with this sheafified coefficient functor. -/
def tensorRightScalarsSheafPullbackIso {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleInverseImage R f ⋙ tensorRightScalarsSheaf R Λ M S ≅
      tensorRightScalarsSheaf R Λ M X ⋙ moduleInverseImage Λ f :=
  Functor.sheafPullbackSheafifiedLeftAdjointIso (siteBaseChange f)
    X.smallEtaleTopology S.smallEtaleTopology
    (ModuleCat.tensorRightScalarsFunctor.{r, l, u + 1, u + 1} R Λ M)
    (ModuleCat.homRightScalarsFunctor.{r, l, u + 1, u + 1} R Λ M)
    (ModuleCat.tensorRightScalarsAdjunction.{r, l, u + 1, u + 1} R Λ M)

/-- An original constant value becomes its original tensor, not a newly chosen module. -/
def tensorRightScalarsSheafConstantIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
        tensorRightScalarsSheaf R Λ M X ≅
      ModuleCat.tensorRightScalarsFunctor.{r, l, u + 1, u + 1} R Λ M ⋙
        constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  constantSheafSheafifiedLeftAdjointIso X.smallEtaleTopology
    (ModuleCat.tensorRightScalarsFunctor.{r, l, u + 1, u + 1} R Λ M)
    (ModuleCat.homRightScalarsFunctor.{r, l, u + 1, u + 1} R Λ M)
    (ModuleCat.tensorRightScalarsAdjunction.{r, l, u + 1, u + 1} R Λ M)

variable [Finite R] [Module.Finite Λ M]

/-- Retain every original chart and its covering map, tensoring only its actual value. -/
def FiniteTypeLocalTrivialization.tensorRightScalars {X : Scheme.{u}}
    {F : ModuleSheaf R X} (t : FiniteTypeLocalTrivialization F) :
    FiniteTypeLocalTrivialization ((tensorRightScalarsSheaf R Λ M X).obj F) where
  index := t.index
  chart := t.chart
  covers := t.covers
  value i := (ModuleCat.tensorRightScalarsFunctor.{r, l, u + 1, u + 1} R Λ M).obj (t.value i)
  finite_value i := by
    let := t.finite_value i
    let : Finite (t.value i) := Module.finite_of_finite R
    exact ModuleCat.tensorRightScalars_finite R Λ M (t.value i)
  trivialization i :=
    ((tensorRightScalarsSheafPullbackIso R Λ M (t.chart i).hom).app F).symm ≪≫
      (tensorRightScalarsSheaf R Λ M (t.chart i).left).mapIso (t.trivialization i) ≪≫
      (tensorRightScalarsSheafConstantIso R Λ M (t.chart i).left).app (t.value i)

/-- Finite-type local constancy follows from the same actual charts. -/
theorem isFiniteTypeLocallyConstant_tensorRightScalars {X : Scheme.{u}}
    {F : ModuleSheaf R X} (hF : IsFiniteTypeLocallyConstant F) :
    IsFiniteTypeLocallyConstant ((tensorRightScalarsSheaf R Λ M X).obj F) := by
  obtain ⟨t⟩ := hF
  exact ⟨t.tensorRightScalars R Λ M⟩

/-- Keep the same finite locally closed partition and its actual immersions. -/
def ConstructiblePartition.tensorRightScalars {X : Scheme.{u}}
    {F : ModuleSheaf R X} (t : ConstructiblePartition F) :
    ConstructiblePartition ((tensorRightScalarsSheaf R Λ M X).obj F) where
  toFiniteLocallyClosedPartition := t.toFiniteLocallyClosedPartition
  locally_constant i :=
    (isFiniteTypeLocallyConstant_iff_of_iso
      ((tensorRightScalarsSheafPullbackIso R Λ M (t.inclusion i)).app F)).mp
        (isFiniteTypeLocallyConstant_tensorRightScalars R Λ M (t.locally_constant i))

/-- Original finite-ring module constructibility gives finite-type constructibility
for the actual tensor with the given finite-type coefficient module. -/
theorem isConstructible_tensorRightScalars {X : Scheme.{u}}
    {F : ModuleSheaf R X} (hF : IsConstructible F) :
    IsConstructible ((tensorRightScalarsSheaf R Λ M X).obj F) := by
  intro U
  obtain ⟨t⟩ := hF U
  exact ⟨(t.tensorRightScalars R Λ M).ofIso
    ((tensorRightScalarsSheafPullbackIso R Λ M U.1.ι).app F)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

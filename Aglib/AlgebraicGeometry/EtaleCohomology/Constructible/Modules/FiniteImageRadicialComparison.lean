/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.SurjectiveUnit
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GeometricPoints
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.ImageMates

/-! # Original finite radicial image adjunction comparisons

Finite universally injective maps have singleton geometric fibers wherever a
lift exists. The original finite evaluation coordinate gives the original
counit, and surjectivity additionally gives the original unit. These are
adjunction comparisons, not a claim of constructible chart descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

open CoefficientStalkBaseChange

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [UniversallyInjective f]

/-- Actual geometric lifts through a universally injective map are unique. -/
@[instance_reducible] def finiteRadicialUniqueLift {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (hy : y ≫ f = s) :
    Unique {z : Spec (.of Ω) ⟶ Y // z ≫ f = s} where
  default := ⟨y, hy⟩
  uniq z := by
    apply Subtype.ext
    have hi : ∀ (K : Type u) [Field K],
        Function.Injective (fun a : Spec (.of K) ⟶ Y => a ≫ f) :=
      ((tfae_universallyInjective f).out 1 2).mp ‹UniversallyInjective f›
    exact hi Ω (z.property.trans hy.symm)

/-- The original abelian unit for a finite surjective radicial morphism is
invertible on all original geometric stalks. -/
theorem finiteRadicial_abelianUnit_isIso [Surjective f]
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((inverseImageAdjunction f).unit.app F) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 X)
  intro Ω _ _ s _
  obtain ⟨y, hy⟩ := Scheme.Finite.GeometricPoints.exists_lift f s
  let := finiteRadicialUniqueLift f s y hy
  exact Finite.unit_stalk_isIso_of_unique f s F

/-- The original abelian counit for a finite radicial map is invertible,
without requiring that the map be surjective. -/
theorem finiteRadicial_abelianCounit_isIso
    (F : AbelianSheaf.{u, u + 1} Y) :
    IsIso ((inverseImageAdjunction f).counit.app F) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks (𝟙 Y)
  intro Ω _ _ y _
  let := finiteRadicialUniqueLift f (y ≫ f) y rfl
  have he : IsIso (pointedDirectImageEvaluation f y (y ≫ f) rfl F) :=
    Finite.directImageEvaluation_isIso_of_unique f (y ≫ f) F
  have := pointedStalkUnit_isIso f y (y ≫ f) rfl ((directImage f).obj F)
  change IsIso (pointedStalkUnit f y ((directImage f).obj F) (y ≫ f) rfl ≫
    (pointSmallEtale y).sheafFiber.map ((inverseImageAdjunction f).counit.app F)) at he
  exact (isIso_comp_left_iff _ _).mp he

variable (R : Type r) [CommRing R]

/-- The actual module unit is invertible for finite surjective radicial maps,
by the proved scalar-forgetting unit equation. -/
theorem finiteRadicial_moduleUnit_isIso [Surjective f] (F : ModuleSheaf R X) :
    IsIso ((moduleImageAdjunction R f).unit.app F) := by
  have : IsIso ((inverseImageAdjunction f).unit.app ((moduleUnderlying R X).obj F)) :=
    finiteRadicial_abelianUnit_isIso f _
  have h : IsIso ((moduleUnderlying R X).map ((moduleImageAdjunction R f).unit.app F) ≫
      (directImage f).map ((moduleInverseImageUnderlyingIso R f).hom.app F)) :=
    (ModuleCat.Sheaf.pullbackUnderlyingIso_unit R (siteBaseChange f)
      X.smallEtaleTopology Y.smallEtaleTopology F).symm ▸ inferInstance
  have : IsIso ((moduleUnderlying R X).map ((moduleImageAdjunction R f).unit.app F)) :=
    (isIso_comp_right_iff _ ((directImage f).map
      ((moduleInverseImageUnderlyingIso R f).hom.app F))).mp h
  exact isIso_of_reflects_iso _ (moduleUnderlying R X)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Unit
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.OverMap
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Exact native restriction of module sheaves

The functors here are Mathlib's original ringed-site pushforwards. Finite
limits are detected on underlying presheaves. For slice restrictions,
finite colimits follow from the original over-site adjunctions. Neither
argument asserts that forgetting scalars or restricting preserves injectives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u' v' r m w

namespace SheafOfModules

section Continuous

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.IsContinuous F J K]
  {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)

/-- Scalar forgetting commutes with the original ringed-site pushforward. -/
def pushforwardCompToSheaf :
    pushforward.{m} φ ⋙ toSheaf S ≅
      toSheaf R ⋙ F.sheafPushforwardContinuous AddCommGrpCat.{m} J K :=
  Iso.refl _

instance pushforward_additive : (pushforward.{m} φ).Additive where
  map_add := by intros; rfl

/-- Native ringed-site pushforward preserves finite limits, computed on presheaves. -/
instance pushforward_preservesFiniteLimits : PreservesFiniteLimits (pushforward.{m} φ) := by
  let I := toSheaf.{m} S ⋙ sheafToPresheaf J AddCommGrpCat.{m}
  have : PreservesFiniteLimits (pushforward.{m} φ ⋙ I) := by
    change PreservesFiniteLimits
      ((toSheaf.{m} R ⋙ sheafToPresheaf K AddCommGrpCat.{m}) ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{m}).obj F.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (pushforward.{m} φ) I

end Continuous

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r})

instance overFunctor_additive (U : C) : (overFunctor.{m} R U).Additive :=
  inferInstanceAs (pushforward.{m} (𝟙 (R.over U))).Additive

instance overFunctor_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits (overFunctor.{m} R U) :=
  inferInstanceAs (PreservesFiniteLimits (pushforward.{m} (𝟙 (R.over U))))

instance overFunctor_preservesFiniteColimits [HasBinaryProducts C] (U : C) :
    PreservesFiniteColimits (overFunctor.{m} R U) :=
  inferInstanceAs (PreservesFiniteColimits (pushforward.{m} (𝟙 (R.over U))))

instance overMap_additive {U V : C} (f : U ⟶ V) : (overMap.{m} R f).Additive :=
  inferInstanceAs (pushforward.{m} (F := Over.map f)
    (Sheaf.pushforwardOverMapIso R f).inv).Additive

instance overMap_preservesFiniteLimits {U V : C} (f : U ⟶ V) :
    PreservesFiniteLimits (overMap.{m} R f) :=
  inferInstanceAs (PreservesFiniteLimits (pushforward.{m} (F := Over.map f)
    (Sheaf.pushforwardOverMapIso R f).inv))

instance overMap_preservesFiniteColimits [HasPullbacks C]
    {U V : C} (f : U ⟶ V) : PreservesFiniteColimits (overMap.{m} R f) := by
  infer_instance

/-- The restriction/forgetting square uses the native abelian restriction. -/
def overFunctorCompToSheaf (U : C) :
    overFunctor.{m} R U ⋙ toSheaf (R.over U) ≅
      toSheaf R ⋙ J.overPullback AddCommGrpCat.{m} U :=
  pushforwardCompToSheaf (𝟙 (R.over U))

/-- The square for a map of slice objects uses the unchanged native functors. -/
def overMapCompToSheaf {U V : C} (f : U ⟶ V) :
    overMap.{m} R f ⋙ toSheaf (R.over U) ≅
      toSheaf (R.over V) ⋙ Sheaf.SliceCohomology.overMapRestriction J f :=
  pushforwardCompToSheaf (Sheaf.pushforwardOverMapIso R f).inv

/-- Native restriction carries the genuine lifted rank-one module to rank one. -/
def overFunctorLiftedUnitIso (U : C) :
    (overFunctor.{max r w} R U).obj (liftedUnit.{u, v, w, r} R) ≅
      liftedUnit.{max u v, v, w, r} (R.over U) :=
  Iso.refl _

/-- Lifted-universe version of the native `overMapUnitIso`. -/
def overMapLiftedUnitIso {U V : C} (f : U ⟶ V) :
    (overMap.{max r w} R f).obj (liftedUnit.{max u v, v, w, r} (R.over V)) ≅
      liftedUnit.{max u v, v, w, r} (R.over U) :=
  Iso.refl _

end SheafOfModules

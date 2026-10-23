/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ShortExactComparison
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Injectivity of original comparison at an exact coefficient colimit

The common-value-universe colimit functor must preserve monomorphisms, and
both original Ext functors must preserve the supplied coefficient cocone.
Then the actual comparison at the point is injective if all its original
stage comparisons are injective. Independent Ext universes are retained
by the same native `ULift` natural transformation used for bijectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : C} {A : D} (a : A ⟶ F.obj X)

/-- Exact colimits transport injectivity for the actual original comparison on
coefficient images, with both cohomological preservation conditions explicit. -/
theorem Functor.extPrecompMap_injective_on_image_of_isColimit
    {B : Type*} [Category B] (U : B ⥤ C)
    {I : Type*} [Category I] (K : I ⥤ B) (c : Cocone K) (hc : IsColimit c) (n : ℕ)
    [HasColimitsOfShape I AddCommGrpCat.{max w w'}]
    [Functor.PreservesMonomorphisms
      (colim : (I ⥤ AddCommGrpCat.{max w w'}) ⥤ AddCommGrpCat.{max w w'})]
    [PreservesColimit K (U ⋙ extFunctorObj X n)]
    [PreservesColimit K (U ⋙ F ⋙ extFunctorObj A n)]
    (hK : ∀ i, Function.Injective (F.extPrecompMap a (U.obj (K.obj i)) n)) :
    Function.Injective (F.extPrecompMap a (U.obj c.pt) n) := by
  let α := whiskerLeft U (F.extPrecompNatTrans a n)
  let : PreservesColimit K
      (U ⋙ (extFunctorObj X n ⋙ AddCommGrpCat.uliftFunctor.{w', w})) :=
    inferInstanceAs (PreservesColimit K
      ((U ⋙ extFunctorObj X n) ⋙ AddCommGrpCat.uliftFunctor.{w', w}))
  let : PreservesColimit K
      (U ⋙ ((F ⋙ extFunctorObj A n) ⋙ AddCommGrpCat.uliftFunctor.{w, w'})) :=
    inferInstanceAs (PreservesColimit K
      ((U ⋙ F ⋙ extFunctorObj A n) ⋙ AddCommGrpCat.uliftFunctor.{w, w'}))
  have hi (i : I) : Mono (α.app (K.obj i)) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y hxy
    have heq : F.extPrecompMap a (U.obj (K.obj i)) n x.down =
        F.extPrecompMap a (U.obj (K.obj i)) n y.down := congrArg ULift.down hxy
    have h := hK i heq
    cases x
    cases y
    exact congrArg ULift.up h
  let (i : I) : Mono ((whiskerLeft K α).app i) := hi i
  let : Mono (whiskerLeft K α) := NatTrans.mono_of_mono_app _
  let : Mono (α.app c.pt) := colim.map_mono' (whiskerLeft K α)
    (isColimitOfPreserves _ hc) (isColimitOfPreserves _ hc) (α.app c.pt)
    (fun i => α.naturality (c.ι.app i))
  have hα : Function.Injective (α.app c.pt) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro x y hxy
  have h : ULift.up x = (ULift.up y : ULift.{w'} (Ext X (U.obj c.pt) n)) :=
    hα (congrArg ULift.up hxy)
  exact congrArg ULift.down h

end CategoryTheory

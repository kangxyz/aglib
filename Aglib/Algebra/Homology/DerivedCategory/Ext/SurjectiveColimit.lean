/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ShortExactComparison
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Surjectivity of the original Ext comparison at an actual colimit

Only the target Ext functor must preserve the supplied colimit. An original
class in its value at the cocone point lifts from stage comparisons after
taking the colimit. Unlike bijectivity, this direction does not require
source Ext to preserve that colimit. This supplies the coefficient-colimit
step in the local proper-base-change comparison criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

private theorem epi_app_coconePt_of_preservesColimit
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    (K : J ⥤ C) {L L' : C ⥤ D} (α : L ⟶ L') (c : Cocone K) (hc : IsColimit c)
    [PreservesColimit K L'] (hα : ∀ i, Epi (α.app (K.obj i))) :
    Epi (α.app c.pt) := by
  let (i : J) : Epi ((Functor.whiskerLeft K α).app i) := hα i
  exact colim.map_epi' (Functor.whiskerLeft K α) (L.mapCocone c)
    (isColimitOfPreserves L' hc) (α.app c.pt) (fun i => α.naturality (c.ι.app i))

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : C} {A : D} (a : A ⟶ F.obj X)

/-- Target cohomological continuity alone descends surjectivity from the supplied stages. -/
theorem Functor.extPrecompMap_surjective_of_isColimit
    {I : Type*} [Category I] (K : I ⥤ C) (c : Cocone K) (hc : IsColimit c) (n : ℕ)
    [PreservesColimit K (F ⋙ extFunctorObj A n)]
    (hK : ∀ i, Function.Surjective (F.extPrecompMap a (K.obj i) n)) :
    Function.Surjective (F.extPrecompMap a c.pt n) := by
  let α := F.extPrecompNatTrans a n
  have hi (i : I) : Epi (α.app (K.obj i)) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨x, hx⟩ := hK i y.down
    refine ⟨ULift.up x, ?_⟩
    change ULift.up (F.extPrecompMap a (K.obj i) n x) = y
    rw [hx]
    cases y
    rfl
  let : Epi (α.app c.pt) := epi_app_coconePt_of_preservesColimit K α c hc hi
  have hα : Function.Surjective (α.app c.pt) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  intro y
  obtain ⟨x, hx⟩ := hα (ULift.up y)
  exact ⟨x.down, congrArg ULift.down hx⟩

/-- Target continuity on an original coefficient diagram suffices even when the
coefficient functor is not assumed to preserve its colimit. -/
theorem Functor.extPrecompMap_surjective_on_image_of_isColimit
    {B : Type*} [Category B] (U : B ⥤ C)
    {I : Type*} [Category I] (K : I ⥤ B) (c : Cocone K) (hc : IsColimit c) (n : ℕ)
    [PreservesColimit K (U ⋙ F ⋙ extFunctorObj A n)]
    (hK : ∀ i, Function.Surjective (F.extPrecompMap a (U.obj (K.obj i)) n)) :
    Function.Surjective (F.extPrecompMap a (U.obj c.pt) n) := by
  let α := whiskerLeft U (F.extPrecompNatTrans a n)
  let : PreservesColimit K
      (U ⋙ ((F ⋙ extFunctorObj A n) ⋙ AddCommGrpCat.uliftFunctor.{w, w'})) :=
    inferInstanceAs (PreservesColimit K
      ((U ⋙ F ⋙ extFunctorObj A n) ⋙ AddCommGrpCat.uliftFunctor.{w, w'}))
  have hi (i : I) : Epi (α.app (K.obj i)) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨x, hx⟩ := hK i y.down
    refine ⟨ULift.up x, ?_⟩
    change ULift.up (F.extPrecompMap a (U.obj (K.obj i)) n x) = y
    rw [hx]
    cases y
    rfl
  let : Epi (α.app c.pt) := epi_app_coconePt_of_preservesColimit K α c hc hi
  have hα : Function.Surjective (α.app c.pt) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  intro y
  obtain ⟨x, hx⟩ := hα (ULift.up y)
  exact ⟨x.down, congrArg ULift.down hx⟩

end CategoryTheory

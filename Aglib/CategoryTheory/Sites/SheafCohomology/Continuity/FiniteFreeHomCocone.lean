/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteTupleHom

/-! # Finite-family cochain colimits from the specified section cocones

A presheaf cocone need not be colimiting at every object. Colimit certificates
at the finitely many objects of a free family already give the original Hom
colimit. Applying this to each tuple degree gives a colimit cocone of the
original Hom cochain complexes. No global sheaf-colimit preservation is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf.Cech

universe u v uI vI

variable {C : Type u} [Category.{v} C]
  {I : Type uI} [Category.{vI} I]
  [HasColimitsOfShape I AddCommGrpCat.{max u v}]
  {ι : Type (max u v)} [Finite ι]
  {D : I ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}

/-- Colimits of the specified finite family of section cocones give the
colimit of the original free-family Hom cocone. -/
def freeFamilyHomIsColimit (U : ι → C) (c : Cocone D)
    (hsec : ∀ i, IsColimit
      (((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op (U i))).mapCocone c)) :
    IsColimit ((preadditiveCoyoneda.obj
      (op (familyPresheaf U ⋙ AddCommGrpCat.free))).mapCocone c) := by
  let : PreservesColimitsOfShape I
      (lim (J := Discrete ι) (C := AddCommGrpCat.{max u v})) :=
    preservesColimitsOfShape_of_natIso HasBiproductsOfShape.colimIsoLim
  have hE : IsColimit ((familyEvaluationDiagram U).flip.mapCocone c) :=
    evaluationJointlyReflectsColimits _ (fun i => hsec i.as)
  exact IsColimit.mapCoconeEquiv (freeFamilyHomProductIso U).symm
    (isColimitOfPreserves lim hE)

variable {W : C} (U : ι → Over W) [HasFiniteProducts (Over W)]

/-- The original free tuple Hom cocone is colimiting when its actual tuple
product section cocones are colimiting. -/
def freeTupleHomIsColimit (n : ℕ) (c : Cocone D)
    (hsec : ∀ a : Fin (n + 1) → ι, IsColimit
      (((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj
        (op (∏ᶜ fun k => U (a k)).left)).mapCocone c)) :
    IsColimit ((preadditiveCoyoneda.obj
      (op (tuplePresheaf (familyMap U) n ⋙ AddCommGrpCat.free))).mapCocone c) :=
  IsColimit.mapCoconeEquiv
    (preadditiveCoyoneda.mapIso ((freeFunctor.mapIso (tupleProductIso U n)).op))
    (freeFamilyHomIsColimit (fun a : Fin (n + 1) → ι => (∏ᶜ fun k => U (a k)).left)
      c hsec)

/-- Degreewise original tuple section certificates give a genuine colimit of
the original cochain complexes, including their differentials. -/
def finiteFamilyHomComplexIsColimit (c : Cocone D)
    (hsec : ∀ (n : ℕ) (a : Fin (n + 1) → ι), IsColimit
      (((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj
        (op (∏ᶜ fun k => U (a k)).left)).mapCocone c)) :
    IsColimit ((Sheaf.ModuleCoefficients.additiveHomFunctor
      (freeComplex (familyMap U))).mapCocone c) :=
  HomologicalComplex.isColimitOfEval _ _ (fun n => freeTupleHomIsColimit U n c (hsec n))

end CategoryTheory.Presheaf.Cech

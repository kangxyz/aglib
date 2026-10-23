/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteFreeHom
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ProjectiveHomComplex

/-! # Colimits of the original finite-family Hom cochains

The source objects here are presheaves. Finite tuple products reduce their Hom
functors to the finite free-family producer, with the original Čech differential.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf.Cech

universe v u k

variable {C : Type u} [Category.{v} C]
  {ι : Type (max u v)} [Finite ι] {W : C} (V : ι → Over W)
  [HasFiniteProducts (Over W)] {I : Type k} [SmallCategory I]
  [HasColimitsOfShape I AddCommGrpCat.{max u v}]

/-- Every original finite free tuple term has a colimit-preserving Hom functor. -/
abbrev freeTupleHomPreservesColimits (n : ℕ) :
    PreservesColimitsOfShape I
      (preadditiveCoyoneda.obj
        (op (tuplePresheaf (familyMap V) n ⋙ AddCommGrpCat.free))) := by
  let : PreservesColimitsOfShape I
      (preadditiveCoyoneda.obj
        (op (freeFunctor.obj (familyPresheaf
          (fun a : Fin (n + 1) → ι => (∏ᶜ fun i => V (a i)).left))))) :=
    freeFamilyHomPreservesColimits (I := I) _
  exact preservesColimitsOfShape_of_natIso
    (preadditiveCoyoneda.mapIso ((freeFunctor.mapIso (tupleProductIso V n)).op))

/-- The native Hom cochain functor of a finite family preserves colimits,
not only its underlying objects in each degree. -/
abbrev finiteFamilyHomComplexPreservesColimits :
    PreservesColimitsOfShape I
      (Sheaf.ModuleCoefficients.additiveHomFunctor (freeComplex (familyMap V))) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape I
    (preadditiveCoyoneda.obj
      (op (tuplePresheaf (familyMap V) n ⋙ AddCommGrpCat.free)))
  exact freeTupleHomPreservesColimits (I := I) V n

end CategoryTheory.Presheaf.Cech

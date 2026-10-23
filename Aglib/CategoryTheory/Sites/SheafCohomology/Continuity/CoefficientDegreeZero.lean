/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.SectionsColimit
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Degree-zero continuity with independent Ext universes

The original degree-zero cohomology and sections are compared after lifting
both group universes. Full faithfulness of the native lift reflects colimit
preservation back to the original cohomology functor.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Sheaf.H

open Limits Abelian Opposite

universe u v w e uI vI b

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]
  {T : C} (hT : IsTerminal T)

/-- The original degree-zero equivalence is natural after lifting both universes. -/
def degreeZeroSectionsUliftIso :
    functorH J 0 ⋙ AddCommGrpCat.uliftFunctor.{w, e} ≅
      (sheafSections J AddCommGrpCat.{w}).obj (op T) ⋙
        AddCommGrpCat.uliftFunctor.{e, w} :=
  NatIso.ofComponents (fun F => AddEquiv.toAddCommGrpIso
    ((AddEquiv.ulift.trans (equiv₀ F hT)).trans AddEquiv.ulift.symm)) (fun {F G} f => by
      apply AddCommGrpCat.ext
      intro x
      apply ULift.ext
      change equiv₀ G hT (map f 0 x.down) =
        f.hom.app (op T) (equiv₀ F hT x.down)
      exact (equiv₀_naturality hT f x.down).symm)

variable {I : Type uI} [Category.{vI} I]

include hT in
/-- Actual section-colimit preservation implies original degree-zero preservation,
without identifying the coefficient and Ext universes. -/
lemma preservesColimitsOfShape_degreeZero
    [PreservesColimitsOfShape I ((sheafSections J AddCommGrpCat.{w}).obj (op T))] :
    PreservesColimitsOfShape I (functorH J 0) := by
  let : PreservesColimitsOfShape I
      (functorH J 0 ⋙ AddCommGrpCat.uliftFunctor.{w, e}) :=
    preservesColimitsOfShape_of_natIso (degreeZeroSectionsUliftIso hT).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (functorH J 0) AddCommGrpCat.uliftFunctor.{w, e}

end CategoryTheory.Sheaf.H

namespace CategoryTheory.GrothendieckTopology.OneHypercoverFamily

open Limits Opposite

universe u v k e b

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{k}] [HasExt.{e} (Sheaf J AddCommGrpCat.{k})]
  (H : J.OneHypercoverFamily.{b}) [H.IsGenerating]
  (hfin : ∀ ⦃X : C⦄ (E : J.OneHypercover.{b} X), H E →
    Finite E.I₀ ∧ ∀ i j : E.I₀, Finite (E.I₁ i j))
  {I : Type k} [SmallCategory I] [IsFiltered I] {T : C} (hT : IsTerminal T)

include H hfin hT in
/-- Finite generating hypercovers supply the degree-zero input to continuity. -/
lemma preservesFilteredColimitsDegreeZero :
    PreservesColimitsOfShape I (Sheaf.functorH J 0) := by
  let := preservesFilteredColimitsSections (I := I) H hfin T
  exact Sheaf.H.preservesColimitsOfShape_degreeZero hT

end CategoryTheory.GrothendieckTopology.OneHypercoverFamily

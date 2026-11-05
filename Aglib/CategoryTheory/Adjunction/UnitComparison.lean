/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Whole comparison isomorphisms determined by the original adjunction unit

Given the existing component comparisons and the actual unit, their unit
factorizations prove naturality and the complete whiskered unit square. No
replacement comparison, presentation or realization is selected.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe uC vC uA vA uB vB

variable {C : Type uC} [Category.{vC} C]
  {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
  (P : C ⥤ A) (H : C ⥤ B) (k : P ⟶ H ⋙ R)
  (e : ∀ c, L.obj (P.obj c) ≅ H.obj c)
  (he : ∀ c, adj.unit.app (P.obj c) ≫ R.map (e c).hom = k.app c)

include adj k he in
/-- The original unit determines the full comparison naturality square. -/
theorem comparison_naturality_of_unit {c d : C} (a : c ⟶ d) :
    L.map (P.map a) ≫ (e d).hom = (e c).hom ≫ H.map a := by
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    adj.homEquiv_unit, adj.homEquiv_unit, he c, he d]
  exact k.naturality a

/-- Assemble the existing component isomorphisms without changing their maps. -/
def comparisonNatIsoOfUnit : P ⋙ L ≅ H :=
  NatIso.ofComponents e (by
    intro c d a
    exact comparison_naturality_of_unit adj P H k e he a)

/-- The assembled comparison retains the complete original unit square. -/
theorem comparisonNatIsoOfUnit_unit :
    (Functor.rightUnitor P).inv ≫ Functor.whiskerLeft P adj.unit ≫
      (Functor.associator P L R).inv ≫
      Functor.whiskerRight (comparisonNatIsoOfUnit adj P H k e he).hom R = k := by
  apply NatTrans.ext
  funext c
  change 𝟙 _ ≫ adj.unit.app (P.obj c) ≫ 𝟙 _ ≫ R.map (e c).hom = k.app c
  simpa only [Category.id_comp] using he c

end CategoryTheory.Adjunction

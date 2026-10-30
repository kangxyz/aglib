/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnitComparisonBaseChange

/-!
# Whole naturality equations for specified unit comparisons

The property retains all original transformations and is proved from their
component formulas and actual left-comparison cube. Keeping this whole equation
abstract avoids duplicating large concrete adjunction terms in consumers.
-/

@[expose] public section

universe uA vA uB vB uC vC uA' vA' uB' vB' uC' vC'

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {C : Type uC} {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vA'} A'] [Category.{vB'} B'] [Category.{vC'} C']
  {J : A ⥤ B} {I : A ⥤ C} {J' : A' ⥤ B'} {I' : A' ⥤ C'}
  {L : B ⥤ C} {R : C ⥤ B} {L' : B' ⥤ C'} {R' : C' ⥤ B'}
  {G : B ⥤ B'} {H : C ⥤ C'} {V : A ⥤ A'}

/-- The whole original unit-comparison naturality equation. -/
def UnitComparisonNaturalityEquation
    (β : R ⋙ G ⟶ H ⋙ R') (eJ : J ⋙ G ⟶ V ⋙ J') (eI : I ⋙ H ⟶ V ⋙ I')
    (δ : J ⟶ I ⋙ R) (δ' : J' ⟶ I' ⋙ R') : Prop :=
  ∀ K, G.map (δ.app K) ≫ β.app (I.obj K) ≫ R'.map (eI.app K) =
    eJ.app K ≫ δ'.app (V.obj K)

/-- Actual component formulas and the actual left cube prove whole naturality;
none of the comparison transformations is replaced. -/
theorem unitComparisonNaturalityEquation_of_mate
    (adj : L ⊣ R) (adj' : L' ⊣ R') (α : TwoSquare G L L' H)
    (β : R ⋙ G ⟶ H ⋙ R') (hβ : β = (mateEquiv adj adj' α).natTrans)
    (σ : J ⋙ L ⟶ I) (σ' : J' ⋙ L' ⟶ I')
    (eJ : J ⋙ G ⟶ V ⋙ J') (eI : I ⋙ H ⟶ V ⋙ I')
    (δ : J ⟶ I ⋙ R) (δ' : J' ⟶ I' ⋙ R')
    (hδ : ∀ K, δ.app K = adj.unit.app (J.obj K) ≫ R.map (σ.app K))
    (hδ' : ∀ K, δ'.app K = adj'.unit.app (J'.obj K) ≫ R'.map (σ'.app K))
    (hσ : ∀ K, α.app (J.obj K) ≫ H.map (σ.app K) ≫ eI.app K =
      L'.map (eJ.app K) ≫ σ'.app (V.obj K)) :
    UnitComparisonNaturalityEquation β eJ eI δ δ' := by
  intro K
  rw [hδ, hδ']
  exact adjunctionUnitComparison_baseChange adj adj' α β hβ σ σ' eJ eI K (hσ K)

end CategoryTheory

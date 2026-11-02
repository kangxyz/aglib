/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections
public import Aglib.CategoryTheory.Adjunction.UnitHomMap

/-! # The actual section pullback and original integer source

The image unit and the original right-adjoint section comparison construct the
whole section map. Its coefficient naturality is proved before applying the
original constant-integer Hom comparison.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

universe uC vC uD vD uV vV s

section Ordinary

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {V : Type uV} [Category.{vV} V] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) (Γ : C ⥤ V) {Δ : D ⥤ V} (e : R ⋙ Γ ≅ Δ)

/-- The whole original section pullback from its actual unit and right comparison. -/
def unitSectionsNatTrans : Γ ⟶ L ⋙ Δ where
  app Y := adj.unitSectionMap Γ e Y
  naturality {Y Z} q := by
    have hη := adj.unit.naturality q
    change q ≫ adj.unit.app Z = adj.unit.app Y ≫ R.map (L.map q) at hη
    have he := e.hom.naturality (L.map q)
    change Γ.map (R.map (L.map q)) ≫ e.hom.app (L.obj Z) =
      e.hom.app (L.obj Y) ≫ Δ.map (L.map q) at he
    dsimp only [unitSectionMap]
    rw [← Functor.map_comp_assoc, hη, Functor.map_comp]
    simp only [Category.assoc]
    rw [he]
    rw [Functor.comp_map]

/-- Each component is the original unit-section map. -/
theorem unitSectionsNatTrans_app (Y : C) :
    (unitSectionsNatTrans adj Γ e).app Y =
      Γ.map (adj.unit.app Y) ≫ e.hom.app (L.obj Y) := rfl

end Ordinary

section Integer

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  {L : C ⥤ D} {R : D ⥤ C}
  {K : AddCommGrpCat.{s} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{s}}
  {K' : AddCommGrpCat.{s} ⥤ D} {Δ : D ⥤ AddCommGrpCat.{s}}
  [K.Additive] [K'.Additive]
  (constantAdj : K ⊣ Γ) (imageAdj : L ⊣ R) (constantAdj' : K' ⊣ Δ)
  (e : R ⋙ Γ ≅ Δ) (c : K ⋙ L ≅ K')
  (hc : c = leftAdjointCompIso constantAdj imageAdj constantAdj' e)

include hc in
/-- The actual source transport is the original section-unit pullback on integer Hom. -/
theorem integerHomSectionsAddEquiv_pullback {Y : C}
    (a : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ Y) :
    integerHomSectionsAddEquiv constantAdj' (L.obj Y)
        (c.inv.app (AddCommGrpCat.of (ULift.{s} ℤ)) ≫ L.map a) =
      (unitSectionsNatTrans imageAdj Γ e).app Y
        (integerHomSectionsAddEquiv constantAdj Y a) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv (Δ.obj (L.obj Y))
      (constantAdj'.homEquiv _ (L.obj Y)
        (c.inv.app (AddCommGrpCat.of (ULift.{s} ℤ)) ≫ L.map a)) =
    imageAdj.unitSectionMap Γ e Y
      (AddCommGrpCat.uliftZMultiplesAddEquiv (Γ.obj Y)
        (constantAdj.homEquiv _ Y a))
  rw [unitSectionMap_homEquiv constantAdj imageAdj constantAdj' e c hc]
  rfl

end Integer

section IntegerFunctor

variable {C : Type uC} [Category.{s} C] [Preadditive C]
  {D : Type uD} [Category.{s} D] [Preadditive D]
  {L : C ⥤ D} {R : D ⥤ C}
  {K : AddCommGrpCat.{s} ⥤ C} {Γ : C ⥤ AddCommGrpCat.{s}}
  {K' : AddCommGrpCat.{s} ⥤ D} {Δ : D ⥤ AddCommGrpCat.{s}}
  [K.Additive] [K'.Additive]
  (constantAdj : K ⊣ Γ) (imageAdj : L ⊣ R) (constantAdj' : K' ⊣ Δ)
  (e : R ⋙ Γ ≅ Δ) (c : K ⋙ L ≅ K')
  (hc : c = leftAdjointCompIso constantAdj imageAdj constantAdj' e)

include hc in
/-- The same whole original-source equation for the existing Hom functor. -/
theorem integerHomSectionsIso_pullback {Y : C}
    (a : K.obj (AddCommGrpCat.of (ULift.{s} ℤ)) ⟶ Y) :
    (integerHomSectionsIso constantAdj').hom.app (L.obj Y)
        (c.inv.app (AddCommGrpCat.of (ULift.{s} ℤ)) ≫ L.map a) =
      (unitSectionsNatTrans imageAdj Γ e).app Y
        ((integerHomSectionsIso constantAdj).hom.app Y a) :=
  integerHomSectionsAddEquiv_pullback constantAdj imageAdj constantAdj' e c hc a

end IntegerFunctor

end CategoryTheory.Adjunction

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.NaturalPastedRectangle
public import Aglib.CategoryTheory.Adjunction.PastedRectangleSource

/-! # Whole refinement rectangles with the original source-unit map -/

@[expose] public section

namespace CategoryTheory

variable {A B C D E F G : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F] [Category G]
  {HA : A ⥤ B} {QC : A ⥤ C} {QD : B ⥤ C}
  {HB : D ⥤ E} {RC : D ⥤ F} {RD : E ⥤ G} {HT : F ⥤ G}
  {IC : C ⥤ F} {ID : C ⥤ G} {MC : A ⥤ D} {MD : B ⥤ E}

/-- The actual normalized refinement rectangle, retaining whole original maps. -/
def NaturalRefinementRectangleEquation
    (σD : QD ⋙ ID ⟶ MD ⋙ RD) (σMid : HA ⋙ MD ⟶ MC ⋙ HB)
    (δTarget : ID ⟶ IC ⋙ HT) (σC : QC ⋙ IC ⟶ MC ⋙ RC)
    (over : HA ⋙ QD ≅ QC) (comm : RC ⋙ HT ≅ HB ⋙ RD) : Prop :=
  ∀ K, PastedRectangleEquation
    (ID.map (over.inv.app K)) (δTarget.app (QC.obj K))
    (σD.app (HA.obj K) ≫ RD.map (σMid.app K))
    (HT.map (σC.app K)) (comm.hom.app (MC.obj K))

/-- Contract the whole proved identity-source mate equation inside the whole
pasted rectangle, keeping the specified original refinement transformation. -/
theorem naturalPastedRectangle_contract_identitySource
    {L T : C ⥤ C} {P : G ⥤ F}
    (aI : L ⊣ T) (aP : P ⊣ HT) (β : TwoSquare ID L P IC)
    (rid : T ≅ 𝟭 C) (δTarget : ID ⟶ IC ⋙ HT)
    (hδ : IdentitySourceMateEquation aI aP β rid δTarget)
    (σD : QD ⋙ ID ⟶ MD ⋙ RD) (σMid : HA ⋙ MD ⟶ MC ⋙ HB)
    (σTarget : T ⋙ ID ⟶ IC ⋙ HT) (σC : QC ⋙ IC ⟶ MC ⋙ RC)
    (over : HA ⋙ QD ≅ QC) (comm : RC ⋙ HT ≅ HB ⋙ RD)
    (hσ : σTarget = (mateEquiv aI aP β).natTrans)
    (h : NaturalPastedRectangleEquation σD σMid σTarget σC over rid comm) :
    NaturalRefinementRectangleEquation σD σMid δTarget σC over comm := by
  subst σTarget
  intro K
  exact pastedRectangle_contract_identitySource aI aP β rid δTarget hδ (QC.obj K)
    (ID.map (over.inv.app K))
    (σD.app (HA.obj K) ≫ RD.map (σMid.app K))
    (HT.map (σC.app K)) (comm.hom.app (MC.obj K)) (h K)

end CategoryTheory

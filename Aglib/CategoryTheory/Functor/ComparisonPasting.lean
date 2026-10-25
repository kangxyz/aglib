/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.TwoSquare

/-! # Pasting section and coefficient comparisons

A section transformation and a coefficient transformation define one comparison
between the original composite functors. Composition and transport of these
comparisons turn whole section and coefficient relations into a commutative square.
All categories, including the target of sections, have independent universes.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

namespace CategoryTheory.Functor

section Comparison

variable {C : Type u₁} {A : Type u₂} {B : Type u₃} {E : Type u₆}
  [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} B] [Category.{v₆} E]
  {P : C ⥤ A} {I : A ⥤ B} {Q : C ⥤ B} {G₀ : A ⥤ E} {G₁ : B ⥤ E}

/-- Paste a section transformation with a coefficient transformation, retaining
the original source and target composite functors. -/
def comparisonPasting (σ : G₀ ⟶ I ⋙ G₁) (α : P ⋙ I ⟶ Q) :
    P ⋙ G₀ ⟶ Q ⋙ G₁ :=
  whiskerLeft P σ ≫ (associator P I G₁).inv ≫ whiskerRight α G₁

/-- The comparison has the original section map followed by the coefficient map. -/
@[simp]
theorem comparisonPasting_app (σ : G₀ ⟶ I ⋙ G₁) (α : P ⋙ I ⟶ Q) (F : C) :
    (comparisonPasting σ α).app F = σ.app (P.obj F) ≫ G₁.map (α.app F) := by
  simp only [comparisonPasting, NatTrans.comp_app, whiskerLeft_app,
    associator_inv_app, whiskerRight_app, Category.id_comp]

/-- The comparison is the horizontal pasting of the original two squares,
with its identity functors removed by the ordinary unitors. -/
theorem comparisonPasting_eq_hComp (σ : G₀ ⟶ I ⋙ G₁) (α : P ⋙ I ⟶ Q) :
    comparisonPasting σ α =
      whiskerRight (rightUnitor P).inv G₀ ≫
        (TwoSquare.hComp
          (TwoSquare.mk P Q I (𝟭 B) (α ≫ (rightUnitor Q).inv))
          (TwoSquare.mk (𝟭 A) I G₀ G₁ ((leftUnitor G₀).hom ≫ σ))).natTrans ≫
        whiskerLeft Q (leftUnitor G₁).hom := by
  ext F
  simp [comparisonPasting, TwoSquare.hComp]

variable {D : Type u₄} [Category.{v₄} D]
  {J : B ⥤ D} {R : C ⥤ D} {G₂ : D ⥤ E}

/-- Comparison maps compose by pasting their section and coefficient
transformations. The interchange is naturality of the second section map. -/
theorem comparisonPasting_comp (σ₁ : G₀ ⟶ I ⋙ G₁) (σ₂ : G₁ ⟶ J ⋙ G₂)
    (α₁ : P ⋙ I ⟶ Q) (α₂ : Q ⋙ J ⟶ R) :
    comparisonPasting σ₁ α₁ ≫ comparisonPasting σ₂ α₂ =
      comparisonPasting
        (σ₁ ≫ whiskerLeft I σ₂ ≫ (associator I J G₂).inv)
        ((associator P I J).inv ≫ whiskerRight α₁ J ≫ α₂) := by
  ext F
  simp only [NatTrans.comp_app, comparisonPasting_app, whiskerLeft_app,
    associator_inv_app, whiskerRight_app, Functor.comp_obj, Functor.map_comp,
    Category.id_comp, Category.assoc]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc] using
    congrArg (fun f => σ₁.app (P.obj F) ≫ f ≫ G₂.map (α₂.app F))
      (σ₂.naturality (α₁.app F))

/-- Transport across the intermediate functor can be placed in either the
section transformation or the coefficient transformation. -/
theorem comparisonPasting_transport {I' : A ⥤ B} (σ : G₀ ⟶ I ⋙ G₁)
    (τ : I ⟶ I') (α : P ⋙ I' ⟶ Q) :
    comparisonPasting (σ ≫ whiskerRight τ G₁) α =
      comparisonPasting σ (whiskerLeft P τ ≫ α) := by
  ext F
  simp only [comparisonPasting_app, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, Functor.map_comp, Category.assoc]

/-- The component of a comparison after precomposition is its original component
at the image object, with the coefficient associator retained in the input. -/
theorem comparisonPasting_whiskerLeft_app {C' : Type u₅} [Category.{v₅} C']
    (R' : C' ⥤ C) (σ : G₀ ⟶ I ⋙ G₁) (α : P ⋙ I ⟶ Q) (F : C') :
    (comparisonPasting σ ((associator R' P I).hom ≫ whiskerLeft R' α)).app F =
      (comparisonPasting σ α).app (R'.obj F) := by
  simp only [comparisonPasting_app, NatTrans.comp_app, associator_hom_app,
    whiskerLeft_app, Functor.comp_obj, Category.id_comp]

end Comparison

section CoefficientPasting

variable {X : Type u₁} {S : Type u₂} {X' : Type u₃} {S' : Type u₄}
  {Z : Type u₅} {U : Type u₆} {W : Type u₇} {V : Type u₈}
  [Category.{v₁} X] [Category.{v₂} S] [Category.{v₃} X'] [Category.{v₄} S']
  [Category.{v₅} Z] [Category.{v₆} U] [Category.{v₇} W] [Category.{v₈} V]
  {P : X ⥤ S} {P' : X' ⥤ S'} {PU : Z ⥤ U} {PV : W ⥤ V}
  {Ig : S ⥤ S'} {Ig' : X ⥤ X'} {IU : S ⥤ U} {IV : S' ⥤ V}
  {IpiU : X ⥤ Z} {IpiV : X' ⥤ W} {Ib : U ⥤ V} {Ir : Z ⥤ W}

/-- The whole relative relation between the original coefficient squares gives
the coefficient equation for the folded comparison square. -/
theorem comparisonPasting_coefficient_eq_of_twoSquare
    (beta : TwoSquare P Ig' Ig P') (betaU : TwoSquare P IpiU IU PU)
    (betaV : TwoSquare P' IpiV IV PV) (betaR : TwoSquare PU Ir Ib PV)
    (deltaS : TwoSquare IU Ig Ib IV) (deltaX : TwoSquare IpiU Ig' Ir IpiV)
    (hrelative : (beta.vComp betaV).whiskerRight deltaS =
      (betaU.vComp betaR).whiskerLeft deltaX) :
    whiskerLeft P deltaS.natTrans ≫ (associator P Ig IV).inv ≫
        whiskerRight beta.natTrans IV ≫
        ((associator Ig' P' IV).hom ≫ whiskerLeft Ig' betaV.natTrans) =
      (associator P IU Ib).inv ≫ whiskerRight betaU.natTrans Ib ≫
        (deltaX.hComp betaR).natTrans := by
  ext F
  have hF := NatTrans.congr_app hrelative F
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.hComp, TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hF

variable {E : Type u₉} [Category.{v₉} E] {GU : U ⥤ E} {GV : V ⥤ E}

/-- The comparison with a horizontal coefficient pasting retains the original
section map, relative exchange and coefficient comparison at every component. -/
theorem comparisonPasting_hComp_app (s : GU ⟶ Ib ⋙ GV)
    (betaR : TwoSquare PU Ir Ib PV) (deltaX : TwoSquare IpiU Ig' Ir IpiV) (F : X) :
    (comparisonPasting s (deltaX.hComp betaR).natTrans).app F =
      s.app (PU.obj (IpiU.obj F)) ≫
        GV.map (betaR.app (IpiU.obj F) ≫ PV.map (deltaX.app F)) := by
  simp only [comparisonPasting_app, TwoSquare.hComp, TwoSquare.natTrans,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft, Functor.whiskerRight,
    associator_hom_app, associator_inv_app, Functor.comp_obj,
    Category.id_comp, Category.comp_id]

end CoefficientPasting

section Square

variable {C : Type u₁} {A : Type u₂} {B : Type u₃}
  {U : Type u₄} {V : Type u₅} {E : Type u₆}
  [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} B]
  [Category.{v₄} U] [Category.{v₅} V] [Category.{v₆} E]
  {P : C ⥤ A} {L : C ⥤ B} {QU : C ⥤ U} {QV : C ⥤ V}
  {Ig : A ⥤ B} {IU : A ⥤ U} {IV : B ⥤ V} {Ib : U ⥤ V}
  {SU : A ⥤ E} {SV : B ⥤ E} {GU : U ⥤ E} {GV : V ⥤ E}

/-- The original whole unit square gives the section coherence with explicit
functor associators, before any categories or section functors are specialized. -/
theorem comparisonPasting_unit_coherence_of_square
    (t : SU ⟶ Ig ⋙ SV) (s : GU ⟶ Ib ⋙ GV)
    (eU : IU ⋙ GU ≅ SU) (eV : IV ⋙ GV ≅ SV)
    (delta : IU ⋙ Ib ⟶ Ig ⋙ IV)
    (h : t ≫ whiskerLeft Ig eV.inv =
      eU.inv ≫ (whiskerLeft IU s ≫ whiskerRight delta GV)) :
    t ≫ whiskerLeft Ig eV.inv ≫ (associator Ig IV GV).inv =
      eU.inv ≫ whiskerLeft IU s ≫ (associator IU Ib GV).inv ≫
        whiskerRight delta GV := by
  ext F
  have hF := NatTrans.congr_app h F
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    associator_inv_app, Category.id_comp, Category.comp_id] using hF

/-- Whole section coherence and whole relative coefficient coherence give the
commutative square of the four actual comparison transformations. -/
theorem comparisonPasting_commSq
    (t : SU ⟶ Ig ⋙ SV) (s : GU ⟶ Ib ⋙ GV)
    (eU : IU ⋙ GU ≅ SU) (eV : IV ⋙ GV ≅ SV)
    (beta : P ⋙ Ig ⟶ L) (betaU : P ⋙ IU ⟶ QU)
    (betaV : L ⋙ IV ⟶ QV) (rho : QU ⋙ Ib ⟶ QV)
    (delta : IU ⋙ Ib ⟶ Ig ⋙ IV)
    (hunit : t ≫ whiskerLeft Ig eV.inv ≫ (associator Ig IV GV).inv =
      eU.inv ≫ whiskerLeft IU s ≫ (associator IU Ib GV).inv ≫ whiskerRight delta GV)
    (hcoeff : whiskerLeft P delta ≫ (associator P Ig IV).inv ≫
      whiskerRight beta IV ≫ betaV =
        (associator P IU Ib).inv ≫ whiskerRight betaU Ib ≫ rho) :
    CommSq (comparisonPasting t beta) (comparisonPasting eU.inv betaU)
      (comparisonPasting eV.inv betaV) (comparisonPasting s rho) := by
  refine ⟨?_⟩
  rw [comparisonPasting_comp, comparisonPasting_comp]
  have hunit' : t ≫ whiskerLeft Ig eV.inv ≫ (associator Ig IV GV).inv =
      (eU.inv ≫ whiskerLeft IU s ≫ (associator IU Ib GV).inv) ≫
        whiskerRight delta GV := by
    simpa only [Category.assoc] using hunit
  rw [hunit', comparisonPasting_transport, hcoeff]

end Square

section TwoSquareComparison

variable {X : Type u₁} {S : Type u₂} {X' : Type u₃} {S' : Type u₄}
  {Z : Type u₅} {U : Type u₆} {W : Type u₇} {V : Type u₈} {E : Type u₉}
  [Category.{v₁} X] [Category.{v₂} S] [Category.{v₃} X'] [Category.{v₄} S']
  [Category.{v₅} Z] [Category.{v₆} U] [Category.{v₇} W] [Category.{v₈} V]
  [Category.{v₉} E]
  {P : X ⥤ S} {P' : X' ⥤ S'} {PU : Z ⥤ U} {PV : W ⥤ V}
  {Ig : S ⥤ S'} {Ig' : X ⥤ X'} {IU : S ⥤ U} {IV : S' ⥤ V}
  {IpiU : X ⥤ Z} {IpiV : X' ⥤ W} {Ib : U ⥤ V} {Ir : Z ⥤ W}
  {SU : S ⥤ E} {SV : S' ⥤ E} {GU : U ⥤ E} {GV : V ⥤ E}

/-- The component view of the whole comparison square, expressed through the
original chart comparison and the original relative coefficient factors. -/
theorem comparisonPasting_twoSquare_app
    (t : SU ⟶ Ig ⋙ SV) (s : GU ⟶ Ib ⋙ GV)
    (eU : IU ⋙ GU ≅ SU) (eV : IV ⋙ GV ≅ SV)
    (beta : TwoSquare P Ig' Ig P') (betaU : TwoSquare P IpiU IU PU)
    (betaV : TwoSquare P' IpiV IV PV) (betaR : TwoSquare PU Ir Ib PV)
    (deltaS : TwoSquare IU Ig Ib IV) (deltaX : TwoSquare IpiU Ig' Ir IpiV)
    (hunit : t ≫ whiskerLeft Ig eV.inv ≫ (associator Ig IV GV).inv =
      eU.inv ≫ whiskerLeft IU s ≫ (associator IU Ib GV).inv ≫
        whiskerRight deltaS.natTrans GV)
    (hrelative : (beta.vComp betaV).whiskerRight deltaS =
      (betaU.vComp betaR).whiskerLeft deltaX) (F : X) :
    (comparisonPasting t beta.natTrans).app F ≫
        (comparisonPasting eV.inv betaV.natTrans).app (Ig'.obj F) =
      (comparisonPasting eU.inv betaU.natTrans).app F ≫
        s.app (PU.obj (IpiU.obj F)) ≫
        GV.map (betaR.natTrans.app (IpiU.obj F) ≫ PV.map (deltaX.natTrans.app F)) := by
  have hcoeff := comparisonPasting_coefficient_eq_of_twoSquare
    beta betaU betaV betaR deltaS deltaX hrelative
  have hsquare := comparisonPasting_commSq t s eU eV beta.natTrans betaU.natTrans
    ((associator Ig' P' IV).hom ≫ whiskerLeft Ig' betaV.natTrans)
    (deltaX.hComp betaR).natTrans deltaS.natTrans hunit hcoeff
  have hF := NatTrans.congr_app hsquare.w F
  simpa only [NatTrans.comp_app, comparisonPasting_whiskerLeft_app,
    comparisonPasting_hComp_app] using hF

end TwoSquareComparison

end CategoryTheory.Functor

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackSectionsBase

/-! # Original coefficient-square section maps on etale tests

The original chart-evaluation isomorphisms identify the original square
section transfer with the component of the original adjoint coefficient map,
followed by restriction along the specified test morphism. The proof consumes
the existing unit-representative equation, not a continuity assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge

/-- The original chart-evaluation comparisons, as a whole natural isomorphism in coefficients. -/
def pullbackSectionsEtaleEvaluationNatIso {X : Scheme.{u}} (U : X.Etale) :
    inverseImage U.hom ⋙ globalSections U.left ≅
      (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) :=
  NatIso.ofComponents (fun F => pullbackSectionsEtaleEvaluationIso F U)
    (fun q => pullbackSectionsEtaleEvaluationIso_naturality q U)

/-- Compare the original square and triangle in the functor category, before evaluation. -/
lemma inverseImageSquareIso_inv_eq_triangle_whole {X S Y Z : Scheme.{u}}
    (f : S ⟶ X) (u : Y ⟶ X) (w : Z ⟶ S) (r : Z ⟶ Y)
    (h : r ≫ u = w ≫ f) :
    (inverseImageSquareIso u w f r h.symm).inv =
      (pullbackTriangleIso (w ≫ f) u r h).inv ≫ (inverseImageComp f w).hom := by
  simp only [inverseImageSquareIso, pullbackTriangleIso, Iso.trans_inv,
    Iso.symm_inv, Category.assoc]

/-- Evaluate the whole comparison at an arbitrary native coefficient. -/
lemma inverseImageSquareIso_inv_eq_triangle {X S Y Z : Scheme.{u}}
    (f : S ⟶ X) (u : Y ⟶ X) (w : Z ⟶ S) (r : Z ⟶ Y)
    (h : r ≫ u = w ≫ f) (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageSquareIso u w f r h.symm).inv.app F =
      (pullbackTriangleIso (w ≫ f) u r h).inv.app F ≫
        (inverseImageComp f w).hom.app F :=
  NatTrans.congr_app (inverseImageSquareIso_inv_eq_triangle_whole f u w r h) F

/-- The original coefficient-square section transfer before evaluating a coefficient. -/
def squareSectionsNatTrans {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀) :
    inverseImage f₀ ⋙ globalSections X₀ ⟶
      inverseImage g ⋙ inverseImage f₁ ⋙ globalSections X₁ :=
  Functor.whiskerLeft (inverseImage f₀) (globalSectionsPullbackNatTrans h) ≫
    Functor.whiskerRight (inverseImageSquareIso f₀ f₁ g h e).inv (globalSections X₁)

/-- The component of the whole square is the original pullback and square component. -/
lemma squareSectionsNatTrans_app {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀) (F : AbelianSheaf.{u, u + 1} S₀) :
    (squareSectionsNatTrans f₀ f₁ g h e).app F =
      globalSectionsPullback h ((inverseImage f₀).obj F) ≫
        (globalSections X₁).map ((inverseImageSquareIso f₀ f₁ g h e).inv.app F) := rfl

/-- The whole native bifunctor evaluates to the literal original relative section arrow. -/
lemma pullbackSectionsBifunctor_map_app {X : Scheme.{u}} {U V : Over X}
    (a : U ⟶ V) (F : AbelianSheaf.{u, u + 1} X) :
    ((pullbackSectionsBifunctor X).map a.op).app F = pullbackSectionsMap F a := rfl

/-- Normalize the original section arrow in the whole coefficient bifunctor. -/
lemma pullbackSectionsBifunctor_comp_square {X S Y Z : Scheme.{u}}
    (f : S ⟶ X) (u : Y ⟶ X) (w : Z ⟶ S)
    (a : Over.mk (w ≫ f) ⟶ Over.mk u) :
    (pullbackSectionsBifunctor X).map a.op ≫
        Functor.whiskerRight (inverseImageComp f w).hom (globalSections Z) =
      squareSectionsNatTrans u w f a.left (Over.w a).symm := by
  let p := Functor.whiskerLeft (inverseImage u) (globalSectionsPullbackNatTrans a.left)
  let t := (pullbackTriangleIso (w ≫ f) u a.left (Over.w a)).inv
  let k := (inverseImageComp f w).hom
  have hc : Functor.whiskerRight t (globalSections Z) ≫
      Functor.whiskerRight k (globalSections Z) =
      Functor.whiskerRight (inverseImageSquareIso u w f a.left (Over.w a).symm).inv
        (globalSections Z) :=
    (Functor.whiskerRight_comp t k (globalSections Z)).symm.trans
      (congrArg (fun q => Functor.whiskerRight q (globalSections Z))
        (inverseImageSquareIso_inv_eq_triangle_whole f u w a.left (Over.w a)).symm)
  change (p ≫ Functor.whiskerRight t (globalSections Z)) ≫
    Functor.whiskerRight k (globalSections Z) = _
  exact (Category.assoc _ _ _).trans (congrArg (fun q => p ≫ q) hc)

/-- The original unit followed by restriction, as a whole coefficient transformation. -/
def unitSectionNatTrans {X S : Scheme.{u}} (f : S ⟶ X)
    {U : X.Etale} {W : S.Etale} (a : W ⟶ (siteBaseChange f).obj U) :
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) ⟶
      inverseImage f ⋙
        (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op W) :=
  Functor.whiskerRight (inverseImageAdjunction f).unit
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) ≫
    Functor.whiskerLeft (inverseImage f)
      ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).map a.op)

/-- The whole unit transformation retains the original unit section map as its component. -/
lemma unitSectionNatTrans_app {X S : Scheme.{u}} (f : S ⟶ X)
    {U : X.Etale} {W : S.Etale} (a : W ⟶ (siteBaseChange f).obj U)
    (F : AbelianSheaf.{u, u + 1} X) :
    (unitSectionNatTrans f a).app F = unitSectionMap f F a := rfl

/-- Package the existing original representative equation before specializing its coefficient. -/
lemma unitSectionNatTrans_triangle {X S : Scheme.{u}} (f : S ⟶ X)
    {U : X.Etale} {W : S.Etale} (a : W ⟶ (siteBaseChange f).obj U) :
    unitSectionNatTrans f a ≫
        Functor.whiskerLeft (inverseImage f) (pullbackSectionsEtaleEvaluationNatIso W).inv ≫
        (Functor.isoWhiskerRight (inverseImageComp f W.hom) (globalSections W.left)).inv =
      (pullbackSectionsEtaleEvaluationNatIso U).inv ≫
        (pullbackSectionsBifunctor X).map (unitRepresentativeArrow f a).op := by
  apply NatTrans.ext
  funext F
  change (unitSectionNatTrans f a).app F ≫
      (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv ≫
        (globalSections W.left).map ((inverseImageComp f W.hom).inv.app F) =
      (pullbackSectionsEtaleEvaluationIso F U).inv ≫
        ((pullbackSectionsBifunctor X).map (unitRepresentativeArrow f a).op).app F
  exact (congrArg
    (fun q => q ≫ (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv ≫
      (globalSections W.left).map ((inverseImageComp f W.hom).inv.app F))
    (unitSectionNatTrans_app f a F)).trans
      ((unitSectionMap_etaleEvaluation f F a).trans
        (congrArg (fun q => (pullbackSectionsEtaleEvaluationIso F U).inv ≫ q)
          (pullbackSectionsBifunctor_map_app (unitRepresentativeArrow f a) F).symm))

/-- Cancel native composition in the whole original unit-and-square equation. -/
lemma unitSectionNatTrans_square {X S : Scheme.{u}} (f : S ⟶ X)
    {U : X.Etale} {W : S.Etale} (a : W ⟶ (siteBaseChange f).obj U) :
    unitSectionNatTrans f a ≫
        Functor.whiskerLeft (inverseImage f) (pullbackSectionsEtaleEvaluationNatIso W).inv =
      (pullbackSectionsEtaleEvaluationNatIso U).inv ≫
        squareSectionsNatTrans (X₀ := U.left) (S₀ := X) (X₁ := W.left) (S₁ := S)
          U.hom W.hom f (unitRepresentativeArrow f a).left
          (Over.w (unitRepresentativeArrow f a)).symm := by
  let E := Functor.isoWhiskerRight (inverseImageComp f W.hom) (globalSections W.left)
  let L := (pullbackSectionsEtaleEvaluationNatIso U).inv
  let t := (pullbackSectionsBifunctor X).map (unitRepresentativeArrow f a).op
  have h : (unitSectionNatTrans f a ≫
      Functor.whiskerLeft (inverseImage f) (pullbackSectionsEtaleEvaluationNatIso W).inv) ≫
        E.inv = L ≫ t :=
    (Category.assoc _ _ _).trans (unitSectionNatTrans_triangle f a)
  exact (E.comp_inv_eq.mp h).trans
    ((Category.assoc _ _ _).trans (congrArg (fun q => L ≫ q)
      (pullbackSectionsBifunctor_comp_square f U.hom W.hom (unitRepresentativeArrow f a))))

/-- Evaluate the whole original unit-and-square equation once. -/
lemma unitSectionMap_square_etaleEvaluation {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale} {W : S.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) :
    unitSectionMap f F a ≫
        (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv =
      (pullbackSectionsEtaleEvaluationIso F U).inv ≫
        (squareSectionsNatTrans (X₀ := U.left) (S₀ := X) (X₁ := W.left) (S₁ := S)
          U.hom W.hom f (unitRepresentativeArrow f a).left
          (Over.w (unitRepresentativeArrow f a)).symm).app F :=
  (congrArg
    (fun q => q ≫ (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv)
    (unitSectionNatTrans_app f a F)).symm.trans
      (NatTrans.congr_app (unitSectionNatTrans_square f a) F)

/-- The original square section map factors into its pullback, square and coefficient maps. -/
lemma squareSectionsMap_factor {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareSectionsMap f₀ f₁ g h e φ =
      (globalSectionsPullback h ((inverseImage f₀).obj F) ≫
        (globalSections X₁).map ((inverseImageSquareIso f₀ f₁ g h e).inv.app F)) ≫
          (globalSections X₁).map ((inverseImage f₁).map φ) :=
  (congrArg (fun q => globalSectionsPullback h ((inverseImage f₀).obj F) ≫ q)
    ((globalSections X₁).map_comp
      ((inverseImageSquareIso f₀ f₁ g h e).inv.app F)
      ((inverseImage f₁).map φ))).trans (Category.assoc _ _ _).symm

/-- The whole native square followed by a coefficient map is the original square section map. -/
lemma squareSectionsMap_natTrans {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareSectionsMap f₀ f₁ g h e φ =
      (squareSectionsNatTrans f₀ f₁ g h e).app F ≫
        (globalSections X₁).map ((inverseImage f₁).map φ) :=
  (squareSectionsMap_factor f₀ f₁ g h e φ).trans
    (congrArg (fun q => q ≫ (globalSections X₁).map ((inverseImage f₁).map φ))
      (squareSectionsNatTrans_app f₀ f₁ g h e F).symm)

/-- Pure isomorphism algebra for the original section-square factors. -/
lemma squareSectionEvaluation_of_unit {C : Type*} [Category* C]
    {A B D E H J : C} (e : A ≅ B) (e' : H ≅ J)
    (v : D ⟶ E) (u : B ⟶ D) (d : A ⟶ E) (k : E ⟶ H)
    (φ : D ⟶ J) (z : B ⟶ J) (m : A ⟶ H)
    (hu : u ≫ v = e.inv ≫ d) (hm : m = d ≫ k)
    (hn : φ ≫ e'.inv = v ≫ k) (hz : z = u ≫ φ) :
    m ≫ e'.hom = e.hom ≫ z := by
  have hs : e.inv ≫ m = z ≫ e'.inv := by
    calc
      _ = e.inv ≫ (d ≫ k) := congrArg (fun q => e.inv ≫ q) hm
      _ = (e.inv ≫ d) ≫ k := (Category.assoc _ _ _).symm
      _ = (u ≫ v) ≫ k := congrArg (fun q => q ≫ k) hu.symm
      _ = u ≫ (φ ≫ e'.inv) :=
        (Category.assoc _ _ _).trans (congrArg (fun q => u ≫ q) hn.symm)
      _ = (u ≫ φ) ≫ e'.inv := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun q => q ≫ e'.inv) hz.symm
  exact e'.eq_comp_inv.mp
    ((e.inv_comp_eq.mp hs).trans (Category.assoc e.hom z e'.inv).symm)

/-- The original adjoint coefficient map restricted along a specified etale test. -/
lemma adjointCoefficient_test {X S : Scheme.{u}} (f : S ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} S}
    (φ : (inverseImage f).obj F ⟶ G) {U : X.Etale} {W : S.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) :
    ((inverseImageAdjunction f).homEquiv _ _ φ).hom.app (op U) ≫ G.obj.map a.op =
      unitSectionMap f F a ≫ φ.hom.app (op W) := by
  change ((((inverseImageAdjunction f).unit.app F).hom.app (op U)) ≫
    φ.hom.app (op ((siteBaseChange f).obj U))) ≫ G.obj.map a.op =
    ((((inverseImageAdjunction f).unit.app F).hom.app (op U)) ≫
      ((inverseImage f).obj F).obj.map a.op) ≫ φ.hom.app (op W)
  exact (Category.assoc _ _ _).trans
    ((congrArg
      (fun q => ((inverseImageAdjunction f).unit.app F).hom.app (op U) ≫ q)
      (φ.hom.naturality a.op).symm).trans (Category.assoc _ _ _).symm)

/-- Original square section transfer is the original adjoint coefficient map on an etale test. -/
theorem squareSectionsMap_etaleEvaluation {X S : Scheme.{u}} (f : S ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} S}
    (φ : (inverseImage f).obj F ⟶ G) {U : X.Etale} {W : S.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) :
    squareSectionsMap (X₀ := U.left) (S₀ := X) (X₁ := W.left) (S₁ := S)
        U.hom W.hom f (unitRepresentativeArrow f a).left
        (Over.w (unitRepresentativeArrow f a)).symm φ ≫
      (pullbackSectionsEtaleEvaluationIso G W).hom =
    (pullbackSectionsEtaleEvaluationIso F U).hom ≫
      ((inverseImageAdjunction f).homEquiv _ _ φ).hom.app (op U) ≫ G.obj.map a.op := by
  let E := pullbackSectionsEtaleEvaluationIso F U
  let E' := pullbackSectionsEtaleEvaluationIso G W
  let v := (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv
  let d := (squareSectionsNatTrans (X₀ := U.left) (S₀ := X) (X₁ := W.left) (S₁ := S)
    U.hom W.hom f (unitRepresentativeArrow f a).left
    (Over.w (unitRepresentativeArrow f a)).symm).app F
  let k := (globalSections W.left).map ((inverseImage W.hom).map φ)
  exact squareSectionEvaluation_of_unit E E' v (unitSectionMap f F a) d k
    (φ.hom.app (op W))
    (((inverseImageAdjunction f).homEquiv _ _ φ).hom.app (op U) ≫ G.obj.map a.op)
    (squareSectionsMap (X₀ := U.left) (S₀ := X) (X₁ := W.left) (S₁ := S)
      U.hom W.hom f (unitRepresentativeArrow f a).left
      (Over.w (unitRepresentativeArrow f a)).symm φ)
    (unitSectionMap_square_etaleEvaluation f F a)
    (squareSectionsMap_natTrans (X₀ := U.left) (S₀ := X) (X₁ := W.left) (S₁ := S)
      U.hom W.hom f (unitRepresentativeArrow f a).left
      (Over.w (unitRepresentativeArrow f a)).symm φ)
    ((pullbackSectionsEtaleEvaluationNatIso W).inv.naturality φ)
    (adjointCoefficient_test f φ a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ActualDiagramLift
public import Aglib.CategoryTheory.Over.SitePullbackPasting
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Relative pullback tests and their original restriction comparisons

The relative object and the test object act on the same selected pullbacks.
Restriction keeps the original symmetry–pasting–symmetry component. Its
comparison with the other native pasting order uses the actual pullback
symmetry, and its naturality is proved in both variables before restricting
through a morphism-property site's full inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

universe u v uA vA

namespace CategoryTheory.Over.RelativeTests

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X T : C}

/-- Pull back the original test and retain its map to the original base. -/
abbrev tests (Y : Over X) : Over X ⥤ Over X :=
  Over.pullback Y.hom ⋙ Over.map Y.hom

/-- The relative-object map is the literal lift on the selected pullbacks. -/
def mapApp (U : Over X) {Y Z : Over X} (a : Y ⟶ Z) :
    (tests Y).obj U ⟶ (tests Z).obj U :=
  by
    have h : Limits.pullback.fst U.hom Y.hom ≫ U.hom =
        (Limits.pullback.snd U.hom Y.hom ≫ a.left) ≫ Z.hom := by
      calc
        _ = Limits.pullback.snd U.hom Y.hom ≫ Y.hom := Limits.pullback.condition
        _ = Limits.pullback.snd U.hom Y.hom ≫ (a.left ≫ Z.hom) :=
          congrArg (fun k => Limits.pullback.snd U.hom Y.hom ≫ k) (Over.w a).symm
        _ = _ := (Category.assoc _ _ _).symm
    refine Over.homMk
      (Limits.pullback.lift (Limits.pullback.fst U.hom Y.hom)
        (Limits.pullback.snd U.hom Y.hom ≫ a.left) h) ?_
    change Limits.pullback.lift (Limits.pullback.fst U.hom Y.hom)
        (Limits.pullback.snd U.hom Y.hom ≫ a.left) h ≫
        (Limits.pullback.snd U.hom Z.hom ≫ Z.hom) =
      Limits.pullback.snd U.hom Y.hom ≫ Y.hom
    calc
      _ = (Limits.pullback.snd U.hom Y.hom ≫ a.left) ≫ Z.hom :=
        Limits.pullback.lift_snd_assoc _ _ _ _
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (fun k => Limits.pullback.snd U.hom Y.hom ≫ k) (Over.w a))

@[reassoc]
theorem mapApp_fst (U : Over X) {Y Z : Over X} (a : Y ⟶ Z) :
    (mapApp U a).left ≫ Limits.pullback.fst U.hom Z.hom =
      Limits.pullback.fst U.hom Y.hom :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem mapApp_snd (U : Over X) {Y Z : Over X} (a : Y ⟶ Z) :
    (mapApp U a).left ≫ Limits.pullback.snd U.hom Z.hom =
      Limits.pullback.snd U.hom Y.hom ≫ a.left :=
  Limits.pullback.lift_snd _ _ _

@[reassoc]
theorem pullback_map_fst {S : C} (f : S ⟶ X) {U V : Over X} (b : U ⟶ V) :
    ((Over.pullback f).map b).left ≫ Limits.pullback.fst V.hom f =
      Limits.pullback.fst U.hom f ≫ b.left :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem pullback_map_snd {S : C} (f : S ⟶ X) {U V : Over X} (b : U ⟶ V) :
    ((Over.pullback f).map b).left ≫ Limits.pullback.snd V.hom f =
      Limits.pullback.snd U.hom f :=
  Limits.pullback.lift_snd _ _ _

/-- Relative-object maps are natural in every original Over test. -/
def map {Y Z : Over X} (a : Y ⟶ Z) : tests Y ⟶ tests Z where
  app U := mapApp U a
  naturality {U V} b := by
    apply Over.OverMorphism.ext
    change ((Over.pullback Y.hom).map b).left ≫ (mapApp V a).left =
      (mapApp U a).left ≫ ((Over.pullback Z.hom).map b).left
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc]
      rw [mapApp_fst V a, pullback_map_fst Y.hom b, pullback_map_fst Z.hom b,
        ← Category.assoc, mapApp_fst U a]
    · simp only [Category.assoc]
      rw [mapApp_snd V a, ← Category.assoc, pullback_map_snd Y.hom b,
        pullback_map_snd Z.hom b, mapApp_snd U a]

theorem map_id (Y : Over X) : map (𝟙 Y) = 𝟙 (tests Y) := by
  apply NatTrans.ext
  funext U
  apply Over.OverMorphism.ext
  change (mapApp U (𝟙 Y)).left = 𝟙 _
  apply Limits.pullback.hom_ext
  · rw [mapApp_fst, Category.id_comp]
  · rw [mapApp_snd, Over.id_left, Category.comp_id, Category.id_comp]

theorem map_comp {Y Z W : Over X} (a : Y ⟶ Z) (b : Z ⟶ W) :
    map (a ≫ b) = map a ≫ map b := by
  apply NatTrans.ext
  funext U
  apply Over.OverMorphism.ext
  change (mapApp U (a ≫ b)).left = (mapApp U a).left ≫ (mapApp U b).left
  apply Limits.pullback.hom_ext
  · rw [mapApp_fst, Category.assoc, mapApp_fst, mapApp_fst]
  · rw [mapApp_snd, Category.assoc, mapApp_snd,
      ← Category.assoc (mapApp U a).left (Limits.pullback.snd U.hom Z.hom) b.left,
      mapApp_snd]
    exact congrArg (fun q => Limits.pullback.snd U.hom Y.hom ≫ q)
      (Over.comp_left Y Z W a b) |>.trans (Category.assoc _ _ _).symm

/-- The two variables form one actual functor, with the original map lifts. -/
def functor : Over X ⥤ (Over X ⥤ Over X) where
  obj := tests
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The original symmetry identifies the two selected base-change orders. -/
def symmetryOverIso (g : T ⟶ X) (Y : Over X) :
    Over.mk (Limits.pullback.fst g Y.hom) ≅ (Over.pullback g).obj Y :=
  Over.isoMk (pullbackSymmetry g Y.hom) (pullbackSymmetry_hom_comp_snd g Y.hom)

/-- The original symmetry–pasting–symmetry comparison, with its selected order. -/
def restrictionSchemeIso (g : T ⟶ X) (Y : Over X) (U : Over T) :
    Limits.pullback U.hom (Limits.pullback.snd Y.hom g) ≅
      Limits.pullback (U.hom ≫ g) Y.hom :=
  pullbackSymmetry U.hom (Limits.pullback.snd Y.hom g) ≪≫
    pullbackLeftPullbackSndIso Y.hom g U.hom ≪≫
      pullbackSymmetry Y.hom (U.hom ≫ g)

@[reassoc]
theorem restrictionSchemeIso_fst (g : T ⟶ X) (Y : Over X) (U : Over T) :
    (restrictionSchemeIso g Y U).hom ≫ Limits.pullback.fst (U.hom ≫ g) Y.hom =
      Limits.pullback.fst U.hom (Limits.pullback.snd Y.hom g) := by
  simp only [restrictionSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
    pullbackLeftPullbackSndIso_hom_snd]

@[reassoc]
theorem restrictionSchemeIso_snd (g : T ⟶ X) (Y : Over X) (U : Over T) :
    (restrictionSchemeIso g Y U).hom ≫ Limits.pullback.snd (U.hom ≫ g) Y.hom =
      Limits.pullback.snd U.hom (Limits.pullback.snd Y.hom g) ≫
        Limits.pullback.fst Y.hom g := by
  simp only [restrictionSchemeIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackLeftPullbackSndIso_hom_fst]

/-- The existing opposite-order pasting gives this exact component after the
actual relative symmetry map; equality is proved on both original projections. -/
theorem restrictionSchemeIso_hom_eq_pasting (g : T ⟶ X) (Y : Over X) (U : Over T) :
    (restrictionSchemeIso g Y U).hom =
      (mapApp U (symmetryOverIso g Y).inv).left ≫
        ((Over.pullbackPostcomposeIso Y.hom g).hom.app U).left := by
  have hf : (mapApp U (symmetryOverIso g Y).inv).left ≫
      Limits.pullback.fst U.hom (Limits.pullback.fst g Y.hom) =
      Limits.pullback.fst U.hom (Limits.pullback.snd Y.hom g) :=
    mapApp_fst U (symmetryOverIso g Y).inv
  have hs : (mapApp U (symmetryOverIso g Y).inv).left ≫
      Limits.pullback.snd U.hom (Limits.pullback.fst g Y.hom) =
      Limits.pullback.snd U.hom (Limits.pullback.snd Y.hom g) ≫
        (pullbackSymmetry g Y.hom).inv :=
    mapApp_snd U (symmetryOverIso g Y).inv
  apply Limits.pullback.hom_ext
  · rw [restrictionSchemeIso_fst, Category.assoc,
      Over.pullbackPostcomposeIso_hom_fst, hf]
  · rw [restrictionSchemeIso_snd, Category.assoc,
      Over.pullbackPostcomposeIso_hom_snd, ← Category.assoc, hs,
      Category.assoc, pullbackSymmetry_inv_comp_snd]

/-- The selected comparison is an isomorphism over the original base. -/
def restrictionOverIso (g : T ⟶ X) (Y : Over X) (U : Over T) :
    (Over.map g).obj ((tests ((Over.pullback g).obj Y)).obj U) ≅
      (tests Y).obj ((Over.map g).obj U) :=
  Over.isoMk (restrictionSchemeIso g Y U) (by
    change (restrictionSchemeIso g Y U).hom ≫
        (Limits.pullback.snd (U.hom ≫ g) Y.hom ≫ Y.hom) =
      (Limits.pullback.snd U.hom (Limits.pullback.snd Y.hom g) ≫
        Limits.pullback.snd Y.hom g) ≫ g
    rw [← Category.assoc, restrictionSchemeIso_snd]
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc])

/-- Naturality in every test, before any morphism-property restriction. -/
def restrictionIso (g : T ⟶ X) (Y : Over X) :
    tests ((Over.pullback g).obj Y) ⋙ Over.map g ≅ Over.map g ⋙ tests Y :=
  NatIso.ofComponents (restrictionOverIso g Y) (by
    intro U V b
    apply Over.OverMorphism.ext
    change ((Over.pullback (Limits.pullback.snd Y.hom g)).map b).left ≫
        (restrictionSchemeIso g Y V).hom =
      (restrictionSchemeIso g Y U).hom ≫
        ((Over.pullback Y.hom).map ((Over.map g).map b)).left
    have hf : ((Over.pullback Y.hom).map ((Over.map g).map b)).left ≫
        Limits.pullback.fst (V.hom ≫ g) Y.hom =
        Limits.pullback.fst (U.hom ≫ g) Y.hom ≫ b.left :=
      pullback_map_fst Y.hom ((Over.map g).map b)
    have hs : ((Over.pullback Y.hom).map ((Over.map g).map b)).left ≫
        Limits.pullback.snd (V.hom ≫ g) Y.hom =
        Limits.pullback.snd (U.hom ≫ g) Y.hom :=
      pullback_map_snd Y.hom ((Over.map g).map b)
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, restrictionSchemeIso_fst, pullback_map_fst]
      rw [hf, ← Category.assoc, restrictionSchemeIso_fst]
    · simp only [Category.assoc, restrictionSchemeIso_snd, pullback_map_snd_assoc]
      rw [hs, restrictionSchemeIso_snd])

/-- The complete square in the relative-object variable uses the same lifts. -/
theorem restrictionIso_relative (g : T ⟶ X) {Y Z : Over X} (a : Y ⟶ Z)
    (U : Over T) :
    (Over.map g).map ((map ((Over.pullback g).map a)).app U) ≫
        (restrictionIso g Z).hom.app U =
      (restrictionIso g Y).hom.app U ≫ (map a).app ((Over.map g).obj U) := by
  apply Over.OverMorphism.ext
  change (mapApp U ((Over.pullback g).map a)).left ≫
      (restrictionSchemeIso g Z U).hom =
    (restrictionSchemeIso g Y U).hom ≫ (mapApp ((Over.map g).obj U) a).left
  have hfT : (mapApp U ((Over.pullback g).map a)).left ≫
      Limits.pullback.fst U.hom (Limits.pullback.snd Z.hom g) =
      Limits.pullback.fst U.hom (Limits.pullback.snd Y.hom g) :=
    mapApp_fst U ((Over.pullback g).map a)
  have hfS : (mapApp ((Over.map g).obj U) a).left ≫
      Limits.pullback.fst (U.hom ≫ g) Z.hom =
      Limits.pullback.fst (U.hom ≫ g) Y.hom :=
    mapApp_fst ((Over.map g).obj U) a
  have hsT : (mapApp U ((Over.pullback g).map a)).left ≫
      Limits.pullback.snd U.hom (Limits.pullback.snd Z.hom g) =
      Limits.pullback.snd U.hom (Limits.pullback.snd Y.hom g) ≫
        ((Over.pullback g).map a).left :=
    mapApp_snd U ((Over.pullback g).map a)
  have hsS : (mapApp ((Over.map g).obj U) a).left ≫
      Limits.pullback.snd (U.hom ≫ g) Z.hom =
      Limits.pullback.snd (U.hom ≫ g) Y.hom ≫ a.left :=
    mapApp_snd ((Over.map g).obj U) a
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, restrictionSchemeIso_fst]
    rw [hfT, hfS, restrictionSchemeIso_fst]
  · simp only [Category.assoc, restrictionSchemeIso_snd]
    rw [hsS, ← Category.assoc, hsT, Category.assoc,
      pullback_map_fst, restrictionSchemeIso_snd_assoc]

end CategoryTheory.Over.RelativeTests

namespace CategoryTheory.MorphismProperty.Over.RelativeTests

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (P : MorphismProperty C)
  {X T : C}

/-- Restrict the original plain-Over test functor through the actual inclusion. -/
abbrev tests (Y : CategoryTheory.Over X) : P.Over ⊤ X ⥤ CategoryTheory.Over X :=
  MorphismProperty.Over.forget P ⊤ X ⋙ CategoryTheory.Over.RelativeTests.tests Y

/-- The restricted relative map keeps the same original pullback lift. -/
def map {Y Z : CategoryTheory.Over X} (a : Y ⟶ Z) : tests P Y ⟶ tests P Z :=
  Functor.whiskerLeft (MorphismProperty.Over.forget P ⊤ X)
    (CategoryTheory.Over.RelativeTests.map a)

theorem map_id (Y : CategoryTheory.Over X) : map P (𝟙 Y) = 𝟙 (tests P Y) := by
  simp only [map, CategoryTheory.Over.RelativeTests.map_id, Functor.whiskerLeft_id']

theorem map_comp {Y Z W : CategoryTheory.Over X} (a : Y ⟶ Z) (b : Z ⟶ W) :
    map P (a ≫ b) = map P a ≫ map P b := by
  simp only [map, CategoryTheory.Over.RelativeTests.map_comp, Functor.whiskerLeft_comp]

/-- The restricted two-variable functor does not identify P.Over with Over. -/
def functor : CategoryTheory.Over X ⥤ (P.Over ⊤ X ⥤ CategoryTheory.Over X) where
  obj := tests P
  map := map P
  map_id := map_id P
  map_comp := map_comp P

section Restriction

variable [P.IsStableUnderComposition]

/-- The actual site inclusion restricts the already proved test comparison. -/
def restrictionIso (g : T ⟶ X) (hg : P g) (Y : CategoryTheory.Over X) :
    tests P ((CategoryTheory.Over.pullback g).obj Y) ⋙ CategoryTheory.Over.map g ≅
      MorphismProperty.Over.map ⊤ hg ⋙ tests P Y :=
  NatIso.ofComponents
    (fun U => CategoryTheory.Over.RelativeTests.restrictionOverIso g Y
      ((MorphismProperty.Over.forget P ⊤ T).obj U))
    (fun {_ _} a =>
      (CategoryTheory.Over.RelativeTests.restrictionIso g Y).hom.naturality
        ((MorphismProperty.Over.forget P ⊤ T).map a))

/-- Relative-object naturality is the original plain-Over equation at the
actual included test, rather than a replacement site-map assumption. -/
theorem restrictionIso_relative (g : T ⟶ X) (hg : P g)
    {Y Z : CategoryTheory.Over X} (a : Y ⟶ Z) (U : P.Over ⊤ T) :
    (CategoryTheory.Over.map g).map
        ((map P ((CategoryTheory.Over.pullback g).map a)).app U) ≫
        (restrictionIso P g hg Z).hom.app U =
      (restrictionIso P g hg Y).hom.app U ≫
        (map P a).app ((MorphismProperty.Over.map ⊤ hg).obj U) :=
  CategoryTheory.Over.RelativeTests.restrictionIso_relative g a
    ((MorphismProperty.Over.forget P ⊤ T).obj U)

end Restriction

variable {A : Type uA} [Category.{vA} A]

/-- Original coordinates obtained by evaluating the original relative tests. -/
def coordinates (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A) (Y : CategoryTheory.Over X) :
    (P.Over ⊤ X)ᵒᵖ ⥤ A :=
  (tests P Y).op ⋙ F

/-- Coordinate transport is literal precomposition with the original test map. -/
def coordinateMap (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A)
    {Y Z : CategoryTheory.Over X} (a : Y ⟶ Z) :
    coordinates P F Z ⟶ coordinates P F Y :=
  Functor.whiskerRight (NatTrans.op (map P a)) F

theorem coordinateMap_id (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A)
    (Y : CategoryTheory.Over X) :
    coordinateMap P F (𝟙 Y) = 𝟙 (coordinates P F Y) := by
  apply NatTrans.ext
  funext U
  change F.map ((map P (𝟙 Y)).app U.unop).op = 𝟙 _
  rw [map_id]
  exact F.map_id _

theorem coordinateMap_comp (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A)
    {Y Z W : CategoryTheory.Over X} (a : Y ⟶ Z) (b : Z ⟶ W) :
    coordinateMap P F (a ≫ b) = coordinateMap P F b ≫ coordinateMap P F a := by
  apply NatTrans.ext
  funext U
  change F.map ((map P (a ≫ b)).app U.unop).op =
    F.map ((map P b).app U.unop).op ≫ F.map ((map P a).app U.unop).op
  rw [map_comp]
  exact F.map_comp _ _

/-- The complete coordinate functor, with both original variables and map laws. -/
def coordinateFunctor (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A) :
    (CategoryTheory.Over X)ᵒᵖ ⥤ ((P.Over ⊤ X)ᵒᵖ ⥤ A) where
  obj Y := coordinates P F Y.unop
  map a := coordinateMap P F a.unop
  map_id Y := coordinateMap_id P F Y.unop
  map_comp a b := coordinateMap_comp P F b.unop a.unop

variable [P.IsStableUnderComposition]

/-- The full original op/whisker/associator construction transports a supplied
section comparison along the selected restriction-test isomorphism. -/
def coordinateRestrictionIso (g : T ⟶ X) (hg : P g)
    (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A)
    (G : (CategoryTheory.Over T)ᵒᵖ ⥤ A)
    (e : (CategoryTheory.Over.map g).op ⋙ F ≅ G) (Y : CategoryTheory.Over X) :
    (MorphismProperty.Over.map ⊤ hg).op ⋙ coordinates P F Y ≅
      coordinates P G ((CategoryTheory.Over.pullback g).obj Y) :=
  (Functor.associator (MorphismProperty.Over.map ⊤ hg).op (tests P Y).op F).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.opComp (MorphismProperty.Over.map ⊤ hg) (tests P Y)).symm F ≪≫
    Functor.isoWhiskerRight (NatIso.op (restrictionIso P g hg Y)) F ≪≫
    Functor.isoWhiskerRight
      (Functor.opComp (tests P ((CategoryTheory.Over.pullback g).obj Y))
        (CategoryTheory.Over.map g)) F ≪≫
    Functor.associator (tests P ((CategoryTheory.Over.pullback g).obj Y)).op
      (CategoryTheory.Over.map g).op F ≪≫
    Functor.isoWhiskerLeft (tests P ((CategoryTheory.Over.pullback g).obj Y)).op e

/-- The actual component is the original test comparison followed by the
supplied original section comparison; all associators have been evaluated. -/
theorem coordinateRestrictionIso_hom_app (g : T ⟶ X) (hg : P g)
    (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A)
    (G : (CategoryTheory.Over T)ᵒᵖ ⥤ A)
    (e : (CategoryTheory.Over.map g).op ⋙ F ≅ G)
    (Y : CategoryTheory.Over X) (U : P.Over ⊤ T) :
    (coordinateRestrictionIso P g hg F G e Y).hom.app (Opposite.op U) =
      F.map ((restrictionIso P g hg Y).hom.app U).op ≫
        e.hom.app (Opposite.op ((tests P ((CategoryTheory.Over.pullback g).obj Y)).obj U)) := by
  change (𝟙 _) ≫ F.map (𝟙 _) ≫
      F.map ((restrictionIso P g hg Y).hom.app U).op ≫ F.map (𝟙 _) ≫
      (𝟙 _) ≫ e.hom.app
        (Opposite.op ((tests P ((CategoryTheory.Over.pullback g).obj Y)).obj U)) = _
  simp only [F.map_id, Category.id_comp]

/-- Naturality of the supplied section comparison and the proved relative test
square give the full coordinate square in an independent value category. -/
theorem coordinateRestrictionIso_relative (g : T ⟶ X) (hg : P g)
    (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A)
    (G : (CategoryTheory.Over T)ᵒᵖ ⥤ A)
    (e : (CategoryTheory.Over.map g).op ⋙ F ≅ G)
    {Y Z : CategoryTheory.Over X} (a : Y ⟶ Z) :
    Functor.whiskerLeft (MorphismProperty.Over.map ⊤ hg).op (coordinateMap P F a) ≫
        (coordinateRestrictionIso P g hg F G e Y).hom =
      (coordinateRestrictionIso P g hg F G e Z).hom ≫
        coordinateMap P G ((CategoryTheory.Over.pullback g).map a) := by
  apply NatTrans.ext
  funext U
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  change (coordinateMap P F a).app
        ((MorphismProperty.Over.map ⊤ hg).op.obj (Opposite.op U.unop)) ≫
      (coordinateRestrictionIso P g hg F G e Y).hom.app (Opposite.op U.unop) =
    (coordinateRestrictionIso P g hg F G e Z).hom.app (Opposite.op U.unop) ≫
      (coordinateMap P G ((CategoryTheory.Over.pullback g).map a)).app (Opposite.op U.unop)
  rw [coordinateRestrictionIso_hom_app P g hg F G e Y U.unop,
    coordinateRestrictionIso_hom_app P g hg F G e Z U.unop]
  let t := (map P ((CategoryTheory.Over.pullback g).map a)).app U.unop
  have htest := congrArg (fun k => F.map k.op) (restrictionIso_relative P g hg a U.unop)
  have he := e.hom.naturality t.op
  change F.map ((CategoryTheory.Over.map g).map t).op ≫
      e.hom.app (Opposite.op ((tests P ((CategoryTheory.Over.pullback g).obj Y)).obj U.unop)) =
    e.hom.app (Opposite.op ((tests P ((CategoryTheory.Over.pullback g).obj Z)).obj U.unop)) ≫
      G.map t.op at he
  change F.map ((map P a).app ((MorphismProperty.Over.map ⊤ hg).obj U.unop)).op ≫
      (F.map ((restrictionIso P g hg Y).hom.app U.unop).op ≫ _) =
    (F.map ((restrictionIso P g hg Z).hom.app U.unop).op ≫ _) ≫ G.map t.op
  rw [op_comp, op_comp, F.map_comp, F.map_comp] at htest
  rw [← Category.assoc, ← htest, Category.assoc, he, Category.assoc]

/-- The complete relative-object comparison has the same original components. -/
def coordinateRestrictionNatIso (g : T ⟶ X) (hg : P g)
    (F : (CategoryTheory.Over X)ᵒᵖ ⥤ A)
    (G : (CategoryTheory.Over T)ᵒᵖ ⥤ A)
    (e : (CategoryTheory.Over.map g).op ⋙ F ≅ G) :
    coordinateFunctor P F ⋙
        (Functor.whiskeringLeft (P.Over ⊤ T)ᵒᵖ (P.Over ⊤ X)ᵒᵖ A).obj
          (MorphismProperty.Over.map ⊤ hg).op ≅
      (CategoryTheory.Over.pullback g).op ⋙ coordinateFunctor P G :=
  NatIso.ofComponents
    (fun Y => coordinateRestrictionIso P g hg F G e Y.unop)
    (fun {_ _} a => coordinateRestrictionIso_relative P g hg F G e a.unop)

end CategoryTheory.MorphismProperty.Over.RelativeTests

/- The original adjunctions evaluate the actual pasted section by its projections. -/

namespace CategoryTheory.Over.RelativeTests

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The original Over Hom equivalence has the selected first pullback projection. -/
theorem mapPullbackAdj_homEquiv_fst {X S : C} (f : X ⟶ S)
    (U : Over X) (H : Over S) (a : (Over.map f).obj U ⟶ H) :
    ((Over.mapPullbackAdj f).homEquiv U H a).left ≫
        Limits.pullback.fst H.hom f = a.left := by
  simp only [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact Limits.pullback.lift_fst _ _ _

/-- Its inverse uses the counit of the same actual adjunction. -/
theorem mapPullbackAdj_homEquiv_symm_left {X S : C} (f : X ⟶ S)
    (U : Over X) (H : Over S) (a : U ⟶ (Over.pullback f).obj H) :
    (((Over.mapPullbackAdj f).homEquiv U H).symm a).left =
      a.left ≫ Limits.pullback.fst H.hom f := by
  rw [Adjunction.homEquiv_counit]
  simp only [Over.comp_left, Over.map_map_left, Over.mapPullbackAdj_counit_left]

private theorem square_inv_fst_fst {X S X' S' : C}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (H : Over S) :
    ((Over.pullbackSquareIso f f' g g' h).inv.app H).left ≫
        Limits.pullback.fst (Limits.pullback.snd H.hom g) f' ≫
        Limits.pullback.fst H.hom g =
      Limits.pullback.fst (Limits.pullback.snd H.hom f) g' ≫
        Limits.pullback.fst H.hom f := by
  have hh := congrArg
    (fun k => ((Over.pullbackSquareIso f f' g g' h).inv.app H).left ≫ k)
    (Over.pullbackSquareIso_fst_fst f f' g g' h H)
  simpa only [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id_app,
    Over.id_left, Category.id_comp] using hh.symm

/-- The same original q/p/g adjunctions evaluate the pasted section by its
original first projection. This is a value law, not a supplied mate equation. -/
theorem pasting_homEquiv_fst {X S T : C} (f : X ⟶ S) (g : T ⟶ S)
    (H : Over S) (U : Over T)
    (a : (Over.pullback f).obj ((Over.map g).obj U) ⟶ (Over.pullback f).obj H) :
    (Equiv.symm
      ((Over.mapPullbackAdj (Limits.pullback.fst g f)).homEquiv
        ((Over.pullback (Limits.pullback.fst g f)).obj U) ((Over.pullback g).obj H))
      ((Over.mapPullbackAdj (Limits.pullback.snd g f)).homEquiv
          ((Over.pullback (Limits.pullback.fst g f)).obj U) ((Over.pullback f).obj H)
          ((Over.pullbackPostcomposeIso f g).hom.app U ≫ a) ≫
        (Over.pullbackSquareIso f (Limits.pullback.fst g f) g
          (Limits.pullback.snd g f) Limits.pullback.condition).inv.app H)).left ≫
        Limits.pullback.fst H.hom g =
      ((Over.pullbackPostcomposeIso f g).hom.app U).left ≫ a.left ≫
        Limits.pullback.fst H.hom f := by
  let m := (Over.mapPullbackAdj (Limits.pullback.snd g f)).homEquiv
    ((Over.pullback (Limits.pullback.fst g f)).obj U) ((Over.pullback f).obj H)
    ((Over.pullbackPostcomposeIso f g).hom.app U ≫ a)
  rw [mapPullbackAdj_homEquiv_symm_left, Over.comp_left]
  change ((m.left ≫
      ((Over.pullbackSquareIso f (Limits.pullback.fst g f) g
        (Limits.pullback.snd g f) Limits.pullback.condition).inv.app H).left) ≫
      Limits.pullback.fst (Limits.pullback.snd H.hom g) (Limits.pullback.fst g f)) ≫
      Limits.pullback.fst H.hom g = _
  rw [Category.assoc, Category.assoc, square_inv_fst_fst, ← Category.assoc]
  have hm : m.left ≫ Limits.pullback.fst (Limits.pullback.snd H.hom f)
      (Limits.pullback.snd g f) =
      ((Over.pullbackPostcomposeIso f g).hom.app U ≫ a).left :=
    mapPullbackAdj_homEquiv_fst (Limits.pullback.snd g f)
      ((Over.pullback (Limits.pullback.fst g f)).obj U) ((Over.pullback f).obj H)
      ((Over.pullbackPostcomposeIso f g).hom.app U ≫ a)
  rw [hm]
  exact Category.assoc _ _ _


/-- The complete original pasted section is the same map through the original
q/p/g adjunctions. Both projections use the selected pullback and symmetry maps. -/
theorem pasting_homEquiv {S T : C} (g : T ⟶ S) (Y : Over S) (H : Over S) (U : Over T)
    (a : (Over.pullback Y.hom).obj ((Over.map g).obj U) ⟶
      (Over.pullback Y.hom).obj H) :
    (Over.mapPullbackAdj g).homEquiv ((tests ((Over.pullback g).obj Y)).obj U) H
        ((restrictionOverIso g Y U).hom ≫
          ((Over.mapPullbackAdj Y.hom).homEquiv _ H).symm a) =
      mapApp U (symmetryOverIso g Y).inv ≫
        ((Over.mapPullbackAdj (Limits.pullback.fst g Y.hom)).homEquiv
          ((Over.pullback (Limits.pullback.fst g Y.hom)).obj U)
          ((Over.pullback g).obj H)).symm
          ((Over.mapPullbackAdj (Limits.pullback.snd g Y.hom)).homEquiv
              ((Over.pullback (Limits.pullback.fst g Y.hom)).obj U)
              ((Over.pullback Y.hom).obj H)
              ((Over.pullbackPostcomposeIso Y.hom g).hom.app U ≫ a) ≫
            (Over.pullbackSquareIso Y.hom (Limits.pullback.fst g Y.hom) g
              (Limits.pullback.snd g Y.hom) Limits.pullback.condition).inv.app H) := by
  let q := Limits.pullback.fst g Y.hom
  let p := Limits.pullback.snd g Y.hom
  let D := (Over.pullback q).obj U
  let e := (Over.pullbackPostcomposeIso Y.hom g).hom.app U
  let j := mapApp U (symmetryOverIso g Y).inv
  let r := (restrictionOverIso g Y U).hom
  let t := (Over.pullbackSquareIso Y.hom q g p Limits.pullback.condition).inv.app H
  let m := (Over.mapPullbackAdj p).homEquiv D ((Over.pullback Y.hom).obj H) (e ≫ a)
  let k := ((Over.mapPullbackAdj q).homEquiv D ((Over.pullback g).obj H)).symm (m ≫ t)
  have hK : k.left ≫ Limits.pullback.fst H.hom g =
      e.left ≫ a.left ≫ Limits.pullback.fst H.hom Y.hom :=
    pasting_homEquiv_fst Y.hom g H U a
  have hR : r.left = j.left ≫ e.left := restrictionSchemeIso_hom_eq_pasting g Y U
  have ha := mapPullbackAdj_homEquiv_symm_left Y.hom
    ((Over.pullback Y.hom).obj ((Over.map g).obj U)) H a
  change (Over.mapPullbackAdj g).homEquiv _ H
    (r ≫ ((Over.mapPullbackAdj Y.hom).homEquiv _ H).symm a) = j ≫ k
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · have hl := mapPullbackAdj_homEquiv_fst g _ H
      (r ≫ ((Over.mapPullbackAdj Y.hom).homEquiv _ H).symm a)
    rw [hl, Over.comp_left, Over.comp_left, Category.assoc, hK, hR, ha]
    simp only [Category.assoc]
  · exact (Over.w _).trans (Over.w (j ≫ k)).symm

end CategoryTheory.Over.RelativeTests

/-! The complete finite comparison equations are proved before any native
coefficient objects are supplied. Their hypotheses are the actual original
comparison and inverse equations, without a new comparison model. -/
namespace CategoryTheory.Over.RelativeTests.Comparison

universe uI vI uC vC uD vD

theorem square_app
    {A D : Type*} [Category* A] [Category* D]
    {F₀ F₁ F₂ F₃ : A ⥤ D}
    (e : F₁ ≅ F₂) (a : F₀ ≅ F₁) (b : F₀ ≅ F₃) (c : F₃ ≅ F₂)
    (he : e = a.symm ≪≫ b ≪≫ c) (V : A) :
    a.hom.app V ≫ e.hom.app V = b.hom.app V ≫ c.hom.app V := by
  have hw : a.hom ≫ e.hom = b.hom ≫ c.hom := by
    rw [he]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact congrArg (fun k => k.app V) hw

theorem cancel
    {D : Type*} [Category* D] {A B C E Z : D}
    (a : A ⟶ B) (i : B ⟶ A) (s : B ⟶ C) (b : A ⟶ E) (c : E ⟶ C)
    (hi : i ≫ a = 𝟙 B) (hs : a ≫ s = b ≫ c)
    (p : C ⟶ Z) (q : B ⟶ Z) (u : A ⟶ Z) (v : E ⟶ Z)
    (hq : a ≫ q = u) (hp : c ≫ p = v) (hb : b ≫ v = u) : s ≫ p = q := by
  have hh : a ≫ (s ≫ p) = a ≫ q := by
    rw [← Category.assoc, hs, Category.assoc, hp, hb, hq]
  have hh' := congrArg (fun k => i ≫ k) hh
  simpa only [← Category.assoc, hi, Category.id_comp] using hh'

theorem post_cancel
    {D : Type*} [Category* D] {A B C E Q P U V : D}
    (a : A ⟶ B) (i : B ⟶ A) (s : B ⟶ C) (b : A ⟶ E) (c : E ⟶ C)
    (q : B ⟶ Q) (p : C ⟶ P) (u : Q ⟶ U) (v : U ⟶ V)
    (w : P ⟶ V) (wi : V ⟶ P) (r : A ⟶ U) (z : E ⟶ V)
    (hi : i ≫ a = 𝟙 B) (hs : a ≫ s = b ≫ c)
    (hq : a ≫ q ≫ u = r) (hp : c ≫ p ≫ w = z)
    (hw : w ≫ wi = 𝟙 P) (hb : b ≫ z = r ≫ v) :
    s ≫ p = q ≫ u ≫ v ≫ wi := by
  have hh : a ≫ (s ≫ p) = a ≫ (q ≫ u ≫ v ≫ wi) := by
    calc
      _ = b ≫ (c ≫ p) := by rw [← Category.assoc, hs, Category.assoc]
      _ = b ≫ ((c ≫ p ≫ w) ≫ wi) := by
        simp only [Category.assoc, hw, Category.comp_id]
      _ = b ≫ (z ≫ wi) := congrArg (fun k => b ≫ (k ≫ wi)) hp
      _ = (r ≫ v) ≫ wi := by rw [← Category.assoc, hb]
      _ = _ := by rw [← hq]; simp only [Category.assoc]
  have hh' := congrArg (fun k => i ≫ k) hh
  simpa only [← Category.assoc, hi, Category.id_comp] using hh'

theorem transport_cancel
    {D : Type*} [Category* D] {A B C E F : D}
    (a : A ⟶ B) (b : B ⟶ A) (c : A ⟶ C) (d : C ⟶ E)
    (e : E ⟶ F) (i : F ⟶ E) (δ : B ⟶ F)
    (hab : a ≫ b = 𝟙 A) (hei : e ≫ i = 𝟙 E)
    (hδ : δ = b ≫ c ≫ d ≫ e) : a ≫ δ ≫ i = c ≫ d := by
  rw [hδ]
  calc
    a ≫ (b ≫ c ≫ d ≫ e) ≫ i = ((a ≫ b) ≫ c ≫ d) ≫ (e ≫ i) := by
      simp only [Category.assoc]
    _ = c ≫ d := by rw [hab, hei, Category.id_comp, Category.comp_id]

theorem mapped_comparison
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (F : C ⥤ D)
    {A B E Z : C} {U V : D}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ Z) (d : A ⟶ E)
    (hd : a ≫ b = d) (p : U ⟶ F.obj A) (q : F.obj Z ⟶ V) :
    p ≫ F.map d ≫ F.map c ≫ q =
      p ≫ F.map a ≫ F.map (b ≫ c) ≫ q := by
  rw [← hd]
  simp only [Functor.map_comp, Category.assoc]

/-- The given actual arrows satisfy both functor laws, using the complete
original faithful lift without retaining another operational functor. -/
theorem diagram_laws
    {I : Type uI} [Category.{vI} I]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) [F.Faithful] (K : I ⥤ D) (A : I → C)
    (e : ∀ i, K.obj i ≅ F.obj (A i))
    (g : ∀ {i j : I}, (i ⟶ j) → (A i ⟶ A j))
    (hg : ∀ {i j : I} (f : i ⟶ j),
      F.map (g f) = (e i).inv ≫ K.map f ≫ (e j).hom) :
    (∀ i, g (𝟙 i) = 𝟙 (A i)) ∧
      (∀ {i j k : I} (a : i ⟶ j) (b : j ⟶ k), g (a ≫ b) = g a ≫ g b) := by
  constructor
  · intro i
    exact (Functor.actualDiagramLift F K A e g hg).map_id i
  · intro i j k a b
    exact (Functor.actualDiagramLift F K A e g hg).map_comp a b

/-- Cancel the original comparison edges at the actual mapped arrows.
All mapped values and middle arrows are inferred from the producer equations. -/
theorem constantGroupSquare_mapped_of_inferred_equations
    {D : Type*} [Category* D]
    {SL LP L TR RP R LM RM Z E SC TC LC RC : D}
    {left right : L ⟶ Z}
    (u : SL ⟶ LP) (v : LP ⟶ L) (z : Z ⟶ E)
    {sX : SL ⟶ TR} {sC : SC ⟶ TC}
    {p : TR ⟶ RP} {q : RP ⟶ R} {t : L ⟶ R}
    {l₁ : L ⟶ LM} {l₂ : LM ⟶ Z}
    {r₁ : R ⟶ RM} {r₂ : RM ⟶ Z} {tail : R ⟶ Z}
    {iL : SL ⟶ SC} {iT : TR ⟶ TC}
    {cL₁ : SC ⟶ LC} {cL₂ : LC ⟶ E}
    {cT₁ : TC ⟶ RC} {cT₂ : RC ⟶ E}
    (hR : sX ≫ p ≫ q = u ≫ v ≫ t)
    (hN : iL ≫ sC = sX ≫ iT)
    (hC : sC ≫ cT₁ ≫ cT₂ = cL₁ ≫ cL₂)
    (hL : u ≫ v ≫ l₁ ≫ l₂ ≫ z = iL ≫ cL₁ ≫ cL₂)
    (hT : p ≫ q ≫ r₁ ≫ r₂ ≫ z = iT ≫ cT₁ ≫ cT₂)
    (hMapL : left = l₁ ≫ l₂)
    (hMapR : right = t ≫ tail)
    (hMapTail : tail = r₁ ≫ r₂)
    (hu : Epi u) (hv : Epi v) (hz : Mono z) : left = right := by
  let : Epi u := hu
  let : Epi v := hv
  let : Mono z := hz
  rw [hMapL, hMapR, hMapTail]
  apply (cancel_mono z).mp
  apply (cancel_epi v).mp
  apply (cancel_epi u).mp
  simp only [Category.assoc]
  calc
    u ≫ v ≫ l₁ ≫ l₂ ≫ z = iL ≫ cL₁ ≫ cL₂ := hL
    _ = iL ≫ sC ≫ cT₁ ≫ cT₂ := by rw [hC]
    _ = sX ≫ iT ≫ cT₁ ≫ cT₂ := by
      rw [← Category.assoc, hN, Category.assoc]
    _ = sX ≫ p ≫ q ≫ r₁ ≫ r₂ ≫ z := by rw [hT]
    _ = u ≫ v ≫ t ≫ r₁ ≫ r₂ ≫ z := by
      have hp := congrArg (fun k => k ≫ r₁ ≫ r₂ ≫ z) hR
      simpa only [Category.assoc] using hp



/-- Map the original two-factor equation before any concrete coefficient is supplied. -/
theorem map_pair
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (F : C ⥤ D)
    {A B E Z : C} (a : A ⟶ B) (b : B ⟶ Z) (c : A ⟶ E) (d : E ⟶ Z)
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  exact (F.map_comp a b).symm.trans
    ((congrArg F.map h).trans (F.map_comp c d))

/-- Reassociate the mapped actual producer relation before supplying any native tail. -/
theorem map_relation_assoc
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) {A B E : C} {a : A ⟶ B} {b : B ⟶ E} {d : A ⟶ E}
    (h : a ≫ b = d) (Z : D) (t : F.obj E ⟶ Z) :
    F.map a ≫ F.map b ≫ t = F.map d ≫ t := by
  rw [← Category.assoc, ← F.map_comp, h]

/-- Map the complete original three-factor coefficient normalization. -/
theorem map_three_two
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (F : C ⥤ D)
    {A B E Z W : C} (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ Z)
    (d : A ⟶ W) (e : W ⟶ Z) (h : a ≫ b ≫ c = d ≫ e) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e := by
  calc
    _ = F.map (a ≫ b ≫ c) := by rw [F.map_comp, F.map_comp]
    _ = F.map (d ≫ e) := congrArg F.map h
    _ = _ := F.map_comp d e

/-- Cancel the same supplied inverse at the end of the original coefficient arrow. -/
theorem suffix_cancel
    {D : Type*} [Category* D] {A B C E : D}
    (a : A ⟶ B) (b : B ⟶ C) (i : C ⟶ E) (e : E ⟶ C)
    (hi : i ≫ e = 𝟙 C) : (a ≫ b ≫ i) ≫ e = a ≫ b := by
  simp only [Category.assoc, hi, Category.comp_id]

/-- The actual sheaf coefficient arrow follows from its original comparison,
normalization and naturality equations. No extra coefficient representative
or group-reflection equation is introduced. -/
theorem coefficient_square
    {D : Type*} [Category* D]
    {S T A B Q C K R M E SC TC RC : D}
    {δ : A ⟶ R} {whole : B ⟶ R}
    (s : S ⟶ T) (p : T ⟶ A) (y : R ⟶ E)
    {b : A ⟶ B} {u : S ⟶ Q} {v : Q ⟶ C}
    {t : C ⟶ B} {ti : B ⟶ C} {r : C ⟶ R}
    {x : A ⟶ M} {cp : M ⟶ E}
    {iL : S ⟶ SC} {sC : SC ⟶ TC} {iT : T ⟶ TC}
    {cf : TC ⟶ M} {cg : SC ⟶ RC} {cq : RC ⟶ E}
    {k : Q ⟶ K} {ρ : K ⟶ RC} {bq : K ⟶ R}
    (hR : s ≫ p ≫ b = u ≫ v ≫ t)
    (hN : iL ≫ sC = s ≫ iT)
    (hC : sC ≫ cf ≫ cp = cg ≫ cq)
    (h0 : p ≫ x = iT ≫ cf)
    (hg : u ≫ k ≫ ρ = iL ≫ cg)
    (hq : bq ≫ y = ρ ≫ cq)
    (hn : k ≫ bq = v ≫ r)
    (hi : t ≫ ti = 𝟙 C)
    (hδ : δ ≫ y = x ≫ cp)
    (hwhole : whole = ti ≫ r)
    (hs : Epi s) (hp : Epi p) (hy : Mono y) : δ = b ≫ whole := by
  let : Epi s := hs
  let : Epi p := hp
  let : Mono y := hy
  rw [hwhole]
  apply (cancel_mono y).mp
  apply (cancel_epi p).mp
  apply (cancel_epi s).mp
  simp only [Category.assoc]
  have hi' : t ≫ ti ≫ r ≫ y = r ≫ y := by
    rw [← Category.assoc t ti, hi, Category.id_comp]
  calc
    s ≫ p ≫ δ ≫ y = s ≫ p ≫ x ≫ cp := by rw [hδ]
    _ = s ≫ iT ≫ cf ≫ cp := by
      have h0' := congrArg (fun z => s ≫ z ≫ cp) h0
      simpa only [Category.assoc] using h0'
    _ = iL ≫ sC ≫ cf ≫ cp := by
      have hN' := congrArg (fun z => z ≫ cf ≫ cp) hN.symm
      simpa only [Category.assoc] using hN'
    _ = iL ≫ cg ≫ cq := by rw [hC]
    _ = u ≫ k ≫ ρ ≫ cq := by
      have hg' := congrArg (fun z => z ≫ cq) hg.symm
      simpa only [Category.assoc] using hg'
    _ = u ≫ k ≫ bq ≫ y := by rw [hq]
    _ = u ≫ v ≫ r ≫ y := by
      have hn' := congrArg (fun z => u ≫ z ≫ y) hn
      simpa only [Category.assoc] using hn'
    _ = s ≫ p ≫ b ≫ ti ≫ r ≫ y := by
      have hR' := congrArg (fun z => z ≫ ti ≫ r ≫ y) hR
      simpa only [Category.assoc, hi'] using hR'.symm

/-- Transport the original canonical component using its actual coefficient
and naturality equations, without restating a concrete intermediate type. -/
theorem canonical_transport
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) {A B R S : D} {U V W Z : C}
    (e : R ≅ S) (u : A ⟶ B)
    {γ₀ : A ⟶ F.obj U} {γ₁ : B ⟶ F.obj V}
    {a : U ⟶ V} {b : V ⟶ W} {i : W ⟶ Z} {k : U ⟶ Z}
    {m : F.obj Z ⟶ R} {s : F.obj W ⟶ S} {κ : B ⟶ S} {c : A ⟶ R}
    (hn : u ≫ γ₁ = γ₀ ≫ F.map a)
    (hk : a ≫ b ≫ i = k)
    (hs : s = F.map i ≫ m ≫ e.hom)
    (hκ : κ = γ₁ ≫ F.map b ≫ s)
    (hc : c = γ₀ ≫ F.map k ≫ m) : u ≫ κ ≫ e.inv = c := by
  rw [hκ, hs]
  calc
    _ = (u ≫ γ₁) ≫ F.map b ≫ F.map i ≫ m := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = γ₀ ≫ F.map a ≫ F.map b ≫ F.map i ≫ m := by
      rw [hn]
      simp only [Category.assoc]
    _ = γ₀ ≫ F.map (a ≫ b ≫ i) ≫ m := by
      simp only [Functor.map_comp, Category.assoc]
    _ = c := by rw [hk, ← hc]

/-- Use the SAME supplied adjunction and its original unit to identify the
original arrows from their actual transported comparison equation. -/
theorem eq_of_original_unit_transport
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {X Y : C} {A B : D} (e : X ≅ Y) (e' : A ≅ B)
    {δ κ : L.obj Y ⟶ B}
    (h : L.map e.hom ≫ δ ≫ e'.inv = L.map e.hom ≫ κ ≫ e'.inv) : δ = κ := by
  apply (adj.homEquiv Y B).injective
  simp only [Adjunction.homEquiv_unit]
  apply (cancel_epi e.hom).mp
  apply (cancel_mono (R.map e'.inv)).mp
  have hη := adj.unit.naturality e.hom
  change e.hom ≫ adj.unit.app Y = adj.unit.app X ≫ R.map (L.map e.hom) at hη
  have hu := congrArg (fun k => adj.unit.app X ≫ R.map k) h
  simp only [Functor.map_comp, ← Category.assoc, ← hη] at hu ⊢
  exact hu

/-- The SAME three original comparison factors, shared before specialization. -/
def coefficientIso
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (L : C ⥤ D) {M N : C} {P Q : D}
    (b : L.obj M ≅ P) (e : M ≅ N) (c : L.obj N ≅ Q) : P ≅ Q :=
  b.symm ≪≫ L.mapIso e ≪≫ c

theorem coefficientIso_hom
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (L : C ⥤ D) {M N : C} {P Q : D}
    (b : L.obj M ≅ P) (e : M ≅ N) (c : L.obj N ≅ Q) :
    (coefficientIso L b e c).hom = b.inv ≫ L.map e.hom ≫ c.hom := by
  simp only [coefficientIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]

theorem coefficientIso_normalization
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (L : C ⥤ D) {M N : C} {P Q : D}
    (b : L.obj M ≅ P) (e : M ≅ N) (c : L.obj N ≅ Q) :
    b.hom ≫ (coefficientIso L b e c).hom = L.map e.hom ≫ c.hom := by
  rw [coefficientIso_hom]
  exact b.hom_inv_id_assoc _

/-- Replace only the original first comparison in an already supplied equation. -/
theorem trans_comp
    {D : Type*} [Category* D] {A B C : D}
    {f : A ⟶ C} {a a' : A ⟶ B} {b : B ⟶ C}
    (h : f = a ≫ b) (ha : a = a') : f = a' ≫ b :=
  h.trans (congrArg (fun k => k ≫ b) ha)

end CategoryTheory.Over.RelativeTests.Comparison

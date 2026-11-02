/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.SectionZeroOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem
public import Aglib.AlgebraicGeometry.Descent.Opens

/-! # Original relative sections and open descent

The relative section functor is the existing `pullbackSectionsFunctor`.
Its actual zero open commutes with every relative restriction. Surjective
restrictions therefore detect equality. A matching section gives saturated
comparison opens, which descend through the original open image. The final
section amalgamation uses these opens; no section-descent assumption is built
into a replacement sheaf model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe v

/-- The complete difference comparison is proved before specializing the
original relative-section construction. Its maps are all the given functor's
maps, and both composition equations are retained. -/
private theorem presheaf_difference_matching
    {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Ab.{v})
    {R Q T U : C} (r₁ r₂ : R ⟶ Q) (a : Q ⟶ T) (b : Q ⟶ U)
    (s : P.obj (op T)) (t : P.obj (op U))
    (hs : P.map (r₁ ≫ a).op s = P.map (r₂ ≫ a).op s)
    (hb : r₁ ≫ b = r₂ ≫ b) :
    P.map r₁.op (P.map a.op s - P.map b.op t) =
      P.map r₂.op (P.map a.op s - P.map b.op t) := by
  have ha : P.map r₁.op (P.map a.op s) = P.map r₂.op (P.map a.op s) :=
    (ConcreteCategory.congr_hom (P.map_comp a.op r₁.op) s).symm.trans
      (hs.trans (ConcreteCategory.congr_hom (P.map_comp a.op r₂.op) s))
  have hc : P.map r₁.op (P.map b.op t) = P.map r₂.op (P.map b.op t) :=
    (ConcreteCategory.congr_hom (P.map_comp b.op r₁.op) t).symm.trans
      ((congrArg (fun f : R ⟶ U => P.map f.op t) hb).trans
        (ConcreteCategory.congr_hom (P.map_comp b.op r₂.op) t))
  exact (map_sub (P.map r₁.op).hom _ _).trans
    ((congrArg₂ (fun x y : P.obj (op R) => x - y) ha hc).trans
      (map_sub (P.map r₂.op).hom _ _).symm)

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

open Continuity
attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)

/-- The zero open of the original relative section, at its original scheme. -/
def relativeSectionZeroOpen (Y : Over X)
    (s : (pullbackSectionsFunctor F).obj (op Y)) : Y.left.Opens :=
  sectionZeroOpen ((inverseImage Y.hom).obj F) s

/-- The original relative zero open is the whole scheme exactly for the zero section. -/
theorem relativeSectionZeroOpen_top_iff
    (F : AbelianSheaf.{u, u + 1} X) (R : Over X)
    (s : (pullbackSectionsFunctor F).obj (op R)) :
    relativeSectionZeroOpen F R s = ⊤ ↔ s = 0 :=
  sectionZeroOpen_eq_top_iff ((inverseImage R.hom).obj F) s

/-- Relative section restriction has the literal inverse-image zero open. -/
theorem relativeSectionZeroOpen_map {Y Z : Over X} (a : Y ⟶ Z)
    (s : (pullbackSectionsFunctor F).obj (op Z)) :
    relativeSectionZeroOpen F Y ((pullbackSectionsFunctor F).map a.op s) =
      a.left ⁻¹ᵁ relativeSectionZeroOpen F Z s := by
  let e : (inverseImage a.left).obj ((inverseImage Z.hom).obj F) ≅
      (inverseImage Y.hom).obj F :=
    ((pullbackTriangleIso Y.hom Z.hom a.left (Over.w a)).app F).symm
  change sectionZeroOpen ((inverseImage Y.hom).obj F)
      ((globalSections Y.left).map e.hom
        (globalSectionsPullback a.left ((inverseImage Z.hom).obj F) s)) = _
  exact (sectionZeroOpen_mapIso e
    (globalSectionsPullback a.left ((inverseImage Z.hom).obj F) s)).trans
      (sectionZeroOpen_globalSectionsPullback a.left ((inverseImage Z.hom).obj F) s)

/-- Surjective original relative pullback detects sections, without any
flatness, finite-coefficient or representability condition. -/
theorem pullbackSectionsMap_injective_of_surjective {Y Z : Over X} (a : Y ⟶ Z)
    [Surjective a.left] : Function.Injective ((pullbackSectionsFunctor F).map a.op) := by
  intro s t h
  apply sub_eq_zero.mp
  have hz : (pullbackSectionsFunctor F).map a.op (s - t) = 0 := by
    rw [map_sub, h, sub_self]
  have htop : relativeSectionZeroOpen F Y
      ((pullbackSectionsFunctor F).map a.op (s - t)) = ⊤ :=
    (sectionZeroOpen_eq_top_iff _ _).mpr hz
  rw [relativeSectionZeroOpen_map] at htop
  apply (sectionZeroOpen_eq_top_iff _ _).mp
  ext z
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨y, rfl⟩ := a.left.surjective z
    have hy : y ∈ a.left ⁻¹ᵁ relativeSectionZeroOpen F Z (s - t) := by
      rw [htop]; trivial
    exact hy

/-- Matching is expressed on the existing section functor and all original
relative arrows. It is a property of a section, not a new coefficient model. -/
def IsMatchingRelativeSection (Y : Over X)
    (s : (pullbackSectionsFunctor F).obj (op Y)) : Prop :=
  ∀ (Z : Over X) (a b : Z ⟶ Y),
    (pullbackSectionsFunctor F).map a.op s = (pullbackSectionsFunctor F).map b.op s

/-- A matching original section gives equal comparison-zero opens on the two
sides of the actual kernel pair of any relative map. -/
theorem comparisonZeroOpen_matching {T U Q : Over X}
    (a : Q ⟶ T) (b : Q ⟶ U)
    (s : (pullbackSectionsFunctor F).obj (op T))
    (hs : IsMatchingRelativeSection F T s)
    (t : (pullbackSectionsFunctor F).obj (op U)) :
    pullback.fst b.left b.left ⁻¹ᵁ
        relativeSectionZeroOpen F Q
          ((pullbackSectionsFunctor F).map a.op s - (pullbackSectionsFunctor F).map b.op t) =
      pullback.snd b.left b.left ⁻¹ᵁ
        relativeSectionZeroOpen F Q
          ((pullbackSectionsFunctor F).map a.op s - (pullbackSectionsFunctor F).map b.op t) := by
  let R : Over X := Over.mk (pullback.fst b.left b.left ≫ Q.hom)
  let r₁ : R ⟶ Q := Over.homMk (pullback.fst b.left b.left)
  have h₂ : pullback.snd b.left b.left ≫ Q.hom =
      pullback.fst b.left b.left ≫ Q.hom := by
    rw [← Over.w b]
    simp only [← Category.assoc]
    rw [pullback.condition]
  let r₂ : R ⟶ Q := Over.homMk (pullback.snd b.left b.left) h₂
  have hb : r₁ ≫ b = r₂ ≫ b := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have hm := hs R (r₁ ≫ a) (r₂ ≫ a)
  have he := presheaf_difference_matching (pullbackSectionsFunctor F) r₁ r₂ a b s t hm hb
  have hz := congrArg (relativeSectionZeroOpen F R) he
  exact (relativeSectionZeroOpen_map F r₁ _).symm.trans
    (hz.trans (relativeSectionZeroOpen_map F r₂ _))

/-- The comparison open descends to the original open image, with its exact
inverse-image equation. This supplies the geometric open in section descent. -/
theorem existsUnique_comparisonOpen {T U Q : Over X}
    (a : Q ⟶ T) (b : Q ⟶ U) (hb : IsOpenMap b.left) [Surjective b.left]
    (s : (pullbackSectionsFunctor F).obj (op T))
    (hs : IsMatchingRelativeSection F T s)
    (t : (pullbackSectionsFunctor F).obj (op U)) :
    ∃! V : U.left.Opens, b.left ⁻¹ᵁ V =
      relativeSectionZeroOpen F Q
        ((pullbackSectionsFunctor F).map a.op s - (pullbackSectionsFunctor F).map b.op t) := by
  let W := relativeSectionZeroOpen F Q
    ((pullbackSectionsFunctor F).map a.op s - (pullbackSectionsFunctor F).map b.op t)
  have hw := comparisonZeroOpen_matching F a b s hs t
  obtain ⟨V, hV, huniq⟩ := Scheme.existsUnique_preimage_eq_of_isOpenMap
    (fun _ : PUnit.{1} => b.left) (fun _ => hb)
    (fun x => ⟨PUnit.unit, b.left.surjective x⟩) (fun _ => W) (fun _ _ => hw)
  exact ⟨V, hV PUnit.unit, fun V' h => huniq V' fun _ => h⟩

end AlgebraicGeometry.Scheme.EtaleCohomology

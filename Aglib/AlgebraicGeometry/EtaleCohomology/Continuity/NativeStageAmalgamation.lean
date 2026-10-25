/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.CanonicalStageAmalgamation

/-! # Gluing finite representatives in the original relative stage sheaf

Structural-arrow normalization is performed on the local chart tests and their
compatibility, before gluing. The resulting section belongs to the original
relative stage object, rather than to a subsequently transported raw model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u v

open EtaleAffineBasis
attribute [local instance] hasSheafifyLarge

/-- Equality of structural arrows transports the whole compatible unit family.
No global section or existential of global sections is transported here. -/
theorem unitSections_compatible_of_structural_eq {X S : Scheme.{u}}
    (f g : S ⟶ X) (h : f = g) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → S.Etale) (U : J → X.Etale)
    (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ f)
    (t : ∀ j, F.obj.obj (op (U j)))
    (hcomp : Presieve.Arrows.Compatible
      (((inverseImage f).obj F).obj ⋙ CategoryTheory.forget Ab.{u + 1})
      (fun j ↦ (etaleTerminalIsTerminal S).from (W j))
      (fun j ↦ unitSectionMap f F (relativeChartTest f (W j) (U j) (a j) (ha j))
        (t j))) :
    Presieve.Arrows.Compatible
      (((inverseImage g).obj F).obj ⋙ CategoryTheory.forget Ab.{u + 1})
      (fun j ↦ (etaleTerminalIsTerminal S).from (W j))
      (fun j ↦ unitSectionMap g F
        (relativeChartTest g (W j) (U j) (a j)
          ((ha j).trans (congrArg (fun z ↦ (W j).hom ≫ z) h))) (t j)) := by
  cases h
  exact hcomp

/-- The original unit test of a base-changed representative, already over the
literal original relative object. -/
def nativeBaseChangeChartTest {X S : Scheme.{u}} (B : Over X)
    (τ : B.left ⟶ S) (r : S ⟶ X) (h : τ ≫ r = B.hom)
    (W : Over S) [Etale W.hom] (U : X.Etale)
    (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r) :
    baseChangeEtaleChart τ W ⟶ (siteBaseChange B.hom).obj U :=
  relativeChartTest B.hom (baseChangeEtaleChart τ W) U (pullback.snd τ W.hom ≫ a)
    ((baseChangeChart_triangle τ r W U a ha).trans
      (congrArg (fun z ↦ (baseChangeEtaleChart τ W).hom ≫ z) h))

/-- Actual overlap matching supplies compatibility in the original relative
stage sheaf, after geometric normalization of the local family. -/
theorem nativeBaseChange_unitSections_compatible {X S : Scheme.{u}}
    (B : Over X) (τ : B.left ⟶ S) (r : S ⟶ X) (h : τ ≫ r = B.hom)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} (W : J → Over S)
    [∀ j, Etale (W j).hom] (U : J → X.Etale)
    (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (hmatch : BaseChangeOverlapMatching τ r F W U a ha t) :
    Presieve.Arrows.Compatible
      (((inverseImage B.hom).obj F).obj ⋙ CategoryTheory.forget Ab.{u + 1})
      (fun j ↦ (etaleTerminalIsTerminal B.left).from (baseChangeEtaleChart τ (W j)))
      (fun j ↦ unitSectionMap B.hom F
        (nativeBaseChangeChartTest B τ r h (W j) (U j) (a j) (ha j)) (t j)) := by
  exact unitSections_compatible_of_structural_eq (τ ≫ r) B.hom h F
    (fun j ↦ baseChangeEtaleChart τ (W j)) U
    (fun j ↦ pullback.snd τ (W j).hom ≫ a j)
    (fun j ↦ baseChangeChart_triangle τ r (W j) (U j) (a j) (ha j)) t
    (baseChange_unitSections_compatible τ r F W U a ha t hmatch)

/-- Original unit sections glue directly to a section at the given relative
object. The relative object is normalized before applying sheaf gluing. -/
theorem exists_native_unitSections_amalgamation {X : Scheme.{u}}
    (B : Over X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → B.left.Etale) (U : J → X.Etale)
    (a : ∀ j, W j ⟶ (siteBaseChange B.hom).obj (U j))
    (t : ∀ j, F.obj.obj (op (U j)))
    (hcover : Sieve.ofArrows W (fun j ↦ (etaleTerminalIsTerminal B.left).from (W j)) ∈
      B.left.smallEtaleTopology (etaleTerminal B.left))
    (hcompatible : Presieve.Arrows.Compatible
      (((inverseImage B.hom).obj F).obj ⋙ CategoryTheory.forget Ab.{u + 1})
      (fun j ↦ (etaleTerminalIsTerminal B.left).from (W j))
      (fun j ↦ unitSectionMap B.hom F (a j) (t j))) :
    ∃ s : (pullbackSectionsFunctor F).obj (op B), ∀ j,
      (pullbackSectionsFunctor F).map
        (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ B.hom)) (V := B)).op s =
      etaleRepresentativeSection F (Over.mk ((W j).hom ≫ B.hom)) (U j)
        (unitRepresentativeArrow B.hom (a j)) (t j) := by
  rcases B with ⟨S, ⟨⟨⟩⟩, f⟩
  exact exists_canonical_unitSections_amalgamation f F W U a t hcover hcompatible

/-- The local equations of an original native unit amalgamation. The predicate
is defined before any inverse-system or chosen-stage specialization. -/
def IsNativeUnitAmalgamation {X : Scheme.{u}}
    (B : Over X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → B.left.Etale) (U : J → X.Etale)
    (a : ∀ j, W j ⟶ (siteBaseChange B.hom).obj (U j))
    (t : ∀ j, F.obj.obj (op (U j)))
    (s : (pullbackSectionsFunctor F).obj (op B)) : Prop :=
  ∀ j, (pullbackSectionsFunctor F).map
      (Over.homMk (W j).hom (U := Over.mk ((W j).hom ≫ B.hom)) (V := B)).op s =
    etaleRepresentativeSection F (Over.mk ((W j).hom ≫ B.hom)) (U j)
      (unitRepresentativeArrow B.hom (a j)) (t j)

/-- Actual matching of base-changed local representatives yields an original
native section, with its local equations fixed before indexed specialization. -/
theorem exists_native_baseChange_unitSections_amalgamation {X S : Scheme.{u}}
    (B : Over X) (τ : B.left ⟶ S) (r : S ⟶ X) (h : τ ≫ r = B.hom)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} (W : J → Over S)
    [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (hmatch : BaseChangeOverlapMatching τ r F W U a ha t) :
    ∃ s : (pullbackSectionsFunctor F).obj (op B),
      IsNativeUnitAmalgamation B F (fun j ↦ baseChangeEtaleChart τ (W j)) U
        (fun j ↦ nativeBaseChangeChartTest B τ r h (W j) (U j) (a j) (ha j)) t s := by
  exact exists_native_unitSections_amalgamation B F
    (fun j ↦ baseChangeEtaleChart τ (W j)) U
    (fun j ↦ nativeBaseChangeChartTest B τ r h (W j) (U j) (a j) (ha j)) t
    (baseChangeEtaleChart_covering τ W hcover)
    (nativeBaseChange_unitSections_compatible B τ r h F W U a ha t hmatch)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

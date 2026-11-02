/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenRestriction

/-! Interface examples and approved-foundation guards for the shared provider. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
variable {D U X : Scheme.{u}}

/-- Restriction of a factored morphism uses the actual ideal comparison map. -/
example (p : D ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.Hom.idealModulePullbackFactor p j).hom =
      Scheme.Hom.idealPullbackMap (p ≫ j) p j (𝟙 D) (Category.id_comp _) :=
  Scheme.Hom.idealModulePullbackFactor_hom p j

/-- Disjointness is sufficient; neither morphism is assumed to be a closed immersion. -/
example (i : D ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (h : Disjoint (Set.range i) (Set.range j)) :
    Nonempty ((Scheme.Modules.pullback j).obj (Scheme.Hom.idealModule i) ≅
      SheafOfModules.unit U.ringCatSheaf) :=
  ⟨Scheme.Hom.idealModulePullbackIsoOfDisjoint i j h⟩

/-- info: 'AlgebraicGeometry.Scheme.Hom.idealModulePullbackFactor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.idealModulePullbackFactor

/-- info: 'AlgebraicGeometry.Scheme.Hom.idealModulePullbackFactor_hom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.idealModulePullbackFactor_hom

/-- info: 'AlgebraicGeometry.Scheme.Hom.idealModuleEmptyIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.idealModuleEmptyIso

/-- info: 'AlgebraicGeometry.Scheme.Hom.idealModuleEmptyIso_hom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.idealModuleEmptyIso_hom

/-- info: 'AlgebraicGeometry.Scheme.Hom.isEmpty_pullback_of_disjoint_ranges' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isEmpty_pullback_of_disjoint_ranges

/-- info: 'AlgebraicGeometry.Scheme.Hom.idealModulePullbackIsoOfDisjoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.idealModulePullbackIsoOfDisjoint

/-- info: 'AlgebraicGeometry.Scheme.Hom.idealModulePullbackIsoOfDisjoint_hom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.idealModulePullbackIsoOfDisjoint_hom

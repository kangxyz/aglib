/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CoefficientExactness

/-! Native counit and original-map interfaces with independent Ext worlds. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w w'

attribute [local instance] hasSheafifyLarge hasSheafifyModules

local instance moduleSheaf_hasFiniteBiproducts (U : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] : HasFiniteBiproducts (ModuleSheaf U Λ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {V U : Scheme.{u}} (f : V ⟶ U) [Etale f] [Surjective f]
  (Λ : Type (u + 1)) [CommRing Λ]

/-- Surjective étale inverse image retains its actual native ringed functor. -/
example : (moduleInverseImage f Λ).Faithful :=
  moduleInverseImage_faithful_of_surjective f Λ

/-- No finite-pushforward comparison is required for the actual counit epimorphism. -/
example (M : ModuleSheaf U Λ) : Epi ((moduleLowerShriekAdjunction f Λ).counit.app M) :=
  moduleLowerShriek_counit_epi_of_surjective f Λ M

variable [HasExt.{w} (ModuleSheaf V Λ)] [HasExt.{w'} (ModuleSheaf U Λ)]

/-- The entire counit square is tested on the literal original Ext maps. -/
example (M N : ModuleSheaf U Λ) (q : ℕ) :
    (moduleLowerShriekExtEquiv f Λ ((moduleInverseImage f Λ).obj M) N q).toAddMonoidHom.comp
        ((Ext.mk₀ ((moduleLowerShriekAdjunction f Λ).counit.app M)).precomp N
          (zero_add q)) =
      (moduleInverseImage f Λ).mapExtAddHom M N q :=
  moduleLowerShriekExtEquiv_counit_precomp f Λ M N q

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriek_counit_epi_of_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriek_counit_epi_of_surjective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExtEquiv_counit_precomp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleLowerShriekExtEquiv_counit_precomp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_extClass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityTransposeMap_extClass

/-- The empty finite biproduct is included in the same original constant-free comparison. -/
example : (⨁ fun _ : Fin 0 => moduleUnit U Λ) ≅
    (moduleSheafEquivalence U Λ).functor.obj
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin 0 → Λ))) :=
  moduleFiniteFreeConstantIso U Λ 0

/-- The original normalized unit counit remains epi at the zero-ring level. -/
example : Epi (moduleUnitLowerShriekCounit f 1) :=
  moduleUnitLowerShriekCounit_epi f 1

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitLowerShriekCounit_ext_square' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitLowerShriekCounit_ext_square

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_unit_biproduct_lowerShriek_epi' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.exists_galois_unit_biproduct_lowerShriek_epi

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_biproduct_two_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_unit_biproduct_two_isPerfPair

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_constantFree_two_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleDualityMap_constantFree_two_isPerfPair

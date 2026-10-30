/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.LowerShriekUnderlying

/-! Public original-map interfaces and approved-axiom guards. -/

@[expose] public section

open CategoryTheory

universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {L L' : C ⥤ D} {R R' : D ⥤ C}

/-- The generic counit uses the selected right comparison, without equating Hom universes. -/
example (a : L ⊣ R) (b : L' ⊣ R') (d : R ≅ R') :
    Functor.whiskerLeft R' ((a.ofNatIsoRight d).leftAdjointUniq b).hom ≫ b.counit =
      (a.ofNatIsoRight d).counit :=
  Adjunction.leftAdjointUniq_hom_counit (a.ofNatIsoRight d) b

/-- info: 'CategoryTheory.Adjunction.underlying_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.underlying_counit

/-- info: 'CategoryTheory.Adjunction.underlying_counit_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.underlying_counit_app

/-- info: 'CategoryTheory.mateEquiv_equivalence_comparison' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.mateEquiv_equivalence_comparison

/-- info: 'CategoryTheory.Adjunction.comparison_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.comparison_counit

/-- info: 'CategoryTheory.Adjunction.comparison_counit_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.comparison_counit_app

/-- info: 'CategoryTheory.Adjunction.underlying_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.underlying_unit

/-- info: 'CategoryTheory.Adjunction.underlying_unit_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.underlying_unit_app

/-- info: 'CategoryTheory.mateEquiv_ofNatIsoRight_comparison' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.mateEquiv_ofNatIsoRight_comparison

/-- info: 'CategoryTheory.mateEquiv_composite_comparison' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.mateEquiv_composite_comparison

/-- info: 'CategoryTheory.Adjunction.underlying_leftAdjointUniq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.underlying_leftAdjointUniq

/-- info: 'CategoryTheory.Functor.underlying_comp_iso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.underlying_comp_iso

/-- info: 'CategoryTheory.Functor.underlying_comp_hom_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.underlying_comp_hom_app

/-- info: 'CategoryTheory.Adjunction.coefficient_counit_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.coefficient_counit_comp

/-- info: 'CategoryTheory.Adjunction.coefficient_counit_extension' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.coefficient_counit_extension

/-- info: 'CategoryTheory.Iso.inv_comp_of_hom_eq_comp' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Iso.inv_comp_of_hom_eq_comp

/-- info: 'CategoryTheory.Adjunction.underlying_coefficient_counit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Adjunction.underlying_coefficient_counit

/-- info: 'CategoryTheory.Functor.underlyingLowerShriek_inv_app' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.underlyingLowerShriek_inv_app

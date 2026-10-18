/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Descent.Modules.Fppf.LineBundleStack

/-! Focused consumer of the fpqc and fppf stacks of quasi-coherent sheaves and line bundles: the
fpqc prestack instance, the property-level fpqc locality, the affine faithfully flat descent of
local rank one, and the stack instances, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

example : quasicoherentPseudofunctor.{u}.IsPrestack Scheme.fppfTopology := inferInstance

example : quasicoherentPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology := inferInstance

example : quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology := inferInstance

example : quasicoherentPseudofunctor.{u}.IsStack Scheme.fppfTopology := inferInstance

example : lineBundlePseudofunctor.{u}.IsStack Scheme.fppfTopology := inferInstance

example {S : Scheme.{u}} (R : Sieve S) (hR : R ∈ Scheme.fppfTopology S) (M : S.Modules)
    [M.IsQuasicoherent] (hM : ∀ ⦃Y : Scheme.{u}⦄ (g : Y ⟶ S), R g →
      Invertible.IsLocallyRankOne Y ((pullback g).obj M)) :
    Invertible.IsLocallyRankOne S M :=
  isLocallyRankOne_of_mem_fppfTopology R hR M hM

/--
info: 'AlgebraicGeometry.Scheme.isPrestack_fpqcTopology_of_isPrestackFor_specMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isPrestack_fpqcTopology_of_isPrestackFor_specMap

/--
info: 'AlgebraicGeometry.Scheme.Modules.isPrestack_quasicoherentPseudofunctor_fpqcTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isPrestack_quasicoherentPseudofunctor_fpqcTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isPrestack_quasicoherentPseudofunctor_fppfTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isPrestack_quasicoherentPseudofunctor_fppfTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStackFor_ofArrows_of_finite_of_isAffine_of_flat_of_union_range_eq_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isStackFor_ofArrows_of_finite_of_isAffine_of_flat_of_union_range_eq_univ

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStackFor_of_mem_fpqcPrecoverage_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isStackFor_of_mem_fpqcPrecoverage_spec

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStackFor_of_mem_fpqcPrecoverage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isStackFor_of_mem_fpqcPrecoverage

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_quasicoherentPseudofunctor_fpqcTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isStack_quasicoherentPseudofunctor_fpqcTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_quasicoherentPseudofunctor_fppfTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isStack_quasicoherentPseudofunctor_fppfTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.prop_of_mem_fpqcPrecoverage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.prop_of_mem_fpqcPrecoverage

/--
info: 'AlgebraicGeometry.Scheme.Modules.prop_of_mem_fppfTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.prop_of_mem_fppfTopology

/--
info: 'AlgebraicGeometry.Scheme.Modules.isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isLocallyRankOne_of_pullback_specMap_of_faithfullyFlat

/--
info: 'AlgebraicGeometry.Scheme.Modules.isLocallyRankOne_of_mem_fppfTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isLocallyRankOne_of_mem_fppfTopology

/--
info: 'CategoryTheory.Pseudofunctor.ObjectProperty.isStack_fullsubcategory_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.ObjectProperty.isStack_fullsubcategory_of_le

/--
info: 'AlgebraicGeometry.Scheme.Modules.isStack_lineBundlePseudofunctor_fppfTopology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isStack_lineBundlePseudofunctor_fppfTopology


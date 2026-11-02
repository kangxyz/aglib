/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.EtaleTraceNormalization

/-! Whole original normalization interfaces and approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

universe u
variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
  (d : ℕ) (hd : ∀ x : X, Y.obj.hom.finrank x = d)

/-- Rank zero is permitted by the sheaf construction; positivity is needed only later. -/
example (hzero : ∀ x : X, Y.obj.hom.finrank x = 0) :
    (inverseImageAdjunction Y.obj.hom).unit ≫ finiteEtaleSheafTrace Y 0 hzero =
      0 • 𝟙 _ := finiteEtaleSheafTrace_rank Y 0 hzero

/-- The whole rank equation uses the original inverse-image unit. -/
example : (inverseImageAdjunction Y.obj.hom).unit ≫ finiteEtaleSheafTrace Y d hd = d • 𝟙 _ :=
  finiteEtaleSheafTrace_rank Y d hd

/-- info: 'AlgebraicGeometry.Scheme.FiniteEtale.exists_freeRepresentable_transfer_local'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.FiniteEtale.exists_freeRepresentable_transfer_local

/-- info: 'AlgebraicGeometry.Scheme.FiniteEtale.freeRepresentable_transfer_ext' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.FiniteEtale.freeRepresentable_transfer_ext

/-- info: 'AlgebraicGeometry.Scheme.FiniteEtale.finiteEtaleFreeTransfer_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.FiniteEtale.finiteEtaleFreeTransfer_eq

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.etaleRepresentedRestrictionTrace_eq_generic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.etaleRepresentedRestrictionTrace_eq_generic

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleSheafTrace_local' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleSheafTrace_local

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleSheafTrace_rank' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteEtaleSheafTrace_rank

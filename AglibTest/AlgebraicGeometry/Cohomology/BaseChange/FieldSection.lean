/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.FieldSection

/-! Focused consumer of the sections of a field base change: a `K`-point gives a section of
`X_K ⟶ Spec K`, and every point `x` does so for `K = κ(x)`; axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Scheme
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology

universe u

variable {k : Type u} [Field k] (X : FScheme k)

/-- `Spec κ(x) ⟶ X ⟶ Spec k` is `Spec` of the residue algebra map. -/
example (Y : Scheme.{u}) (p : Y ⟶ Spec (.of k)) (y : Y) :
    letI := residueAlgebra Y p y
    Y.fromSpecResidueField y ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap k (Y.residueField y))) :=
  fromSpecResidueField_comp_eq_spec_map_algebraMap Y p y

/-- A `K`-point of `X` over `k` gives a section of the base change. -/
example {K : Type u} [Field K] [Algebra k K] (s : Spec (.of K) ⟶ X.left)
    (hs : s ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    IsSplitEpi (fieldBaseChange K X).hom :=
  isSplitEpi_fieldBaseChange_hom X hs

/-- Every point gives a section after base change to its residue field. -/
example (x : X.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), IsSplitEpi (fieldBaseChange K X).hom :=
  exists_isSplitEpi_fieldBaseChange_hom X x

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.exists_isSplitEpi_fieldBaseChange_hom' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_isSplitEpi_fieldBaseChange_hom

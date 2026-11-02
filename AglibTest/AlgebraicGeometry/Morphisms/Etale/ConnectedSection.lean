/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.ConnectedSection

/-! # Original maps of a connected etale scheme with a rational section -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [PreconnectedSpace X]
  (p : X ⟶ Spec (.of k)) [Etale p] (s : Spec (.of k) ⟶ X)
  (hs : s ≫ p = 𝟙 _)

example : p ≫ s = 𝟙 X :=
  Scheme.comp_section_eq_id_of_etale_of_preconnected p s hs

example : (Scheme.isoSpecOfEtaleOfPreconnected p s hs).hom = p ∧
    (Scheme.isoSpecOfEtaleOfPreconnected p s hs).inv = s := ⟨rfl, rfl⟩

/--
info: 'AlgebraicGeometry.Scheme.comp_section_eq_id_of_etale_of_preconnected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.comp_section_eq_id_of_etale_of_preconnected

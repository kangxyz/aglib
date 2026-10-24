/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.UniversallyClosed.ImageComplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Focused consumer of the complement of the image of a closed set under a universally closed
morphism and its base-change universal property (the topological part of Nitsure,
arXiv:math/0504590v1, §6, p. 28, Exercise A), with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

/-- **Fibres of a universally closed morphism contained in an open set form an open, universal
for base change** (the general family version: no flatness or Noetherian hypothesis). -/
example {P X Y Y' W : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [UniversallyClosed f] (h : IsPullback fst snd f g) (i : X ⟶ W) (O : W.Opens) :
    g ⁻¹ᵁ f.complImage (i ⁻¹ᵁ O).compl = ⊤ ↔ (fst ≫ i) ⁻¹ᵁ O = ⊤ :=
  Scheme.preimage_complImage_compl_preimage_eq_top_iff_of_isPullback h i O

/-- The fibre of a universally closed morphism over a point of that open maps into `O`. -/
example {X Y W : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f] (i : X ⟶ W) (O : W.Opens)
    (y : Y) : y ∈ f.complImage (i ⁻¹ᵁ O).compl ↔ ∀ x, f x = y → i x ∈ O :=
  f.mem_complImage_compl_preimage i O y

/-- The same for a proper family, through the universally closed structure morphism. -/
example {P X Y Y' : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsProper f] (h : IsPullback fst snd f g) (C : Closeds X) :
    g ⁻¹ᵁ f.complImage C = ⊤ ↔ fst ⁻¹' C = ∅ :=
  Scheme.preimage_complImage_eq_top_iff_of_isPullback h C

/--
info: 'AlgebraicGeometry.Scheme.preimage_complImage_eq_top_iff_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.preimage_complImage_eq_top_iff_of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.preimage_complImage_compl_preimage_eq_top_iff_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.preimage_complImage_compl_preimage_eq_top_iff_of_isPullback

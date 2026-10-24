/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.Coproduct

/-!
# Finite disjoint unions of quasi-projective schemes over an affine base

The declarations below restate that finite disjoint unions of H-quasi-projective (H-projective)
schemes over `Spec R` are H-quasi-projective (H-projective), in the binary and the finite form, for
an index type in any universe (for example a finite set of polynomials, as for the finite union of
Hilbert schemes `∐_{Φ ∈ F} Hilb^Φ`), for colimit cofans and finite disjoint open decompositions,
that a disjoint union of two projective spaces is H-projective, that empty schemes are
H-projective, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AglibTest.QuasiProjectiveCoproduct

variable {R : CommRingCat.{u}}

/-- Binary disjoint unions. -/
theorem binary {X Y : Scheme.{u}} (f : X ⟶ Spec R) (g : Y ⟶ Spec R) (f' : X ⟶ Spec R)
    (g' : Y ⟶ Spec R) [IsHQuasiProjective f] [IsHQuasiProjective g] [IsHProjective f']
    [IsHProjective g'] :
    IsHQuasiProjective (coprod.desc f g) ∧ IsHProjective (coprod.desc f' g') :=
  ⟨inferInstance, inferInstance⟩

/-- Finite disjoint unions, for an index type in an arbitrary universe. -/
theorem finite {J : Type v} [Finite J] {Y : J → Scheme.{u}} (f f' : ∀ j, Y j ⟶ Spec R)
    [∀ j, IsHQuasiProjective (f j)] [∀ j, IsHProjective (f' j)] :
    IsHQuasiProjective (Sigma.desc f) ∧ IsHProjective (Sigma.desc f') :=
  ⟨inferInstance, inferInstance⟩

/-- The consumer shape of the finite union of Hilbert schemes: the index type is a finite set of
rational polynomials, the schemes live in an arbitrary universe, and the union is H-quasi-projective
and, over a Noetherian ring, Noetherian. -/
theorem finset_index [IsNoetherianRing R] (F : Finset (Polynomial ℚ)) {Y : F → Scheme.{u}}
    (f : ∀ Φ, Y Φ ⟶ Spec R) [∀ Φ, IsHQuasiProjective (f Φ)] :
    IsHQuasiProjective (Sigma.desc f) ∧ IsNoetherian (∐ Y) :=
  ⟨inferInstance, IsHQuasiProjective.isNoetherian (Sigma.desc f)⟩

/-- A disjoint union of two projective spaces is H-projective; empty schemes are H-projective. -/
theorem projectiveSpace (A : Type u) [CommRing A] (ι κ : Type u) [Finite ι] [Finite κ]
    {X : Scheme.{u}} [IsEmpty X] (f : X ⟶ Spec R) :
    IsHProjective (coprod.desc (ProjectiveSpace.toSpec A ι) (ProjectiveSpace.toSpec A κ)) ∧
      IsHProjective f :=
  ⟨inferInstance, inferInstance⟩

/-- A scheme covered by finitely many pairwise disjoint H-quasi-projective (H-projective) opens is
H-quasi-projective (H-projective); likewise for any colimit cofan of a finite family. -/
theorem decomposition {X : Scheme.{u}} {J : Type v} [Finite J] (U : J → X.Opens)
    (hU : ⨆ j, U j = ⊤) (hd : Pairwise (Function.onFun Disjoint U)) (g g' : X ⟶ Spec R)
    (hg : ∀ j, IsHQuasiProjective ((U j).ι ≫ g)) (hg' : ∀ j, IsHProjective ((U j).ι ≫ g'))
    {Y : J → Scheme.{u}} {c : Cofan Y} (hc : IsColimit c) (h : c.pt ⟶ Spec R)
    (hh : ∀ j, IsHQuasiProjective (c.inj j ≫ h)) :
    IsHQuasiProjective g ∧ IsHProjective g' ∧ IsHQuasiProjective h :=
  ⟨IsHQuasiProjective.of_iSup_eq_top_of_pairwise_disjoint U hU hd g hg,
    IsHProjective.of_iSup_eq_top_of_pairwise_disjoint U hU hd g' hg',
    IsHQuasiProjective.of_isColimit hc h hh⟩

/-- info: 'AglibTest.QuasiProjectiveCoproduct.binary' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjectiveCoproduct.binary

/-- info: 'AglibTest.QuasiProjectiveCoproduct.finite' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjectiveCoproduct.finite

/-- info: 'AglibTest.QuasiProjectiveCoproduct.finset_index' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjectiveCoproduct.finset_index

/-- info: 'AglibTest.QuasiProjectiveCoproduct.projectiveSpace' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjectiveCoproduct.projectiveSpace

/-- info: 'AglibTest.QuasiProjectiveCoproduct.decomposition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjectiveCoproduct.decomposition

end AglibTest.QuasiProjectiveCoproduct

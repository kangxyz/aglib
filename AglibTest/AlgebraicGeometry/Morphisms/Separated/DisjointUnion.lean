/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Separated.DisjointUnion

/-!
# Consumer checks for separatedness of a disjoint union of separated opens

An open that is the union of pairwise disjoint opens, each separated over the base, is separated
over the base; separatedness of an open immersion followed by a morphism depends only on the image
(Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 28, disjoint unions).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.SeparatedDisjointUnion

variable {P S : Scheme.{u}} (f : P ⟶ S)

/-- An open covered by pairwise disjoint separated opens is separated. -/
example (U : P.Opens) {κ : Type*} (V : κ → P.Opens) (hV : ⨆ k, V k = U)
    (hsep : ∀ k, IsSeparated ((V k).ι ≫ f)) (hd : Pairwise (Function.onFun Disjoint V)) :
    IsSeparated (U.ι ≫ f) :=
  isSeparated_ι_comp_of_iSup_eq_of_pairwise_disjoint f U V hV hsep hd

/-- An open of a separated scheme, through the cover by itself. -/
example [IsSeparated f] (U : P.Opens) : IsSeparated (U.ι ≫ f) :=
  isSeparated_ι_comp_of_iSup_eq_of_pairwise_disjoint f U (fun _ : PUnit.{1} => U) (by simp)
    (fun _ => inferInstance) fun a b hab => absurd (Subsingleton.elim a b) hab

/-- Two open immersions with the same image. -/
example (U : P.Opens) {V : Scheme.{u}} (j : V ⟶ P) [IsOpenImmersion j]
    (hj : Set.range j = U) [IsSeparated (U.ι ≫ f)] : IsSeparated (j ≫ f) :=
  (isSeparated_comp_iff_of_range_eq U.ι j (by rw [Scheme.Opens.range_ι, hj]) f).mp inferInstance

/-- The image of `U.ι ⁻¹ᵁ V ⟶ U ⟶ P` for `V ≤ U`. -/
example {U V : P.Opens} (h : V ≤ U) : Set.range ((U.ι ⁻¹ᵁ V).ι ≫ U.ι) = V :=
  Scheme.Opens.range_ι_comp_ι_of_le h

/--
info: 'AlgebraicGeometry.isSeparated_ι_comp_of_iSup_eq_of_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isSeparated_ι_comp_of_iSup_eq_of_pairwise_disjoint

/--
info: 'AlgebraicGeometry.isSeparated_comp_iff_of_range_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isSeparated_comp_iff_of_range_eq

/--
info: 'AlgebraicGeometry.Scheme.Opens.range_ι_comp_ι_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Opens.range_ι_comp_ι_of_le

end AglibTest.SeparatedDisjointUnion

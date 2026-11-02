/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.OpenRestriction
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Multiplication

/-!
# Divisibility of the Picard group of an open curve

An open subscheme missing a closed point of a smooth proper geometrically connected curve
over an algebraically closed field has an `n`-divisible Picard group for invertible `n`.
The pure restriction theorem is separate from this use of Jacobian divisibility and its
existing Kummer-finiteness dependency (Milne, Lectures on Étale Cohomology v2.21,
Proposition 14.12, p. 97; Stacks, Tag 03RR).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]

include hX in
/-- **`Pic(U)` is `n`-divisible** for `n` invertible in `k`, when the image of the open immersion
`j` misses a closed point (Milne, *Lectures on Étale Cohomology* v2.21, proof of Prop. 14.12,
p. 97; Stacks, Étale Cohomology, proof of Lemma 69.3, Tag 03RR). -/
theorem exists_nsmul_eq_of_isOpenImmersion (n : ℕ) (hn : IsUnit (n : k))
    (hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j) (c : PicardGroup U) :
    ∃ b : PicardGroup U, n • b = c := by
  obtain ⟨a, ha, rfl⟩ := exists_curveDegree_eq_zero_pullbackClass_eq_of_isOpenImmersion hX j hx c
  obtain ⟨b, -, rfl⟩ := exists_nsmul_eq_of_curveDegree_eq_zero_of_isUnit_of_isAlgClosed hX n hn a ha
  exact ⟨pullbackClass j b, (map_nsmul (PullbackTensor.Local.pullbackHom j) n b).symm⟩

end AlgebraicGeometry.Scheme.OverField.Curve

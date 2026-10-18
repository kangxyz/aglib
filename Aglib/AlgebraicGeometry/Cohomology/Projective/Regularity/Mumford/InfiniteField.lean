/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.Ambient
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.HyperplaneSections
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.GeneralHyperplane

/-!
# Hyperplane sections over an infinite field

Over an infinite field `k`, with finitely many coordinates, a general hyperplane avoids the
finitely many associated points of finitely many coherent modules on `P_k` (Nitsure,
arXiv:math/0504590v1, p. 10). This discharges the premise `HasHyperplaneSections` of Mumford's
bound (`Mumford/Bound.lean`), so Nitsure's Thm 2.3 (p. 11) holds over every infinite field.

* `exists_forall_frameCoefficient_isSMulRegular` (`HilbertPolynomial/GeneralHyperplane.lean`):
  for finitely many coherent modules `Fⱼ`, some `s` makes every frame coefficient `s / Xᵢ` a
  nonzerodivisor on `Γ(Fⱼ, V)`, `V ≤ D₊(Xᵢ)`.
* `hasHyperplaneSectionsUp_of_infinite` and `hasHyperplaneSections_of_infinite`: hyperplane
  sections exist for `[Field k] [Infinite k] [Finite ι]`, through
  `hasHyperplaneSectionsUp_of_isSMulRegular` and `HasHyperplaneSections.of_up`.
* `isProjectiveRegular_mumfordBound_of_infinite`: Mumford's bound over an infinite field for a
  submodule of an ambient module, with no remaining premise. Over every field the free and ideal
  forms are `isProjectiveRegular_mumfordBound_free` and `_ideal` (`Mumford/ArbitraryField.lean`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)

/-- **Hyperplane sections in the raising form exist over an infinite field**: every pair of
coherent modules on `P_k`, for `k` infinite and finitely many coordinates, has a common
monomorphic multiplication by a section of `O(1)`. -/
theorem hasHyperplaneSectionsUp_of_infinite [Infinite k] [Finite ι] :
    HasHyperplaneSectionsUp k ι :=
  hasHyperplaneSectionsUp_of_isSMulRegular fun G Q hG hQ => by
    obtain ⟨s, hs⟩ := exists_forall_frameCoefficient_isSMulRegular k ι ![G, Q]
      (Fin.forall_fin_two.mpr ⟨hG, hQ⟩)
    exact ⟨s, fun i V hV => ⟨hs 0 i V hV, hs 1 i V hV⟩⟩

/-- **Hyperplane sections exist over an infinite field** (Nitsure, arXiv:math/0504590v1,
p. 10): for an infinite field `k` and finitely many coordinates, every pair of coherent modules
on `P_k` has a common nonzerodivisor `μ : O(-1) ⊗ - ⟶ 𝟭`, multiplication by a linear form. -/
theorem hasHyperplaneSections_of_infinite [Infinite k] [Finite ι] :
    HasHyperplaneSections k ι :=
  HasHyperplaneSections.of_up (hasHyperplaneSectionsUp_of_infinite k ι)

variable {k ι}

/-- **Mumford's bound over an infinite field** for a submodule of an ambient module
(Nitsure, arXiv:math/0504590v1, proof of Thm 2.3, pp. 12-13), with the hyperplane sections of
`hasHyperplaneSections_of_infinite`. -/
theorem isProjectiveRegular_mumfordBound_of_infinite [Infinite k] (n p : ℕ)
    (e : ι ≃ Fin (n + 1)) {F G : (ProjectiveSpace k ι).Modules} (j : F ⟶ G) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (hG : IsMumfordAmbient n p G)
    (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  isProjectiveRegular_mumfordBound_of_hasHyperplaneSections n p e
    (hasHyperplaneSections_of_infinite k ι) j hF hG a hχ

end AlgebraicGeometry.Scheme.Cohomology

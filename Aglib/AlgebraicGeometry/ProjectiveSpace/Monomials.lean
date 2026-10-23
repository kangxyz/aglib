/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.HomogeneousFinrank

/-!
# The monomials of a given degree

`Monomials ι r` is the type of exponents `a : ι →₀ ℕ` of degree `r`, the index type of the
monomial basis `MvPolynomial.homogeneousPieceBasis` of the homogeneous polynomials of degree `r`.
For `ι ≃ Fin (n + 1)` there are `(n + r).choose r` of them (stars and bars,
`Finsupp.natCard_degree_eq`), and `monomialsEquiv ι n e r` numbers them by
`ULift (Fin ((n + r).choose r))` through `Finite.equivFinOfCardEq`, the numbering of
`MvPolynomial.homogeneousSubmoduleEquivFinFun`. It indexes the free sheaf `W ⊗ Sym^r V` of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26, for `W = 𝒪` and
`V = 𝒪^{n+1}`, both in the Grassmannian point of a Hilbert family
(`HilbertScheme/LocallyNoetherianPoint`) and in the universal subscheme
(`HilbertScheme/UniversalSubschemeGrassmannian`).
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u)

/-- The monomials of degree `r` in the coordinates `ι`. -/
abbrev Monomials (r : ℕ) : Type u := {a : ι →₀ ℕ // a.degree = r}

variable (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- The monomials of degree `r` in `n + 1` variables, indexed by `ULift (Fin N)` for
`N = (n + r).choose r`, through `Finite.equivFinOfCardEq` (the indexing of
`MvPolynomial.homogeneousSubmoduleEquivFinFun`; the count is `natCard_degree_eq_choose`). -/
def monomialsEquiv (r : ℕ) : Monomials ι r ≃ ULift.{u} (Fin ((n + r).choose r)) :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  (Finite.equivFinOfCardEq (by
    let := Fintype.ofEquiv _ e.symm
    rw [Finsupp.natCard_degree_eq, Fintype.card_congr e, Fintype.card_fin]
    congr 1
    omega)).trans Equiv.ulift.symm

end AlgebraicGeometry.ProjectiveSpace

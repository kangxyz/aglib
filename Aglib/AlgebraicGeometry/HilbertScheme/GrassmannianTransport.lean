/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Naturality
public import Aglib.RingTheory.MvPolynomial.HomogeneousFinrank

/-!
# The Grassmannian embedding through the monomial basis

Mathlib's Grassmannian functor `Module.Grassmannian.functor k M`, `B ↦ G(k, B ⊗[R] M; B)`, is
functorial in `M` along linear equivalences (`Module.Grassmannian.functorIsoOfLinearEquiv`,
`RingTheory/Grassmannian/LinearEquiv`).

Through the monomial basis `A[x]_r ≅ A^N` (`MvPolynomial.homogeneousSubmoduleEquivFinFun`), with
`N = (n + r).choose r` monomials of degree `r` in `n + 1` variables (stars and bars,
`Finsupp.natCard_degree_eq`, `natCard_degree_eq_choose`), the Grassmannian embedding of the
Hilbert functor on Noetherian affine test schemes takes values in the Grassmannian of rank
`⌊Φ(r)⌋₊` quotients of `A^N` (`noetherianAffineGrassmannianNatTransFin`), the functor
`Module.Grassmannian.functor k (Fin N → A)` that `Grassmannian.localFunctor` and
`Grassmannian.homEquivNatTrans` use (Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §5, p. 26).
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Polynomial TensorProduct

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]

include e in
/-- There are `(n + r).choose r` monomials of degree `r` in `n + 1` variables. -/
theorem natCard_degree_eq_choose (r : ℕ) :
    Nat.card {a : ι →₀ ℕ // a.degree = r} = (n + r).choose r := by
  let := Fintype.ofEquiv _ e.symm
  rw [Finsupp.natCard_degree_eq, Fintype.card_congr e, Fintype.card_fin]
  congr 1
  omega

/-- The Grassmannian embedding with values in the Grassmannian of quotients of `A^N`, through the
monomial basis `A[x]_r ≅ A^N`, `N = (n + r).choose r` the number of monomials of degree `r`. -/
def noetherianAffineGrassmannianNatTransFin (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    noetherianAffineHilbertFunctor ι A Φ ⟶ ObjectProperty.ι _ ⋙
      Module.Grassmannian.functor.{u, u, u} (R := A)
        (M := Fin ((n + r).choose r) → A) ⌊Φ.eval (r : ℚ)⌋₊ :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  noetherianAffineGrassmannianNatTrans ι n e A Φ r hr ≫ Functor.whiskerLeft _
    (Module.Grassmannian.functorIsoOfLinearEquiv _
      (MvPolynomial.homogeneousSubmoduleEquivFinFun ι A r (natCard_degree_eq_choose ι n e r))).hom

end AlgebraicGeometry.ProjectiveSpace

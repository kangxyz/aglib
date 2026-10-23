/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Point
public import Aglib.RingTheory.Grassmannian.LinearEquiv
public import Aglib.RingTheory.MvPolynomial.HomogeneousBaseChange

/-!
# The Grassmannian point in Mathlib's Grassmannian functor

For an `A`-algebra `B`, Mathlib's `Module.Grassmannian.functor k` (on `CommAlgCat A`) takes the
value `G(k, B ⊗[A] M; B)`; here `M = A[x]_r = MvPolynomial.homogeneousSubmodule ι A r`, the free
`A`-module of homogeneous polynomials of degree `r`. This file transports the Grassmannian point
`IsHilbertFamily.grassmannianPoint` of a point `Z` of `Hilb^Φ(Spec B)` (`B` Noetherian) to that
value (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26):

* `ProjectiveSpace.unitTwistH0Equiv`: `B ⊗[A] A[x]_r ≃ₗ[B] H^0(P^n_B, 𝒪(r) ⊗ 𝒪)`, through
  `MvPolynomial.homogeneousSubmoduleBaseChangeEquiv : B ⊗[A] A[x]_r ≃ₗ[B] B[x]_r`
  (`RingTheory/MvPolynomial/HomogeneousBaseChange`) and `twistingH0PolynomialLinearEquiv`;
* `IsHilbertFamily.grassmannianFunctorPoint`: the point of
  `(Module.Grassmannian.functor (R := A) (M := A[x]_r) ⌊Φ(r)⌋₊).obj B`, transported along
  `unitTwistH0Equiv` by `Module.Grassmannian.ofLinearEquiv` (`RingTheory/Grassmannian/LinearEquiv`),
  and its injectivity `IsHilbertFamily.eq_of_grassmannianFunctorPoint_eq`.

The naturality of `grassmannianFunctorPoint` in `B` is `HilbertScheme/Naturality`. By
`Module.Grassmannian.map_eq_of_forall` (`RingTheory/Grassmannian/MapCriterion`) it reduces to the
geometric inclusion: `f ⊗ id` maps the sections of `𝒪(r)` vanishing on `Z` into those vanishing on
the pullback of `Z` to `P^n_{B'}`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped Polynomial TensorProduct

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- **The global sections of `𝒪(r)` over `P^n_B` are `B ⊗[A] A[x]_r`**, linearly over `B`. -/
def unitTwistH0Equiv (B : Type u) [CommRing B] [Algebra A B] (r : ℕ) :
    letI := h0Module ι (unitTwist (B := B) ι r)
    B ⊗[A] MvPolynomial.homogeneousSubmodule ι A r ≃ₗ[B]
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (unitTwist (B := B) ι r)) 0 :=
  letI := Fintype.ofEquiv (Fin (n + 1)) e.symm
  (MvPolynomial.homogeneousSubmoduleBaseChangeEquiv ι r A B).trans
    ((twistingH0PolynomialLinearEquiv B ι (e.symm 0) r).symm.trans
      ((moduleCohomologyFunctorOfHom (ProjectiveSpace B ι)
        ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) 0).mapIso
          (ρ_ (twistingSheaf B ι (r : ℤ))).symm).toLinearEquiv)

variable {Φ : ℚ[X]}

/-- **The point of Mathlib's Grassmannian functor** (Nitsure, arXiv:math/0504590v1, §5, p. 26):
for an `A`-algebra `B` with `B` Noetherian, a point `Z` of `Hilb^Φ(Spec B)` and a natural number
`r ≥ hilbertRegularityBound n Φ`, the kernel of `B ⊗[A] A[x]_r ≅ H^0(𝒪(r)) ↠ H^0(𝒪_Z(r))`, a point
of `G(⌊Φ(r)⌋₊, B ⊗[A] A[x]_r; B) = (Module.Grassmannian.functor ⌊Φ(r)⌋₊).obj B`. -/
def IsHilbertFamily.grassmannianFunctorPoint {B : Type u} [CommRing B] [Algebra A B]
    [IsNoetherianRing B] {Z : (pullback (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).IdealSheafData}
    (hZ : IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B))) Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    Module.Grassmannian B (B ⊗[A] MvPolynomial.homogeneousSubmodule ι A r) ⌊Φ.eval (r : ℚ)⌋₊ :=
  letI := h0Module ι (unitTwist (B := B) ι r)
  Module.Grassmannian.ofLinearEquiv (unitTwistH0Equiv ι n e B r).symm
    (hZ.grassmannianPoint ι n e (𝟙 _) r hr)

include e in
/-- **Injectivity of the point of the Grassmannian functor**: two points of `Hilb^Φ(Spec B)`,
`B` Noetherian, with the same point of `(Module.Grassmannian.functor ⌊Φ(r)⌋₊).obj B` in a degree
`r ≥ hilbertRegularityBound n Φ`, are equal. -/
theorem IsHilbertFamily.eq_of_grassmannianFunctorPoint_eq {B : Type u} [CommRing B]
    [Algebra A B] [IsNoetherianRing B]
    {Z Z' : (pullback (toSpec A ι)
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).IdealSheafData}
    (hZ : IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B))) Z)
    (hZ' : IsHilbertFamily ι Φ (Spec.map (CommRingCat.ofHom (algebraMap A B))) Z') (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (h : hZ.grassmannianFunctorPoint ι n e r hr = hZ'.grassmannianFunctorPoint ι n e r hr) :
    Z = Z' := by
  let := h0Module ι (unitTwist (B := B) ι r)
  exact hZ.eq_of_grassmannianPoint_eq ι n e hZ' r hr
    (Module.Grassmannian.ofLinearEquiv_injective _ h)

end ProjectiveSpace

end AlgebraicGeometry

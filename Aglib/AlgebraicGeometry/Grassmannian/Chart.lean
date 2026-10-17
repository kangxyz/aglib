/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.ChartRing
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Affine charts of the Grassmannian over `Spec R`

For a commutative ring `R` and a tuple `x : Fin k → (Fin n → R)`, the chart scheme
`chartScheme R x = Spec (ChartRing R x)` over `Spec R` represents the chart functor on all
schemes over `Spec R`: a morphism `T ⟶ chartScheme R x` over `Spec R` is the same as a point of
Mathlib's Grassmannian `G(k, Γ(T, ⊤) ⊗[R] (Fin n → R); Γ(T, ⊤))` in the chart at `1 ⊗ x`.
The global sections functor is Mathlib's `AlgebraicGeometry.algΓ`, and the equivalence is
Mathlib's adjunction `algΓAlgSpecAdjunction` composed with the corepresentation
`Module.Grassmannian.chartFunctorCorepresentableBy`.

This is the representability of the subfunctors `F_i` of the Grassmannian functor in Stacks,
Tag 089T, where `F_i(S)` is identified with a product of copies of `Γ(S, O_S)`. For a coordinate
tuple `x b = e_{I b}` with `I` injective (an ordering of a `k`-subset of `Fin n`), the chart
scheme is Nitsure's affine chart `U^I` (arXiv:math/0504590v1, §1, "Construction of
Grassmannian", p. 8) over `Spec R`; for a non-injective `I` the chart ring is the zero ring and
the chart scheme is empty.

## Main definitions and results

- `AlgebraicGeometry.Grassmannian.chartScheme`: the chart `Spec (ChartRing R x)` over `Spec R`.
- `AlgebraicGeometry.Grassmannian.chartFunctor`: `T ↦` points of the chart at `1 ⊗ x` over
  `Γ(T, ⊤)`, as a functor on `Over (Spec R)`.
- `AlgebraicGeometry.Grassmannian.chartRepresentableBy`: `chartFunctor R x` is represented by
  `chartScheme R x`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Grassmannian

variable (R : CommRingCat.{u}) {k n : ℕ}

/-- The chart of the Grassmannian at `x`, the spectrum of `ChartRing R x` over `Spec R`. -/
abbrev chartScheme (x : Fin k → Fin n → R) : Over (Spec R) :=
  (algSpec R).obj (op (CommAlgCat.of R (Module.Grassmannian.ChartRing R x)))

/-- The chart functor at `x` on schemes over `Spec R`: a scheme `T` over `Spec R` is sent to the
points of `G(k, Γ(T, ⊤) ⊗[R] (Fin n → R); Γ(T, ⊤))` in the chart at `1 ⊗ x`. -/
def chartFunctor [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x : Fin k → Fin n → R) : (Over (Spec R))ᵒᵖ ⥤ Type u :=
  (algΓ R).leftOp ⋙ (Module.Grassmannian.chartFunctor.{u, u, u} R x).toFunctor

/-- The chart scheme represents the chart functor on all schemes over `Spec R`. -/
def chartRepresentableBy [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x : Fin k → Fin n → R) :
    (chartFunctor R x).RepresentableBy (chartScheme R x) where
  homEquiv {T} :=
    ((algΓAlgSpecAdjunction R).homEquiv T _).symm.trans <|
      (opEquiv _ _).trans (Module.Grassmannian.chartFunctorCorepresentableBy R x).homEquiv
  homEquiv_comp {T T'} f g := by
    change (Module.Grassmannian.chartFunctorCorepresentableBy R x).homEquiv
        (((algΓAlgSpecAdjunction R).homEquiv T _).symm (f ≫ g)).unop = _
    rw [Adjunction.homEquiv_naturality_left_symm, unop_comp,
      Functor.CorepresentableBy.homEquiv_comp]
    rfl

theorem chartFunctor_isRepresentable
    [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]
    (x : Fin k → Fin n → R) :
    (chartFunctor R x).IsRepresentable :=
  (chartRepresentableBy R x).isRepresentable

end AlgebraicGeometry.Grassmannian

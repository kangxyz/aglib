/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Surjectivity

/-!
# The Grassmannian represents rank-`k` locally free quotients of `O^n`

For `R : CommRingCat` and `k n : ℕ`, the natural transformation
`toLocalFunctor R k n : quotFunctor R k n ⟶ Grassmannian.localFunctor R k n`, sending a class of
rank-`k` locally free quotients `O_T^n ↠ Q` to its Grassmannian points on affine schemes over `T`,
is bijective on every scheme `T` over `Spec R` (`toPointsNatTrans_injective`,
`toPointsNatTrans_surjective`). Hence
`quotFunctorIso R k n : quotFunctor R k n ≅ localFunctor R k n` and, with
`Grassmannian.localFunctorRepresentableBy`, the glued Grassmannian `schemeOver R k n` represents
`Quot_k(O^n)` on all schemes over `Spec R` (`quotFunctorRepresentableBy`). The universal quotient
is the class corresponding to the identity, `universalQuotient R k n`, with a representative
`universalQuotientRep R k n`.

Sources: Stacks, Tag 089S (eq. (27.22.0.1), the functor) and Tag 089T (Lemma 27.22.1), TeX
snapshot `a04446e5`; Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
§1, Elementary Examples, Exercises (2) "Grassmannian as a Quot scheme", p. 5, with the
construction on pp. 7–8 and the universal quotient on p. 9. Encoded subset:
`O^n = SheafOfModules.free (ULift (Fin n))` on schemes over `Spec R`, all `k` and `n` (Stacks
assumes `0 < k < n`). Convention: `k` is the rank of the quotient, so this is Stacks' `G(n − k, n)`
and Nitsure's `Grass(n, k)`. The route differs from Stacks' subfunctor criterion: it compares with
the glued scheme through `localFunctor` and Zariski descent of module sheaves. The identification
of the universal quotient with Nitsure's chart quotients (p. 9) is not stated.

All statements assume the named premise `Module.Grassmannian.BaseChangeMkQFormula`, which
`Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

variable (R : CommRingCat.{u}) (k n : ℕ)
variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

instance isIso_toLocalFunctor : IsIso (toLocalFunctor R k n) := by
  have : ∀ T, IsIso ((toLocalFunctor R k n).app T) := fun T ↦
    (isIso_iff_bijective _).mpr
      ⟨toPointsNatTrans_injective T.unop, toPointsNatTrans_surjective T.unop⟩
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks, Tag 089T**: rank-`k` locally free quotients of `O^n` are the points of the
functor represented by the Grassmannian.

Sources: Stacks, Tag 089S (eq. (27.22.0.1)) and Tag 089T (Lemma 27.22.1), TeX snapshot
`a04446e5`; Nitsure, arXiv:math/0504590v1, §1, Elementary Examples, Exercises (2) "Grassmannian as
a Quot scheme", p. 5, with the construction on pp. 7–8. Encoded subset:
`O^n = SheafOfModules.free (ULift (Fin n))` on schemes over `Spec R`, all `k` and `n` (Stacks
assumes `0 < k < n`). Convention: `k` is the rank of the quotient, so this is Stacks' `G(n − k, n)`
and Nitsure's `Grass(n, k)`. Premise: `BaseChangeMkQFormula`, supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
def quotFunctorIso : quotFunctor R k n ≅ localFunctor R k n :=
  asIso (toLocalFunctor R k n)

/-- The inverse direction of `quotFunctorIso`: `Grassmannian.localFunctor R k n ≅ Quot_k(O^n)`. -/
def localFunctorIsoQuotFunctor : localFunctor R k n ≅ quotFunctor R k n :=
  (quotFunctorIso R k n).symm

/-- **The Grassmannian represents `Quot_k(O^n)`** on all schemes over `Spec R`.

Sources: Stacks, Tag 089T (Lemma 27.22.1), TeX snapshot `a04446e5`; Nitsure,
arXiv:math/0504590v1, §1, Elementary Examples, Exercises (2) "Grassmannian as a Quot scheme",
p. 5, with the construction on pp. 7–8 and the universal quotient on p. 9. Encoded subset:
`O^n = SheafOfModules.free (ULift (Fin n))` on schemes over `Spec R`, all `k` and `n` (Stacks
assumes `0 < k < n`). Convention: `k` is the rank of the quotient, so this is Stacks' `G(n − k, n)`
and Nitsure's `Grass(n, k)`. Premise: `BaseChangeMkQFormula`, supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
def quotFunctorRepresentableBy : (quotFunctor R k n).RepresentableBy (schemeOver R k n) :=
  (localFunctorRepresentableBy R k n).ofIso (localFunctorIsoQuotFunctor R k n)

/-- The universal rank-`k` locally free quotient of `O^n` on the Grassmannian: the class
corresponding to the identity of `schemeOver R k n`. -/
def universalQuotient : (quotFunctor R k n).obj (op (schemeOver R k n)) :=
  (quotFunctorRepresentableBy R k n).homEquiv (𝟙 _)

/-- A representative of the universal quotient: an epimorphism `O^n ⟶ Q_univ` on the Grassmannian
with `Q_univ` finite locally free of constant rank `k`. -/
def universalQuotientRep : LocallyFreeQuotient (schemeOver R k n).left k n :=
  Quotient.out (s := LocallyFreeQuotient.setoid (schemeOver R k n).left k n)
    (universalQuotient R k n)

theorem mk_universalQuotientRep :
    (Quotient.mk _ (universalQuotientRep R k n) : (quotFunctor R k n).obj (op (schemeOver R k n))) =
      universalQuotient R k n :=
  Quotient.out_eq (s := LocallyFreeQuotient.setoid (schemeOver R k n).left k n) _

/-- Every class of quotients on `T` is the pullback of the universal quotient along the
corresponding map to the Grassmannian. -/
theorem quotFunctorRepresentableBy_homEquiv {T : Over (Spec R)} (g : T ⟶ schemeOver R k n) :
    (quotFunctorRepresentableBy R k n).homEquiv g =
      (quotFunctor R k n).map g.op (universalQuotient R k n) := by
  rw [universalQuotient, ← (quotFunctorRepresentableBy R k n).homEquiv_comp, Category.comp_id]

end AlgebraicGeometry.Grassmannian

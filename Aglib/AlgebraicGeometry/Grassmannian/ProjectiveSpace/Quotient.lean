/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace.FunctorOfPoints
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Representability

/-!
# Projective space represents rank-one locally free quotients

For `R : CommRingCat` and a labeling `e : ι ≃ Fin m`, projective space
`ProjectiveSpace.schemeOver R ι` represents the functor `Grassmannian.quotFunctor R 1 m` of
rank-one locally free quotients `O_T^m ↠ L` on schemes over `Spec R`
(`ProjectiveSpace.quotFunctorRepresentableBy`). It composes the representation of
`Grassmannian.localFunctor R 1 m` by projective space (`localFunctorRepresentableBy`, through the
comparison `Gr(R^m, 1) ≅ P`) with `Grassmannian.localFunctorIsoQuotFunctor R 1 m`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : CommRingCat.{u}) {ι : Type u} {m : ℕ} (e : ι ≃ Fin m)

/-- **Projective space represents rank-one locally free quotients of `O^m`** on all schemes over
`Spec R`: maps `T ⟶ P(R^ι)` over `Spec R` are the isomorphism classes of epimorphisms
`O_T^m ⟶ L` with `L` finite locally free of rank one.

Sources: Stacks, Tag 089V (Lemma 27.22.3, `G(n, n + 1) = P^n`) and Tag 01NE (`P^n` represents
invertible modules with `n + 1` generating global sections), TeX snapshot `a04446e5`. Stacks writes
`n = m - 1` and assumes `n ≥ 1` in Tag 089V; the declaration covers every `m`. Encoded subset:
quotients of `O^m = SheafOfModules.free (ULift (Fin m))` on schemes over `Spec R`; the form with
`O^ι` needs reindexing along `e`, which is not done here. The identification of the universal
quotient with the quotient `O^ι ↠ O(1)` of the coordinate sections
(`coordinatePowerGeneratingMap R ι 1`) is open. The Grassmannian premise `BaseChangeMkQFormula`
is the imported instance of `Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
def quotFunctorRepresentableBy :
    (Grassmannian.quotFunctor R 1 m).RepresentableBy (schemeOver R ι) :=
  (localFunctorRepresentableBy R e).ofIso (Grassmannian.localFunctorIsoQuotFunctor R 1 m)

end AlgebraicGeometry.ProjectiveSpace

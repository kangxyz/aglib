/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Representability
public import Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace.Quotient

/-!
# Locally free quotients and Grassmannian points

The instance in `Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies the premise
`Module.Grassmannian.BaseChangeMkQFormula`. The declarations below restate, with no hypothesis,
the functor `Quot_k(O^n)` of rank-`k` locally free quotients of `O^n` on schemes over `Spec R`, the
natural transformation from it to `Grassmannian.localFunctor R k n` (the functor represented by
the Grassmannian), its injectivity and surjectivity on every scheme over `Spec R`, the resulting
natural isomorphism (Stacks, Tag 089T), the representability of `Quot_k(O^n)` by the Grassmannian
`schemeOver R k n`, the universal property of the universal quotient, the representability of
rank-one quotients by projective space, and the bijection with Mathlib's Grassmannian points on
affine schemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped Module.Grassmannian

universe u

namespace AglibTest.GrassmannianQuotient

/-- The functor `Quot_k(O^n)` on schemes over `Spec R`. -/
def quotFunctor (R : CommRingCat.{u}) (k n : ℕ) : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1) :=
  AlgebraicGeometry.Grassmannian.quotFunctor R k n

/-- Quotients give Grassmannian points, naturally in the test scheme. -/
def toLocalFunctor (R : CommRingCat.{u}) (k n : ℕ) :
    quotFunctor R k n ⟶ Grassmannian.localFunctor R k n :=
  AlgebraicGeometry.Grassmannian.toLocalFunctor R k n

/-- On every scheme over `Spec R`, a class of quotients is determined by its points. -/
theorem toLocalFunctor_app_injective (R : CommRingCat.{u}) (k n : ℕ) (T : (Over (Spec R))ᵒᵖ) :
    Function.Injective ((toLocalFunctor R k n).app T) :=
  AlgebraicGeometry.Grassmannian.toPointsNatTrans_injective T.unop

/-- On every scheme over `Spec R`, every Grassmannian point comes from a quotient. -/
theorem toLocalFunctor_app_surjective (R : CommRingCat.{u}) (k n : ℕ) (T : (Over (Spec R))ᵒᵖ) :
    Function.Surjective ((toLocalFunctor R k n).app T) :=
  AlgebraicGeometry.Grassmannian.toPointsNatTrans_surjective T.unop

/-- **Stacks, Tag 089T**: `Grassmannian.localFunctor R k n ≅ Quot_k(O^n)`.

Sources: Stacks, Tag 089S (eq. (27.22.0.1), the functor) and Tag 089T (Lemma 27.22.1), TeX
snapshot `a04446e5`; Nitsure, arXiv:math/0504590v1, §1, Elementary Examples, Exercises (2)
"Grassmannian as a Quot scheme", p. 5, with the construction on pp. 7–8 and the universal quotient
on p. 9. Encoded subset: `O^n = SheafOfModules.free (ULift (Fin n))` on schemes over `Spec R`, all
`k` and `n` (Stacks assumes `0 < k < n`). Convention: `k` is the rank of the quotient, so this is
Stacks' `G(n − k, n)` and Nitsure's `Grass(n, k)`. Premise: `BaseChangeMkQFormula`, supplied here
by the instance of `Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
def localFunctorIsoQuotFunctor (R : CommRingCat.{u}) (k n : ℕ) :
    Grassmannian.localFunctor R k n ≅ quotFunctor R k n :=
  AlgebraicGeometry.Grassmannian.localFunctorIsoQuotFunctor R k n

example (R : CommRingCat.{u}) (k n : ℕ) :
    (localFunctorIsoQuotFunctor R k n).inv = toLocalFunctor R k n :=
  rfl

/-- The isomorphism `Quot_k(O^n) ≅ localFunctor R k n`. -/
def quotFunctorIso (R : CommRingCat.{u}) (k n : ℕ) :
    quotFunctor R k n ≅ Grassmannian.localFunctor R k n :=
  AlgebraicGeometry.Grassmannian.quotFunctorIso R k n

/-- The Grassmannian represents `Quot_k(O^n)` on all schemes over `Spec R`. -/
def quotFunctorRepresentableBy (R : CommRingCat.{u}) (k n : ℕ) :
    (quotFunctor R k n).RepresentableBy (Grassmannian.schemeOver R k n) :=
  AlgebraicGeometry.Grassmannian.quotFunctorRepresentableBy R k n

/-- Every class of quotients on `T` is the pullback of the universal quotient along its classifying
map. -/
theorem quotFunctorRepresentableBy_homEquiv (R : CommRingCat.{u}) (k n : ℕ) {T : Over (Spec R)}
    (g : T ⟶ Grassmannian.schemeOver R k n) :
    (quotFunctorRepresentableBy R k n).homEquiv g =
      (quotFunctor R k n).map g.op (AlgebraicGeometry.Grassmannian.universalQuotient R k n) :=
  AlgebraicGeometry.Grassmannian.quotFunctorRepresentableBy_homEquiv R k n g

/-- Projective space represents rank-one locally free quotients of `O^m` (F9 item 2c). -/
def projectiveSpaceQuotFunctorRepresentableBy (R : CommRingCat.{u}) {ι : Type u} {m : ℕ}
    (e : ι ≃ Fin m) : (quotFunctor R 1 m).RepresentableBy (ProjectiveSpace.schemeOver R ι) :=
  ProjectiveSpace.quotFunctorRepresentableBy R e

/-- The universal quotient on the Grassmannian, as an explicit epimorphism `O^n ⟶ Q_univ`. -/
def universalQuotientRep (R : CommRingCat.{u}) (k n : ℕ) :
    AlgebraicGeometry.Grassmannian.LocallyFreeQuotient (Grassmannian.schemeOver R k n).left k n :=
  AlgebraicGeometry.Grassmannian.universalQuotientRep R k n

example (R : CommRingCat.{u}) (k n : ℕ) : Epi (universalQuotientRep R k n).π := inferInstance

example (R : CommRingCat.{u}) (k n : ℕ) :
    Scheme.Modules.SheafHasRank (universalQuotientRep R k n).obj k :=
  (universalQuotientRep R k n).hasRank

/-- On `Spec A`, classes of quotients are the points of `G(k, A ⊗[R] (Fin n → R); A)`. -/
theorem affinePoint_bijective (R : CommRingCat.{u}) (k n : ℕ) (A : CommAlgCat.{u} R) :
    Function.Bijective (AlgebraicGeometry.Grassmannian.affinePoint (k := k) (n := n) A) :=
  AlgebraicGeometry.Grassmannian.affinePoint_bijective A

/-- The affine bijection commutes with base change. -/
theorem affinePoint_pullback (R : CommRingCat.{u}) (k n : ℕ) {A B : CommAlgCat.{u} R}
    (f : A ⟶ B)
    (P : AlgebraicGeometry.Grassmannian.LocallyFreeQuotient (Spec (CommRingCat.of A)) k n) :
    AlgebraicGeometry.Grassmannian.affinePoint B
        (Quotient.mk _ (P.pullback (Spec.map (CommRingCat.ofHom (f.hom : A →+* B))))) =
      Module.Grassmannian.map f.hom
        (AlgebraicGeometry.Grassmannian.affinePoint A (Quotient.mk _ P)) :=
  AlgebraicGeometry.Grassmannian.affinePoint_pullback f P

/-- info: 'AglibTest.GrassmannianQuotient.quotFunctor' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.quotFunctor

/-- info: 'AglibTest.GrassmannianQuotient.toLocalFunctor' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.toLocalFunctor

/-- info: 'AglibTest.GrassmannianQuotient.toLocalFunctor_app_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.toLocalFunctor_app_injective

/-- info: 'AglibTest.GrassmannianQuotient.affinePoint_bijective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.affinePoint_bijective

/-- info: 'AglibTest.GrassmannianQuotient.affinePoint_pullback' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.affinePoint_pullback

/-- info: 'AglibTest.GrassmannianQuotient.toLocalFunctor_app_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.toLocalFunctor_app_surjective

/-- info: 'AglibTest.GrassmannianQuotient.localFunctorIsoQuotFunctor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.localFunctorIsoQuotFunctor

/-- info: 'AglibTest.GrassmannianQuotient.quotFunctorRepresentableBy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.quotFunctorRepresentableBy

/-- info: 'AglibTest.GrassmannianQuotient.universalQuotientRep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.universalQuotientRep

/-- info: 'AglibTest.GrassmannianQuotient.quotFunctorIso' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.quotFunctorIso

/-- info: 'AglibTest.GrassmannianQuotient.quotFunctorRepresentableBy_homEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.quotFunctorRepresentableBy_homEquiv

/-- info: 'AglibTest.GrassmannianQuotient.projectiveSpaceQuotFunctorRepresentableBy' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianQuotient.projectiveSpaceQuotFunctorRepresentableBy

end AglibTest.GrassmannianQuotient

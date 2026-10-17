/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Grassmannian.Representability
public import Aglib.AlgebraicGeometry.Grassmannian.FunctorOfPoints

/-!
# Representability of Mathlib's Grassmannian functor

The instance in `Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies the premise
`Module.Grassmannian.BaseChangeMkQFormula`, so the declarations below state, with no hypothesis,
that the glued scheme `schemeOver R k n` represents Mathlib's `Module.Grassmannian.functor` on
`R`-algebras, and that maps from an arbitrary scheme over `Spec R` into it are the natural
transformations from its functor of points on `R`-algebras to Mathlib's functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped Module.Grassmannian

universe u

namespace AglibTest.GrassmannianScheme

/-- Maps `Spec A ⟶ Gr` over `Spec R` are the points of `G(k, A ⊗[R] (Fin n → R); A)`. -/
def representableEquiv (R : CommRingCat.{u}) (k n : ℕ) (A : CommAlgCat.{u} R) :
    ((algSpec R).obj (op A) ⟶ Grassmannian.schemeOver R k n) ≃
      G(k, A ⊗[R] (Fin n → R); A) :=
  AlgebraicGeometry.Grassmannian.representableEquiv R k n A

/-- The identification is natural: precomposition with `Spec h` is base change along `h`. -/
theorem representableEquiv_comp (R : CommRingCat.{u}) (k n : ℕ) {A B : CommAlgCat.{u} R}
    (h : A ⟶ B) (g : (algSpec R).obj (op A) ⟶ Grassmannian.schemeOver R k n) :
    representableEquiv R k n B ((algSpec R).map h.op ≫ g) =
      Module.Grassmannian.map h.hom (representableEquiv R k n A g) :=
  AlgebraicGeometry.Grassmannian.homPoint_comp g h

/-- The glued Grassmannian represents Mathlib's Grassmannian functor on `R`-algebras. -/
def representableIso (R : CommRingCat.{u}) (k n : ℕ) :
    (algSpec R).rightOp ⋙ yoneda.obj (Grassmannian.schemeOver R k n) ≅
      Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k :=
  AlgebraicGeometry.Grassmannian.representableIso R k n

example (R : CommRingCat.{u}) (k n : ℕ) (A : CommAlgCat.{u} R)
    (g : (algSpec R).obj (op A) ⟶ Grassmannian.schemeOver R k n) :
    (representableIso R k n).hom.app A g = representableEquiv R k n A g :=
  rfl

/-- Maps from any scheme over `Spec R` into the Grassmannian are the natural transformations
from its functor of points on `R`-algebras to Mathlib's Grassmannian functor. -/
def homEquivNatTrans (R : CommRingCat.{u}) (k n : ℕ) (T : Over (Spec R)) :
    (T ⟶ Grassmannian.schemeOver R k n) ≃
      ((algSpec R).rightOp ⋙ yoneda.obj T ⟶
        Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k) :=
  AlgebraicGeometry.Grassmannian.homEquivNatTrans k n T

/-- On an affine scheme `Spec A`, the transformation attached to `g` sends a point
`v : Spec B ⟶ Spec A` to the point of `v ≫ g` over `B`. -/
example (R : CommRingCat.{u}) (k n : ℕ) (T : Over (Spec R)) (g : T ⟶ Grassmannian.schemeOver R k n)
    (B : CommAlgCat.{u} R) (v : (algSpec R).obj (op B) ⟶ T) :
    (homEquivNatTrans R k n T g).app B v = representableEquiv R k n B (v ≫ g) :=
  rfl

/-- The represented functor on all schemes over `Spec R`. -/
example (R : CommRingCat.{u}) (k n : ℕ) (T : Over (Spec R)) :
    (AlgebraicGeometry.Grassmannian.localFunctor R k n).obj (op T) =
      ((algSpec R).rightOp ⋙ yoneda.obj T ⟶
        Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k) :=
  rfl

/-- The represented functor acts on maps of test schemes by precomposition. -/
example (R : CommRingCat.{u}) (k n : ℕ) {T' T : Over (Spec R)} (t : T' ⟶ T)
    (β : (AlgebraicGeometry.Grassmannian.localFunctor R k n).obj (op T)) :
    (AlgebraicGeometry.Grassmannian.localFunctor R k n).map t.op β =
      Functor.whiskerLeft (algSpec R).rightOp (yoneda.map t) ≫ β :=
  rfl

/-- The Grassmannian represents the extension of Mathlib's functor to all schemes over
`Spec R`. -/
def localFunctorIso (R : CommRingCat.{u}) (k n : ℕ) :
    yoneda.obj (Grassmannian.schemeOver R k n) ⋙ uliftFunctor.{u + 1} ≅
      AlgebraicGeometry.Grassmannian.localFunctor R k n :=
  AlgebraicGeometry.Grassmannian.localFunctorIso R k n

/-- The same representability as a `Functor.RepresentableBy` with values in `Type (u + 1)`. -/
def localFunctorRepresentableBy (R : CommRingCat.{u}) (k n : ℕ) :
    (AlgebraicGeometry.Grassmannian.localFunctor R k n).RepresentableBy
      (Grassmannian.schemeOver R k n) :=
  AlgebraicGeometry.Grassmannian.localFunctorRepresentableBy R k n

end AglibTest.GrassmannianScheme

/-- info: 'AglibTest.GrassmannianScheme.representableIso' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianScheme.representableIso

/-- info: 'AglibTest.GrassmannianScheme.representableEquiv' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianScheme.representableEquiv

/-- info: 'AglibTest.GrassmannianScheme.representableEquiv_comp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianScheme.representableEquiv_comp

/-- info: 'AlgebraicGeometry.Grassmannian.representableIso' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.representableIso

/-- info: 'AlgebraicGeometry.Grassmannian.pointHom_homPoint' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.pointHom_homPoint

/-- info: 'AlgebraicGeometry.Grassmannian.homPoint_pointHom' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Grassmannian.homPoint_pointHom

/-- info: 'AglibTest.GrassmannianScheme.homEquivNatTrans' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianScheme.homEquivNatTrans

/-- info: 'AglibTest.GrassmannianScheme.localFunctorIso' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianScheme.localFunctorIso

/-- info: 'AlgebraicGeometry.algSpecPointsEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.algSpecPointsEquiv

/-- info: 'AglibTest.GrassmannianScheme.localFunctorRepresentableBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.GrassmannianScheme.localFunctorRepresentableBy

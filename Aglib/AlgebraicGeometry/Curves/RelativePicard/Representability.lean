/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RelativePicard.DegreeZero
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Representing the actual degree-zero Picard functor

The incoming family asks for a locally Noetherian representing F-scheme and a natural bijection
on every test scheme for the independently constructed, origin-normalized,
geometric-fibre-degree-zero Picard functor. It neither supplies a group law
on the curve nor states that its Abel map is an isomorphism. The group object
on the representing scheme is derived by Yoneda from the already constructed
commutative group functor.

Source: J. S. Milne, Jacobian Varieties, June 12, 2021, Theorem 1.1 and
Lemma 1.3, PDF pages 2–3, https://www.jmilne.org/math/xnotes/JVs.pdf.
These statements apply over an arbitrary field. A rational origin gives a
section over every test scheme, so the normalized classes agree with the
relative Picard quotient and the possible sheafification discrepancy vanishes.
Remark 1.5 explains the role of universal constants in the descent argument.
The retained derived specialization includes identifying our geometric-field
fibre degree test with Milne's fibrewise degree, using field-base-change
invariance of the residue-weighted divisor degree. This latter compatibility
is part of the source boundary, not claimed here as an already proved lemma.
The primary PDF and this applicability span were inspected on 2026-10-09;
this is not an independent verification of every cited proof dependency.

Incoming functor: RelativePicard.DegreeZero, with actual line-bundle classes,
actual pullbacks, actual C divisor degree, and arbitrary (also nonreduced)
test schemes. Its previously disclosed B1, product-formula and optional
all-module tensor-pullback families remain explicit parameters.
Application K2-018#prop:k2018-arithmetic-characters, mathematical revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothClosedPointDimension SmoothFieldDimension SmoothFieldNormality
    SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme.OverField.Curve
open CategoryTheory.MonObj
namespace AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard
universe u
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : AlgebraicGeometry.Scheme.Modules.Invertible.ModuleTensorPullback.{u})

/-- The normalized degree-zero Picard functor on all test schemes, written
as a functor to commutative groups using the additive-to-multiplicative equivalence. -/
def degreeZeroCommGroupFunctor {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)
    (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) : (FScheme F)ᵒᵖ ⥤ CommGrpCat.{u+1} :=
  degreeZeroGroupFunctor hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho ⋙
    AddCommGrpCat.toCommGrp

/-- General all-field, all-genus representability by a locally Noetherian scheme,
with every test scheme included. Local Noetherianity refines the same incoming
representer witness; it is an explicit geometric input, not a consequence of
mere representability. No reducedness hypothesis is imposed. -/
def DegreeZeroPicardRepresentability : Prop :=
  ∀ (F : Type u) [Field F] (X : FScheme F) (hX : Properties X)
    (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _),
    ∃ P : FScheme F, IsLocallyNoetherian P.left ∧
      Nonempty ((degreeZeroCommGroupFunctor hnormal hcomp hreg hclosed hdim hprod htensor
        X hX o ho ⋙ CategoryTheory.forget CommGrpCat).RepresentableBy P)

variable (hrep : DegreeZeroPicardRepresentability hnormal hcomp hreg hclosed hdim hprod htensor)
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)
variable (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

/-- An actual representing scheme chosen from the general representation theorem. -/
def representingScheme : FScheme F := (hrep F X hX o ho).choose

/-- The same chosen representer carries the explicit local Noetherianity
contained in the incoming representability witness. -/
instance representingScheme_isLocallyNoetherian :
    IsLocallyNoetherian
      (representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho).left :=
  (hrep F X hX o ho).choose_spec.1

/-- The representing bijection, natural on all test schemes. -/
def representingEquivalence :
    (degreeZeroCommGroupFunctor hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho ⋙
      CategoryTheory.forget CommGrpCat).RepresentableBy
        (representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho) :=
  (hrep F X hX o ho).choose_spec.2.some

/-- The group laws are derived from the Picard functor, rather than supplied as data. -/
@[instance_reducible] def representingCommGroup :
    CommGrpObj (representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho) :=
  CommGrpObj.ofRepresentableBy _
    (degreeZeroCommGroupFunctor hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho)
    (representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho)

theorem representing_identity_class :
    letI := representingCommGroup hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho
    (representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho).homEquiv
      (η[(representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho)]) = 1
        := by
  let e := representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho
  change e.homEquiv (e.homEquiv.symm 1) = 1
  exact e.homEquiv.apply_symm_apply 1
end AlgebraicGeometry.Scheme.OverField.Curve.RelativePicard

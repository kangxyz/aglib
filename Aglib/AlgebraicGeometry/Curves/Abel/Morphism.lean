/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RelativePicard.Representability
public import Aglib.AlgebraicGeometry.Curves.Abel.Degree
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# The actual Abel morphism into the representing Picard scheme

The morphism is the inverse representing correspondence applied to the
independently constructed degree-zero Abel class of the identity section.
Naturality proves its formula on every test scheme: it sends a section s to
the origin-normalized class of O(graph(s)-graph(o)). At the origin it is the
identity of the commutative group object derived from the Picard functor.
The multiplicative presentation is only the standard AddCommGrp/CommGrp
conversion; its identity is the actual zero Picard class.

No new standard family is introduced. The explicit parameters are the
previously disclosed curve/degree foundations, Cartier graph ideals and
base change, tensor pullback, and the general all-field Picard representation.
No inverse to the Abel morphism, genus-one isomorphism, or group law on X
is supplied or asserted in this module. Those remain subsequent applications.
Incoming Representability SHA256
3afd767a98e5b0c998a18ddc9918e675c57e8b721f70b8e77731f583795d8d12;
Abel.Degree SHA256
8a149f0184b661f117d0e8c9e6a3a1dff009db6f86559fa9ca0668bcf70283e0.
Application K2-018#prop:k2018-arithmetic-characters, mathematical revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982; engineering basis
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
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open AlgebraicGeometry.Scheme.Hom RelativePicard
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : AlgebraicGeometry.Scheme.Modules.Invertible.ModuleTensorPullback.{u})
variable (hrep : DegreeZeroPicardRepresentability hnormal hcomp hreg hclosed hdim hprod htensor)
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)
variable (hcartier : FiniteCartierIdealDegree.{u})
variable (hdivisor : SmoothRelativeDivisorIdeal.{u}) (hbase : RelativeCartierIdealBaseChange.{u})
variable (o : Base F ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

@[simp] theorem degreeZeroAbelClass_origin (T : FScheme F) :
    degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX hcartier hdivisor hbase
      o ho
      T (originPoint X.hom o ho T) = 0 := by
  letI := hX.smooth
  letI := hX.proper
  apply Subtype.ext
  exact normalizedAbelClass_origin hdivisor htensor X.hom o ho T

/-- The morphism corresponding to the degree-zero Abel class of the identity section under the
supplied Picard representation. -/
def abelMorphism : X ⟶ representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX
  o ho :=
  (representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o
    ho).homEquiv.symm
    (Multiplicative.ofAdd (degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho X (𝟙 X)))

theorem abelMorphism_all_tests (T : FScheme F) (s : T ⟶ X) :
    (representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho).homEquiv
      (s ≫ abelMorphism hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX hcartier hdivisor
        hbase o ho) =
    Multiplicative.ofAdd (degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho T s) := by
  rw [Functor.RepresentableBy.homEquiv_comp]
  change degreeZeroMap hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho s
    (((representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o
      ho).homEquiv
      ((representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o
        ho).homEquiv.symm
        (Multiplicative.ofAdd (degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X
          hX
          hcartier hdivisor hbase o ho X (𝟙 X))))).toAdd) =
    degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX hcartier hdivisor hbase
      o ho T s
  rw [Equiv.apply_symm_apply, toAdd_ofAdd]
  have h := congrArg (fun k ↦ k (ULift.up (𝟙 X)))
    ((degreeZeroAbelTransformation hnormal hcomp hreg hclosed hdim hprod htensor X hX
      hcartier hdivisor hbase o ho).naturality s.op)
  change degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX hcartier hdivisor
    hbase o ho
      T (s ≫ 𝟙 X) =
    degreeZeroMap hnormal hcomp hreg hclosed hdim hprod htensor X hX o ho s
      (degreeZeroAbelClass hnormal hcomp hreg hclosed hdim hprod htensor X hX hcartier hdivisor
        hbase o ho X (𝟙 X)) at h
  simpa only [Category.comp_id] using h.symm

theorem abelMorphism_origin :
    letI := representingCommGroup hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho
    originPoint X.hom o ho (𝟙_ (FScheme F)) ≫
      abelMorphism hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX hcartier hdivisor hbase
        o ho =
      η[(representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho)] := by
  letI := representingCommGroup hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o ho
  apply (representingEquivalence hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o
    ho).homEquiv.injective
  rw [abelMorphism_all_tests, degreeZeroAbelClass_origin, representing_identity_class]
  rfl
end AlgebraicGeometry.Scheme.OverField.Curve.Abel

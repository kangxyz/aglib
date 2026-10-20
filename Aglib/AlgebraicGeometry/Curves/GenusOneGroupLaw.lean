/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.Inverse
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ProperInputs
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Basic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# The actual pointed group law on a genus-one field curve

The general all-genus degree-zero Picard functor is represented by an actual
locally Noetherian scheme, whose commutative group object is derived by Yoneda. The independently
constructed Abel morphism is proved a scheme isomorphism using actual relative
evaluation divisors and the two scheme inverse identities. Transporting the
group through that isomorphism gives a genuine group law on the original
curve. The previously proved Abel origin-zero formula identifies its identity
with the specified rational origin.

This works over every field, with no characteristic or prime-to-degree
restriction. The general input families are the explicitly named
incoming curve, divisor-degree, cohomology, relative Cartier and Picard
representation families. No group law, Abel inverse or target application
is a premise. The optional finite-locally-free geometric IsIso family and
B4 differential/canonical-degree layer are not inputs.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen  SmoothClosedPointDimension
    SmoothFieldDimension SmoothFieldNormality SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (NoetherianSheafCohomologyVanishing
    ProperStructureCohomologyBaseChange)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField (PointedGroupLaw)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
open Picard AlgebraicGeometry.Scheme.Hom RelativePicard
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u}) (hcartier : Abel.FiniteCartierIdealDegree.{u})
variable (hbase : RelativeCartierIdealBaseChange.{u}) (hdivisor : SmoothRelativeDivisorIdeal.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hgenus : ProperStructureCohomologyBaseChange.{u})
variable (hrr : LineBundleRiemannRoch.{u}) (hvanish : LineBundleHighDegreeVanishing.{u})
variable (hhigher : NoetherianSheafCohomologyVanishing.{u})
variable (hregular : FibrewiseRegularLineBundle.{u}) (hlocal : SmoothRelativeCartierLocality.{u})
variable (hrep : DegreeZeroPicardRepresentability hnormal hcomp hreg hclosed hdim hprod htensor)
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)
variable (hg : coherentGenus F X = 1) (o : 𝟙_ (FScheme F) ⟶ X)

/-- Actual genus-one group structure, transported through the independently proved Abel
isomorphism. -/
def genusOnePointedGroupLaw : PointedGroupLaw X o := by
  letI := hX.smooth
  letI := hX.proper
  let ho : o.left ≫ X.hom = 𝟙 (Base F) := Over.w o
  let e := Abel.abelSchemeIso hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
    hnorm hgenus hrr hvanish hhigher hregular hlocal hrep X hX o.left ho hg
  letI := representingCommGroup hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o.left ho
  refine ⟨GrpObj.ofIso e.symm, ?_⟩
  change η[representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o.left ho] ≫
    e.inv = o
  have hp : Abel.originPoint X.hom o.left ho (𝟙_ (FScheme F)) = o := by
    apply Over.OverMorphism.ext
    change (𝟙 (Base F)) ≫ o.left = o.left
    exact Category.id_comp _
  have he := Abel.abelMorphism_origin hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX
    hcartier hdivisor hbase o.left ho
  change Abel.originPoint X.hom o.left ho (𝟙_ (FScheme F)) ≫ e.hom =
    η[representingScheme hnormal hcomp hreg hclosed hdim hprod htensor hrep X hX o.left ho] at he
  rw [hp] at he
  rw [← he, Category.assoc, e.hom_inv_id]
  exact Category.comp_id o

include hnormal hcomp hreg hclosed hdim hprod htensor hcartier hbase hdivisor
  hnorm hgenus hrr hvanish hhigher hregular hlocal hrep hX hg in
theorem genusOneGroupLaw : Nonempty (PointedGroupLaw X o) :=
  ⟨genusOnePointedGroupLaw (hnormal := hnormal) (hcomp := hcomp) (hreg := hreg)
    (hclosed := hclosed) (hdim := hdim) (hprod := hprod) (htensor := htensor)
    (hcartier := hcartier) (hbase := hbase) (hdivisor := hdivisor) (hnorm := hnorm)
    (hgenus := hgenus) (hrr := hrr) (hvanish := hvanish) (hhigher := hhigher)
    (hregular := hregular) (hlocal := hlocal) (hrep := hrep) (X := X) (hX := hX)
    (hg := hg) (o := o)⟩
end AlgebraicGeometry.Scheme.OverField.Curve

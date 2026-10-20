/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.FinitePresentation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Basic
public import Aglib.AlgebraicGeometry.Curves.Genus
public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Riemann–Roch and high-degree vanishing for actual line bundles

All cohomology groups and scalar actions are the constructed module sheaf
cohomology. Degree is C's actual residue-weighted divisor degree transferred
through its proved O(D) equivalence, not a supplied numerical function.

LineBundleRiemannRoch retains the reconciliation of that degree with Euler
degree. Stacks 0AYR (33.44.1) is the Euler-degree definition, not a standalone
proof of this formula; 0AZ3 (42.41.3) reconciles it with zero-cycle degree.
The retained reconciliation includes the local ideal/dual identification,
DVR order = quotient length, the residue-weighted length sum (02M0), actual
H0(constants) = the field, and higher cohomology vanishing in dimension ≤ 1.
These dependencies are not claimed to be previously proved C lemmas.

LineBundleHighDegreeVanishing is Stacks 0B90 (33.44.17), over an algebraically
closed field and for all genera and all actual line bundles. The genus-one,
degree-one conclusion h0 = 1 and H1 = 0 is proved below, not retained as an
assumption. Its algebraically closed field is a geometric fibre field; it
places no algebraic-closure restriction on the original curve's base field.
Source statements and visible corrections inspected 2026-10-09.
This file does not import the differential or Riemann–Hurwitz layer.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen  SmoothClosedPointDimension
    SmoothFieldDimension SmoothFieldNormality SmoothFieldRegularity constants)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (finitePresentation_of_finite_local_basis moduleCohomology)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

/-!
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
This module is a new reusable curve foundation for that application.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
open Divisors

/-- The line-bundle Riemann–Roch formula input for proper integral Noetherian curves with the
displayed valuation, dimension, product-formula, and constant-field hypotheses. -/
def LineBundleRiemannRoch : Prop :=
  ∀ (K : Type u) [Field K] (X : FScheme K) [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X.left X.hom) (L : Invertible.LineBundle X.left),
    IsProper X.hom → Function.Bijective (constants X) →
      (Module.finrank K (moduleCohomology K X L.val 0) : ℤ) -
        (Module.finrank K (moduleCohomology K X L.val 1) : ℤ) =
      Picard.Degree.lineBundleDegree X.left X.hom hdim hprod L + 1 - (coherentGenus K X : ℤ)

/-- The vanishing input for first line-bundle cohomology in degree at least `2g - 1` on proper
integral curves over an algebraically closed field, under the displayed valuation and dimension
hypotheses. -/
def LineBundleHighDegreeVanishing : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X : FScheme K) [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left = 1)
    (hprod : Picard.Degree.PrincipalProductFormula X.left X.hom) (L : Invertible.LineBundle X.left),
    IsProper X.hom → 2 * (coherentGenus K X : ℤ) - 1 ≤
      Picard.Degree.lineBundleDegree X.left X.hom (le_of_eq hdim) hprod L →
      Subsingleton (moduleCohomology K X L.val 1)

/-- Finiteness of actual line-bundle cohomology in every degree, from
`properModuleCohomologyFinite` in `Aglib.AlgebraicGeometry.Cohomology.Proper.Field`
at Aglib revision 197ca0728db3cdf1552a6bcefeeda901e3377862, using the original
structural field action and the line bundle's proved finite presentation. -/
theorem lineBundleCohomology_finite {K : Type u} [Field K]
    (X : FScheme K) (hX : IsProper X.hom)
    (L : Invertible.LineBundle X.left) (n : ℕ) : Module.Finite K (moduleCohomology K X L.val n) :=
  Scheme.Cohomology.properModuleCohomologyFinite
    K X L.val n hX (Invertible.lineBundle_isFinitePresentation X.left L)

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hrr : LineBundleRiemannRoch.{u}) (hvanish : LineBundleHighDegreeVanishing.{u})
variable {K : Type u} [Field K] (X : FScheme K) (hX : Properties X)

include hrr in
theorem curveLineBundle_riemannRoch (L : Invertible.LineBundle X.left) :
    (Module.finrank K (moduleCohomology K X L.val 0) : ℤ) -
      (Module.finrank K (moduleCohomology K X L.val 1) : ℤ) =
    curveDegree hnormal hcomp hreg hclosed hdim hprod X hX (Invertible.classOf X.left L) +
      1 - (coherentGenus K X : ℤ) := by
  letI := curveProperties_isIntegral hnormal hcomp hX
  letI := curveProperties_isNoetherian hX
  letI (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hX x.val x.property
  letI := hX.proper
  exact hrr K X (le_of_eq (curveProperties_dimension hdim hX))
    (hprod K X.left X.hom (curveProperties_dimension hdim hX)) L hX.proper
    (@_root_.AlgebraicGeometry.Scheme.constants_bijective_of_proper_geometricallyIntegral K _ X
      hX.proper (curveProperties_geometricallyIntegral hnormal hcomp hX))

include hvanish in
theorem curveLineBundle_highDegree_vanishing [IsAlgClosed K] (L : Invertible.LineBundle X.left)
    (hL : 2 * (coherentGenus K X : ℤ) - 1 ≤
      curveDegree hnormal hcomp hreg hclosed hdim hprod X hX (Invertible.classOf X.left L)) :
    Subsingleton (moduleCohomology K X L.val 1) := by
  letI := curveProperties_isIntegral hnormal hcomp hX
  letI := curveProperties_isNoetherian hX
  letI (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hX x.val x.property
  letI := hX.proper
  exact hvanish K X (curveProperties_dimension hdim hX)
    (hprod K X.left X.hom (curveProperties_dimension hdim hX)) L hX.proper hL

include hrr hvanish in
theorem genusOne_degreeOne_cohomology [IsAlgClosed K] (L : Invertible.LineBundle X.left)
    (hg : coherentGenus K X = 1)
    (hL : curveDegree hnormal hcomp hreg hclosed hdim hprod X hX (Invertible.classOf X.left L) =
      1) :
    Module.finrank K (moduleCohomology K X L.val 0) = 1 ∧
      Subsingleton (moduleCohomology K X L.val 1) := by
  have hz := curveLineBundle_highDegree_vanishing hnormal hcomp hreg hclosed hdim hprod hvanish X
    hX L
    (by rw [hg, hL]; norm_num)
  letI := hz
  refine ⟨?_, hz⟩
  have he := curveLineBundle_riemannRoch hnormal hcomp hreg hclosed hdim hprod hrr X hX L
  have hzdim : Module.finrank K (moduleCohomology K X L.val 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hL, hg, hzdim] at he
  omega
end AlgebraicGeometry.Scheme.OverField.Curve

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Modules.Differentials.Basic
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.Modules.Differentials.SmoothRank
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Curves.Genus
public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.FunctionField
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ProperInputs
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# The actual canonical bundle and unramified Riemann–Hurwitz

The underlying sheaf is the constructed universal Kähler differential sheaf,
not a supplied invertible sheaf. Smooth relative dimension one gives its actual
local singleton bases. The étale canonical comparison is the constructed
map that sends d(a) to d(f# a).

The actual line-bundle degree and canonical-degree/genus application are
constructed below. Finite-map pullback scaling is derived from C's actual
Picard degree theorem and the B2 rank/function-field comparison. The final
unramified Riemann–Hurwitz formula uses the independently constructed étale
differential isomorphism. No Riemann–Hurwitz formula is assumed. Native
smooth-rank and étale-pullback theorems supply the differential properties
(Stacks 02G1/02G2 and 04BX).

Accepted incoming C object interface: `Picard.Basic`, SHA256
b9570475203f86c9d1622f5762bd14b0df6e3c785ac24219fa37c0b9e0581b04.
Application K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
source e73d98b1b5c1e5abcdebf7d058e436d792b87982; frozen engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen  SmoothClosedPointDimension
    SmoothFieldDimension SmoothFieldNormality SmoothFieldRegularity constants)
open AlgebraicGeometry.Scheme.Modules.Differentials
  (  differentialPullbackMap differentialSheaf
    etaleDifferentialIso)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/


@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
variable {F : Type u} [Field F]

theorem differentialSheaf_isLocallyRankOne
     (X : FScheme F)
    (hX : SmoothOfRelativeDimension 1 X.hom) :
    Invertible.IsLocallyRankOne X.left (differentialSheaf X) := by
  obtain ⟨q, hq, hn⟩ := Scheme.Modules.Differentials.differentialSheaf_hasRank_of_smooth F X 1 hX
  refine ⟨q, hq, ?_⟩
  intro i
  exact ⟨(hn i).some.trans (Equiv.ofUnique (Fin 1) PUnit.{u + 1})⟩

def canonicalLineBundle
    (X : FScheme F) (hX : SmoothOfRelativeDimension 1 X.hom) :
    Invertible.LineBundle X.left :=
  ⟨differentialSheaf X, differentialSheaf_isLocallyRankOne X hX⟩

@[simp] theorem canonicalLineBundle_val
    (X : FScheme F) (hX : SmoothOfRelativeDimension 1 X.hom) :
    (canonicalLineBundle X hX).val = differentialSheaf X := rfl

def canonicalLineBundleClass
    (X : FScheme F) (hX : SmoothOfRelativeDimension 1 X.hom) :
    Invertible.LineBundleClass X.left :=
  Quotient.mk (Invertible.lineBundleSetoid X.left) (canonicalLineBundle X hX)

def canonicalEtaleIso
    {X Y : FScheme F} (f : X ⟶ Y) [Etale f.left] :
    ((Scheme.Modules.pullback f.left).obj (differentialSheaf Y) :
      SheafOfModules.{u} X.left.ringCatSheaf) ≅ differentialSheaf X := by
  let e := etaleDifferentialIso f
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

@[simp] theorem canonicalEtaleIso_hom
    {X Y : FScheme F} (f : X ⟶ Y) [Etale f.left] :
    (canonicalEtaleIso f).hom = differentialPullbackMap f := rfl

theorem pullbackCanonical_isLocallyRankOne
    {X Y : FScheme F} (f : X ⟶ Y) [Etale f.left]
    (hX : SmoothOfRelativeDimension 1 X.hom) :
    Invertible.IsLocallyRankOne X.left
      ((Scheme.Modules.pullback f.left).obj (differentialSheaf Y)) :=
  Invertible.isLocallyRankOne_of_iso X.left (canonicalEtaleIso f).symm
    (differentialSheaf_isLocallyRankOne X hX)
end AlgebraicGeometry.Scheme.OverField.Curve


/-!
The following standard boundary is the all-field canonical-degree theorem
0C1A (53.8.4), combined with the degree reconciliation in 0AZ3 (42.41.3).
The latter identifies Euler degree with the residue-weighted zero-cycle degree:
for an effective Cartier ideal locally generated by t, its dual has positive
divisor coefficient ord(t)=length(O/(t)), and 02M0 sums the residue-weighted
local lengths. The local ideal/divisor identification, length/order equality,
and Euler/residue-degree reconciliation are retained dependencies of this
single derived-corollary family; they are not claimed as proved C lemmas.
The precise sources 0C1A, 0AZ3, 02M0 and 01WX and their visible absence of
correction comments were inspected 2026-10-09. The family uses the already
constructed universal differential sheaf, actual coherent H1 genus and C's
actual O(D)-transferred degree. It is not a supplied canonical bundle or RH
formula. Curve integrality, dimension, DVR, properness and constants hypotheses
are discharged in curveDegree_canonical.

Incoming Picard.DivisorInverse SHA256
e5d590b08653fa393d5657a7bf3dece2482b543867c27b33db2b6a6e70187a27.
-/
set_option linter.style.haveILetI false
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
open Divisors

def SmoothCanonicalDegree : Prop :=
  ∀ (F : Type u) [Field F] (X : FScheme F) [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X.left X.hom)
    (hsmooth : SmoothOfRelativeDimension 1 X.hom) ,
    IsProper X.hom → Function.Bijective (constants X) →
      Picard.Degree.lineBundleDegree X.left X.hom hdim hprod (canonicalLineBundle X hsmooth) =
        2 * (coherentGenus F X : ℤ) - 2

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)


theorem curveDegree_canonical (hcanonical : SmoothCanonicalDegree.{u})
      :
    curveDegree hnormal hcomp hreg hclosed hdim hprod X hX
      (Invertible.classOf X.left (canonicalLineBundle X hX.smooth)) =
        2 * (coherentGenus F X : ℤ) - 2 := by
  letI := curveProperties_isIntegral hnormal hcomp hX
  letI := curveProperties_isNoetherian hX
  letI (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hX x.val x.property
  letI := hX.proper
  exact hcanonical F X (le_of_eq (curveProperties_dimension hdim hX))
    (hprod F X.left X.hom (curveProperties_dimension hdim hX)) hX.smooth hX.proper
    (@_root_.AlgebraicGeometry.Scheme.constants_bijective_of_proper_geometricallyIntegral F _ X
      hX.proper (curveProperties_geometricallyIntegral hnormal hcomp hX))

end AlgebraicGeometry.Scheme.OverField.Curve

/-!
The numerical pullback bridge consumes Picard.NormDegree, SHA256
0e7159fc9acf3656433a7a4f1786c6d76832bd7f286888bb4f33e56543e74a37,
and its explicitly retained all-fibre finite-morphism norm/order corollary
(Stacks 02MJ). Its actual field degree is identified with locally free rank
by Degree.FunctionField. Both the rank-scaled degree formula and the final
unramified formula are proved applications. This layer does not depend on
the tensor-pullback family, Riemann–Roch, Picard representability or Abel.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
open Divisors
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hbase : Scheme.Modules.AffineModuleBaseChange.{u})
variable (hgen : AlgebraicGeometry.Scheme.Hom.FiniteFlat.FiniteDominantGenericFibre.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable {F : Type u} [Field F] {X Y : FScheme F}

include hbase hgen hnorm in
theorem curveDegree_pullback_of_hasLocallyFreeRank
    (f : X ⟶ Y) (hX : Properties X) (hY : Properties Y)
    [IsFinite f.left] [IsDominant f.left] (n : ℕ) (hf : HasLocallyFreeRank f.left n)
    (a : Invertible.PicardGroup Y.left) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod X hX (Invertible.pullbackClass f.left a) =
      (n : ℤ) * curveDegree hnormal hcomp hreg hclosed hdim hprod Y hY a := by
  letI := curveProperties_isIntegral hnormal hcomp hX
  letI := curveProperties_isIntegral hnormal hcomp hY
  letI := curveProperties_isNoetherian hX
  letI := curveProperties_isNoetherian hY
  letI (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hX x.val x.property
  letI (y : ClosedPoint Y.left) : IsDiscreteValuationRing (Y.left.presheaf.stalk y.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hY y.val y.property
  letI := hX.proper
  letI := hY.proper
  have hfin := AlgebraicGeometry.Scheme.Hom.FiniteFlat.functionField_finite f.left hbase hgen
    hf.finiteLocallyFree
  have hdeg : AlgebraicGeometry.Scheme.Hom.fieldDegree f.left = n :=
    AlgebraicGeometry.Scheme.Hom.FiniteFlat.functionFieldDegree_eq_of_hasLocallyFreeRank f.left
      hbase hgen n hf
  have h := Picard.NormDegree.picardDegree_pullback f.left Y.hom hnorm
    (le_of_eq (curveProperties_dimension hdim hX)) (le_of_eq (curveProperties_dimension hdim hY))
      hfin
    (hprod F X.left (f.left ≫ Y.hom) (curveProperties_dimension hdim hX))
    (hprod F Y.left Y.hom (curveProperties_dimension hdim hY)) a
  simpa only [curveDegree, Over.w f, hdeg] using h

variable (hfree : FiniteFlatPresentationLocallyFree.{u})
variable (hcanonical : SmoothCanonicalDegree.{u})
include hnormal hcomp hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical in
theorem unramifiedRiemannHurwitz (f : X ⟶ Y) (n : ℕ)
    (hX : Properties X) (hY : Properties Y)
    (hfinite : IsFinite f.left) (he : Etale f.left) (hs : Surjective f.left)
    (hn : HasGeometricDegree f n) :
    2 * (coherentGenus F X : ℤ) - 2 = (n : ℤ) * (2 * (coherentGenus F Y : ℤ) - 2) := by
  letI := hfinite
  letI := he
  letI := hs
  have hf := (hasLocallyFreeRank_iff_hasGeometricDegree hfree hbase f n).mpr hn
  have hcan : Invertible.pullbackClass f.left (Invertible.classOf Y.left (canonicalLineBundle Y
    hY.smooth)) =
      Invertible.classOf X.left (canonicalLineBundle X hX.smooth) := by
    apply Quotient.sound
    exact ⟨canonicalEtaleIso f⟩
  rw [← curveDegree_canonical hnormal hcomp hreg hclosed hdim hprod X hX hcanonical ,
    ← curveDegree_canonical hnormal hcomp hreg hclosed hdim hprod Y hY hcanonical ,
    ← hcan]
  exact curveDegree_pullback_of_hasLocallyFreeRank hnormal hcomp hreg hclosed hdim hprod
    hbase hgen hnorm f hX hY n hf _
end AlgebraicGeometry.Scheme.OverField.Curve

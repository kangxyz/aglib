/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.LineBundleEvaluation
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFaithful
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Regular
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Curves.RiemannRoch
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ProperInputs
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# Actual relative evaluation for degree-one line bundles

The genus-one, degree-one geometric-fibre profile is proved from the general
all-genus Riemann–Roch and high-degree vanishing families, together with the
all-Noetherian-scheme Zariski cohomological dimension theorem. No genus-one
cohomology profile is retained as a background assumption.

The cohomology theorem over a locally Noetherian original base is applied to the actual module
sheaf pushforward. Its local bases produce a genuine rank-one line bundle.
The evaluation contraction is literally the tensor of the actual adjunction
counit with the identity of the actual dual bundle, followed by actual dual
evaluation. Its source has class f*P - L, the sign for the negative zero divisor.

The evaluation construction uses a locally Noetherian original base,
including nonreduced bases, while its canonical comparison permits every
new target. The canonical base-change square and tensor faithfulness
prove that the contraction is regular on every integral geometric fibre.
No section, graph, or Abel inverse is asserted at this stage. All fibre curve, genus and degree
hypotheses are explicit application conditions to be discharged later.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen  SmoothClosedPointDimension
    SmoothFieldDimension SmoothFieldNormality SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (FibreCohomologyConcentrated NoetherianSheafCohomologyVanishing
    evaluation_pullback_ne_zero moduleAddSheaf moduleCohomology moduleH0Equiv relativeEvaluation)
open AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle classOf dualEvaluationIso dualLineBundle lineBundle_isLocallyFree
    pullbackLineBundle tensorLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_naturality tensorSheafMap)
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
open AlgebraicGeometry.Scheme.Cohomology
  (evaluationIdealLineBundle evaluationContraction evaluationContraction_pullback_ne_zero)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open Picard
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hrr : LineBundleRiemannRoch.{u}) (hvanish : LineBundleHighDegreeVanishing.{u})
variable (hhigher : NoetherianSheafCohomologyVanishing.{u})
variable {K : Type u} [Field K] [IsAlgClosed K] (X : FScheme K) (hX : Properties X)
include hrr hvanish hhigher in
theorem genusOne_degreeOne_all_cohomology (L : LineBundle X.left)
    (hg : coherentGenus K X = 1)
    (hL : curveDegree hnormal hcomp hreg hclosed hdim hprod X hX (classOf X.left L) = 1) :
    Module.finrank K (moduleCohomology K X L.val 0) = 1 ∧
      ∀ n : ℕ, 0 < n → Subsingleton (moduleCohomology K X L.val n) := by
  have h := genusOne_degreeOne_cohomology hnormal hcomp hreg hclosed hdim hprod
    hrr hvanish X hX L hg hL
  refine ⟨h.1, fun n hn ↦ ?_⟩
  by_cases he : n = 1
  · subst n; exact h.2
  · letI := curveProperties_isNoetherian hX
    exact hhigher X.left (moduleAddSheaf X.left L.val) 1 n
      (le_of_eq (curveProperties_dimension hdim hX)) (by omega)

variable {Z S : Scheme.{u}} (f : Z ⟶ S)
include hrr hvanish hhigher in
theorem degreeOneFamily_cohomology (L : LineBundle Z)
    (hcurves : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      Properties (Over.mk (pullback.snd f t)))
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      coherentGenus K (Over.mk (pullback.snd f t)) = 1)
    (hdegree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      curveDegree hnormal hcomp hreg hclosed hdim hprod
        (Over.mk (pullback.snd f t)) (hcurves K t)
        (classOf _ (pullbackLineBundle (pullback.fst f t) L)) = 1) :
    FibreCohomologyConcentrated f L.val 1 := by
  intro K _ _ t
  exact genusOne_degreeOne_all_cohomology hnormal hcomp hreg hclosed hdim hprod
    hrr hvanish hhigher (Over.mk (pullback.snd f t)) (hcurves K t)
    (pullbackLineBundle (pullback.fst f t) L) (hg K t) (hdegree K t)

end AlgebraicGeometry.Scheme.OverField.Curve.Abel

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open Picard AlgebraicGeometry.Scheme.Hom
variable {Z S : Scheme.{u}} (f : Z ⟶ S)
variable [IsLocallyNoetherian S]
variable [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
variable (L : LineBundle Z) (hL : FibreCohomologyConcentrated f L.val 1)
theorem evaluationContraction_geometric_regular
    (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
    (hcurves : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      Properties (Over.mk (pullback.snd f t))) :
    GeometricFibreRegular f (evaluationIdealLineBundle f L hL)
      (evaluationContraction f L hL) := by
  intro K _ _ t
  letI : IsIntegral (pullback f t) := curveProperties_isIntegral hnormal hcomp (hcurves K t)
  apply nonzero_lineBundleMap_mono
  intro he
  apply evaluationContraction_pullback_ne_zero f L hL K t
  apply (cancel_mono (pullbackUnitIso (pullback.fst f t)).hom).mp
  exact he.trans (zero_comp).symm
end AlgebraicGeometry.Scheme.OverField.Curve.Abel

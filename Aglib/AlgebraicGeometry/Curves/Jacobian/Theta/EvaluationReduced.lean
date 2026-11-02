/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EvaluationFibre
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.GeometricSimple
public import Aglib.AlgebraicGeometry.Curves.Abel.FiniteCartierReduced
public import Aglib.AlgebraicGeometry.Curves.Genus.BaseChange
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.QuasiCompactSeparated

/-!
# Reduced geometric fibres of the actual evaluation divisor

Riemann--Roch and actual structural genus base change compute degree g
for the original positive fibre bundle. Its h0=1 gives an effective
representative. The already constructed non-repeated open makes this
representative simple. The native coefficient/stalk-length calculation
then proves that the ORIGINAL finite Cartier fibre is reduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.Cohomology Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Picard Picard.DivisorClass Picard.Degree

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original evaluation fibre over an algebraically closed field
is reduced, including the genus-one case. -/
theorem isReduced_thetaEvaluationFibre (hg : 0 < coherentGenus k X)
    {K : Type u} [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ Spec (.of k))
    (a : Over.mk b ⟶ thetaParameterOver hX o ho P R) :
    IsReduced (pullback (zeroInclusion (thetaEvaluationContraction hX o ho P R))
      ((familyScheme X.hom).map a)) := by
  let := picardCommGrpObj X.hom P R
  let Y : FScheme K := Over.mk (pullback.snd X.hom b)
  let hY := curveProperties_baseChange hX K b
  let := hY.proper
  let := hY.smooth
  let := PointDivisor.isIntegral_of_properties Y hY
  let := curveProperties_isNoetherian hY
  let (x : ClosedPoint Y.left) := PointDivisor.isDiscreteValuationRing_stalk Y hY x
  let hd := hY.topologicalKrullDim_eq_one
  let L := thetaEvaluationFibrePositiveLineBundle hX o ho P R b a
  let i := pullback.snd (zeroInclusion (thetaEvaluationContraction hX o ho P R))
    ((familyScheme X.hom).map a)
  let hD := thetaEvaluationFibre_isRelativeEffectiveCartier hX o ho P R b a
  have : IsClosedImmersion i := hD.isClosedImmersion
  have : IsFinite (i ≫ Y.hom) := thetaEvaluationFibre_finite hX o ho P R b a
  have h0 := thetaEvaluationFibre_h0 hX o ho P R b a
  have h1 := thetaEvaluationFibre_h1 hX o ho P R b a
  have hgen := coherentGenus_arbitraryBaseChange properStructureCohomologyBaseChange X hX K b
  have hrr := lineBundleRiemannRoch K Y hd.le
    (properCurveProductFormula K Y.left Y.hom hd) L inferInstance
    (constants_bijective_of_proper_of_isAlgClosed Y)
  have hdeg : lineBundleDegree Y.left Y.hom hd.le
      (properCurveProductFormula K Y.left Y.hom hd) L = (coherentGenus k X : ℤ) := by
    change (Module.finrank K (moduleCohomology K Y L.val 0) : ℤ) -
      Module.finrank K (moduleCohomology K Y L.val 1) =
        lineBundleDegree Y.left Y.hom hd.le
          (properCurveProductFormula K Y.left Y.hom hd) L + 1 - (coherentGenus K Y : ℤ) at hrr
    rw [h0, h1, hgen] at hrr
    omega
  have : Nontrivial (moduleCohomology K Y L.val 0) := Module.nontrivial_of_finrank_eq_succ h0
  obtain ⟨s, hs⟩ := exists_ne (0 : moduleCohomology K Y L.val 0)
  have hs' : moduleH0Equiv Y L.val s ≠ 0 := fun hz =>
    hs ((moduleH0Equiv Y L.val).injective (hz.trans (moduleH0Equiv Y L.val).map_zero.symm))
  obtain ⟨D, heff, hclass⟩ := exists_effective_divisor_class_of_nonzero_section
    Y.left hd.le L (moduleH0Equiv Y L.val s) hs'
  have hDdegree : degDiv Y.left Y.hom D = (coherentGenus k X : ℤ) := by
    rw [← picardDegree_divisor Y.left Y.hom hd.le
      (properCurveProductFormula K Y.left Y.hom hd)]
    exact (congrArg (picardDegree Y.left Y.hom hd.le
      (properCurveProductFormula K Y.left Y.hom hd)) hclass).trans hdeg
  have ha : (a ≫ thetaParameterι hX o ho P R).left (IsLocalRing.closedPoint K) ∈
      rankOneNonRepeatedOpen hX o ho P R := (a.left (IsLocalRing.closedPoint K)).property
  have huniv : classOf _ (RigidifiedPair.map (a ≫ thetaParameterι hX o ho P R)
      (degreeUniversalPair hX o ho P R (coherentGenus k X))).bundle =
      divisorToPicard Y.left hd.le D :=
    (thetaEvaluationFibre_degreeUniversalClass hX o ho P R b a).symm.trans hclass.symm
  have hsimple := effective_divisor_simple_of_mem_rankOneNonRepeatedOpen
    hX o ho P R hg b D heff hDdegree (a ≫ thetaParameterι hX o ho P R) ha huniv
  exact Abel.isReduced_of_positive_class_simple_of_h0_one Y i hD.isLocallyRankOne
    hd.le D heff hsimple hclass h0

end AlgebraicGeometry.Scheme.OverField.Curve

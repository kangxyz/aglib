/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ExceptionalHilbert
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.AnticanonicalHilbert.BaseChange

/-!
# Exceptional Hilbert numerics from the actual first power

Cotangent rank three gives three sections of the original positive exceptional
line through the original power-section equivalence. Rationality supplies the
unit cohomology and closed-stalk CM parameters. An actual finite hyperplane
after algebraic closure and ordinary line-power base change give every
original graded rank. No inverse-line or canonical cohomology is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Cohomology
open IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

variable (A : Type u) [CommRing A] [IsLocalRing A]
  [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

local instance exceptionalFirstPowerResidueField : Field (A ⧸ maximalIdeal A) :=
  Ideal.Quotient.field (maximalIdeal A)

local instance exceptionalFirstPowerComponentModule (r : ℕ) :
    Module (ResidueField A) (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r) :=
  Submodule.module (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r)

/-- A rational normal local surface with actual cotangent rank three has
all original graded ranks `2 * r + 1`. No Gorenstein or canonical-line input
is needed after the first-power rank is genuinely known. -/
theorem exceptional_hilbert_of_cotangent_finrank_three (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (hcot : Module.finrank (ResidueField A) (CotangentSpace A) = 3) (r : ℕ) :
    Module.finrank (ResidueField A)
      (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r) = 2 * r + 1 := by
  let k := A ⧸ maximalIdeal A
  let E := exceptionalCurve A hd
  let X := Over.mk (exceptionalStructureMap A hd)
  obtain ⟨d, j, _, hjclosed, hj, ⟨eL⟩⟩ := exists_exceptionalTautologicalEmbedding A hd
  let := hjclosed
  let ι := ULift.{u} (Fin (d + 1))
  let Y := Over.mk (j ≫ ProjectiveSpace.toSpec k ι)
  have hj' : j ≫ ProjectiveSpace.toSpec k ι = exceptionalStructureMap A hd := hj
  let L := curveHyperplaneLine k ι j
  have hRank (M : E.Modules) (q : ℕ) :
      Module.finrank k (moduleCohomology k Y M q) =
        Module.finrank k (moduleCohomology k X M q) :=
    congrArg (fun f : E ⟶ Spec (.of k) =>
      Module.finrank k (moduleCohomology k (Over.mk f) M q)) hj'
  let : Subsingleton (moduleCohomology k Y (SheafOfModules.unit E.ringCatSheaf) 1) := by
    dsimp only [Y]
    rw [hj']
    exact exceptionalUnit_h1_subsingleton A hd hA hRat
  have hO : Module.finrank k (moduleCohomology k Y
      (SheafOfModules.unit E.ringCatSheaf) 0) = 1 :=
    (hRank _ 0).trans (exceptionalUnit_h0_finrank A hd hA hRat)
  let eOne : exceptionalPower A hd 1 ≅ (exceptionalLine A hd).val :=
    exceptionalPowerTensorIso A hd 1 ≪≫
      tensorSheafIso E (Iso.refl _) (PowerPullback.freeUnitIso E) ≪≫
        (SheafOfModulesOfCommRing.tensorRightUnitIso E.sheaf).app _
  let eSections : exceptionalPowerLayer A 1 ≃ₗ[k]
      moduleCohomology k X L.val 0 :=
    ((exceptionalPowerTheta A hd hA hRat 1).trans
      (moduleH0Equiv X (exceptionalPower A hd 1)).symm).trans
        (moduleCohomologyIso X (eOne ≪≫ eL.symm) 0)
  have hL : Module.finrank k (moduleCohomology k Y L.val 0) = 3 :=
    (hRank L.val 0).trans (eSections.finrank_eq.symm.trans
      ((exceptionalPowerOneCotangentEquiv A).finrank_eq.trans hcot))
  have h := cmCurve_hyperplanePower_h0_finrank_of_firstPower k ι j
    (exceptionalCurve_closedPoint_cmParameter A hd hA hRat) hO hL r
  have hP : Module.finrank k
      (moduleCohomology k X (tensorPowerLineBundle E L r).val 0) = 2 * r + 1 :=
    (hRank (tensorPowerLineBundle E L r).val 0).symm.trans h
  let eP : exceptionalPower A hd r ≅ (tensorPowerLineBundle E L r).val :=
    exceptionalPowerTensorIso A hd r ≪≫ (TrivializedPower.powerIso E eL r).symm
  exact ((exceptionalGradedCohomologyEquiv A hd hA hRat r).trans
    (moduleCohomologyIso X eP 0)).finrank_eq.trans hP

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

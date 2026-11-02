/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Exceptional.Geometry
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic

/-!
# First exceptional-line cohomology and the original cotangent space

The original power-section map in degree one identifies H0 of the positive
exceptional line with the native cotangent space over the original residue
field. Nonregularity in dimension two therefore gives at least three sections.
No canonical coefficient, Gorensteinness, chosen projective embedding, or
all-degree Hilbert function is needed. The full exceptional scheme is retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

variable (A : Type u) [CommRing A] [IsLocalRing A]
  [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

local instance exceptionalFirstPowerField : Field (A ⧸ maximalIdeal A) :=
  Ideal.Quotient.field (maximalIdeal A)

/-- H0 of the original positive exceptional line is the original cotangent
space, using the actual degree-one quotient-section map. -/
def exceptionalLineCohomologyCotangentEquiv (hd : ringKrullDim A = 2)
    (hNagata : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    letI := moduleCohomologyModule (Over.mk (exceptionalStructureMap A hd))
      (exceptionalLine A hd).val 0
    moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
      (exceptionalLine A hd).val 0 ≃ₗ[A ⧸ maximalIdeal A] CotangentSpace A := by
  let E := exceptionalCurve A hd
  let X := Over.mk (exceptionalStructureMap A hd)
  let : Module (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) X (exceptionalLine A hd).val 0) :=
    moduleCohomologyModule X (exceptionalLine A hd).val 0
  let eOne : exceptionalPower A hd 1 ≅ (exceptionalLine A hd).val :=
    exceptionalPowerTensorIso A hd 1 ≪≫
      tensorSheafIso E (Iso.refl _) (PowerPullback.freeUnitIso E) ≪≫
        (SheafOfModulesOfCommRing.tensorRightUnitIso E.sheaf).app _
  let e := ((exceptionalPowerTheta A hd hNagata hRat 1).trans
    (moduleH0Equiv X (exceptionalPower A hd 1)).symm).trans
      (moduleCohomologyIso X eOne 0)
  exact e.symm.trans (exceptionalPowerOneCotangentEquiv A)

/-- A nonregular rational local surface has at least three sections of its
original positive exceptional line, without a cotangent-rank-three premise. -/
theorem exceptionalLine_h0_finrank_ge_three_of_not_regular (hd : ringKrullDim A = 2)
    (hNagata : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (hsing : ¬ IsRegularLocalRing A) :
    letI := moduleCohomologyModule (Over.mk (exceptionalStructureMap A hd))
      (exceptionalLine A hd).val 0
    3 ≤ Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (exceptionalLine A hd).val 0) := by
  let : Module (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (exceptionalLine A hd).val 0) :=
    moduleCohomologyModule (Over.mk (exceptionalStructureMap A hd))
      (exceptionalLine A hd).val 0
  rw [(exceptionalLineCohomologyCotangentEquiv A hd hNagata hRat).finrank_eq]
  have hgt : 2 < (maximalIdeal A).spanFinrank := by
    by_contra h
    have hle : (maximalIdeal A).spanFinrank ≤ 2 := by omega
    apply hsing
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A
    rw [hd]
    exact_mod_cast hle
  have hcot : (maximalIdeal A).spanFinrank =
      Module.finrank (A ⧸ maximalIdeal A) (CotangentSpace A) :=
    spanFinrank_eq_finrank_quotient (maximalIdeal A)
      (maximalIdeal A).fg_of_isNoetherianRing
  rw [hcot] at hgt
  exact Nat.succ_le_of_lt hgt

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

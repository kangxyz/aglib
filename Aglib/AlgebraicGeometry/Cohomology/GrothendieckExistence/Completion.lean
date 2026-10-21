/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.QuotientComparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.QuotientTower

/-!
# Comparison with the original affine-base quotient tower

The single native coherent-adic category uses ideal-sheaf thickenings. This
comparison identifies its actual completion diagram with the original
ideal-power quotient diagram used in formal functions, preserving every
original reduction arrow. No second formal category is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : X.Modules) [F.IsQuasicoherent]

/-- Original coefficient powers agree with actual ideal-sheaf quotients. -/
def idealPowerQuotientIdealSheafIso (n : ℕ) :
    idealPowerQuotient X (idealThickeningBaseScalar f) F I n ≅
      (idealSheafQuotientFunctor X (idealThickeningIdealSheaf f I ^ n)).obj F :=
  idealQuotientThickeningIso f F (I ^ n) ≪≫
    closedImmersionQuotientIso (idealThickeningι f (I ^ n))
      (idealThickeningIdealSheaf f I ^ n).subschemeι (by
        rw [IdealSheafData.ker_subschemeι, idealThickeningι_ker,
          idealThickeningIdealSheaf_pow]) F

/-- The comparison retains the original quotient projection and geometric unit. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_idealSheafIso_hom (n : ℕ) :
    idealQuotientπ X (idealThickeningBaseScalar f) F (I ^ n) ≫
      (idealPowerQuotientIdealSheafIso f I F n).hom =
        (idealSheafQuotientUnit X (idealThickeningIdealSheaf f I ^ n)).app F := by
  simp [idealPowerQuotientIdealSheafIso, idealThickeningUnit]

/-- The actual ideal-sheaf completion tower is the original quotient tower. -/
def idealPowerQuotientIdealSheafTowerIso :
    idealPowerQuotientFunctor X (idealThickeningBaseScalar f) F I ≅
      idealSheafQuotientTower X (idealThickeningIdealSheaf f I) F :=
  NatIso.ofComponents (fun n => idealPowerQuotientIdealSheafIso f I F n.unop) (by
    intro m n g
    apply (cancel_epi (idealQuotientπ X (idealThickeningBaseScalar f) F
      (I ^ m.unop))).mp
    change idealQuotientπ X (idealThickeningBaseScalar f) F (I ^ m.unop) ≫
        idealPowerQuotientMap X (idealThickeningBaseScalar f) F I (leOfHom g.unop) ≫
        (idealPowerQuotientIdealSheafIso f I F n.unop).hom =
      idealQuotientπ X (idealThickeningBaseScalar f) F (I ^ m.unop) ≫
        (idealPowerQuotientIdealSheafIso f I F m.unop).hom ≫
        idealSheafQuotientMap X (idealThickeningIdealSheaf f I ^ m.unop)
          (idealSheaf_pow_le X (idealThickeningIdealSheaf f I) (leOfHom g.unop)) F
    simp)

/-- The tower comparison sends the original reduction to the native completion unit. -/
@[reassoc (attr := simp)]
theorem idealPowerQuotientReduction_idealSheafTowerIso_hom :
    idealPowerQuotientReduction X (idealThickeningBaseScalar f) F I ≫
      (idealPowerQuotientIdealSheafTowerIso f I F).hom =
        idealSheafQuotientTowerUnit X (idealThickeningIdealSheaf f I) F := by
  apply NatTrans.ext
  funext n
  exact idealQuotientπ_idealSheafIso_hom f I F n.unop

end AlgebraicGeometry.Scheme.Cohomology

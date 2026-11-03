/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Exceptional.Geometry
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.AnticanonicalHilbert
public import Aglib.RingTheory.AssociatedGraded.Components
public import Aglib.RingTheory.AssociatedGraded.NativeRing
public import Aglib.RingTheory.Blowup.QuadraticPresentation

/-!
# From the full exceptional curve to the original quadratic cone

The existing exceptional power-section map and the existing original Rees
component map identify the same ideal-power quotient. The resulting residue-
linear equivalence compares the original associated graded component with
actual H0 of the full exceptional scheme.

An actual finite Cartier divisor whose dual ideal is the exceptional line
then supplies the Hilbert function through the numerical Cartier theorem.
The two cohomology conditions on that ideal remain explicit: their canonical
source is not asserted here. The full quadratic kernel is obtained from its
existing unique algebraic implementation, not reproved.
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

/-- The field structure on the original maximal-ideal quotient. -/
local instance exceptionalHilbertResidueField : Field (A ⧸ maximalIdeal A) :=
  Ideal.Quotient.field (maximalIdeal A)

/-- The original residue-field action on a maximal-ideal associated-graded component. -/
local instance exceptionalHilbertComponentModule (r : ℕ) :
    Module (ResidueField A) (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r) :=
  Submodule.module (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r)

/-- The native quotient-power layer is the original homogeneous component,
over the original residue field. The equivalence uses the actual monomial
coefficient map of the original Rees algebra. -/
def exceptionalPowerLayerGradingEquiv (r : ℕ) :
    exceptionalPowerLayer A r ≃ₗ[A ⧸ maximalIdeal A]
      Ideal.associatedGradedQuotientGrading (maximalIdeal A) r := by
  let m := maximalIdeal A
  have hJ : m • (⊤ : Submodule A (m ^ r : Ideal A)) =
      m.associatedGradedComponentRelations r := by
    ext a
    change a ∈ m • (⊤ : Submodule A (m ^ r : Ideal A)) ↔ (a : A) ∈ m ^ (r + 1)
    simpa only [smul_eq_mul, pow_succ'] using
      (Submodule.mem_smul_top_iff (I := m) (m ^ r : Ideal A) a)
  let E : exceptionalPowerLayer A r ≃ₗ[A] m.associatedGradedGrading r :=
    (Submodule.quotEquivOfEq _ _ hJ).trans (m.associatedGradedComponentEquiv r)
  let f : exceptionalPowerLayer A r →ₗ[A]
      Ideal.associatedGradedQuotientGrading m r :=
    { toFun := E
      map_add' := E.map_add
      map_smul' := E.map_smul }
  exact LinearEquiv.ofBijective
    (f.extendScalarsOfSurjective Ideal.Quotient.mk_surjective) E.bijective

/-- The component comparison sends each original ideal-power class to its
literal Rees monomial class, without selecting a coefficient-field section. -/
theorem exceptionalPowerLayerGradingEquiv_class (r : ℕ)
    (a : ↥(maximalIdeal A ^ r)) :
    (exceptionalPowerLayerGradingEquiv A r (exceptionalPowerClass A r a) :
      (maximalIdeal A).associatedGraded) =
      Ideal.Quotient.mk (maximalIdeal A).associatedGradedIdeal
        (reesAlgebra.homogeneous (maximalIdeal A) r a) := rfl

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- Original associated graded components identify with actual exceptional
H0 through the same quotient sections and the original structural scalars. -/
def exceptionalGradedCohomologyEquiv (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) (r : ℕ) :
    Ideal.associatedGradedQuotientGrading (maximalIdeal A) r ≃ₗ[A ⧸ maximalIdeal A]
      moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (exceptionalPower A hd r) 0 :=
  (exceptionalPowerLayerGradingEquiv A r).symm.trans
    ((exceptionalPowerTheta A hd hA hRat r).trans
      (moduleH0Equiv (Over.mk (exceptionalStructureMap A hd))
        (exceptionalPower A hd r)).symm)

/-- Rationality computes the actual exceptional structural H0 dimension
using its original coefficient ring isomorphism. -/
theorem exceptionalUnit_h0_finrank (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (SheafOfModules.unit (exceptionalCurve A hd).ringCatSheaf) 0) = 1 := by
  let X := Over.mk (exceptionalStructureMap A hd)
  let O := SheafOfModules.unit (exceptionalCurve A hd).ringCatSheaf
  let : Module (A ⧸ maximalIdeal A) Γ(O, ⊤) := moduleGlobalSectionsModule X O
  let c : (A ⧸ maximalIdeal A) →ₗ[A ⧸ maximalIdeal A] Γ(O, ⊤) :=
    { toFun := exceptionalCoefficients A hd
      map_add' := (exceptionalCoefficients A hd).map_add
      map_smul' := (exceptionalCoefficients A hd).map_mul }
  let E := LinearEquiv.ofBijective c (exceptionalCoefficients_bijective A hd hA hRat)
  exact ((moduleH0Equiv X O).trans E.symm).finrank_eq.trans (Module.finrank_self _)

/-- Rationality kills actual exceptional structural H1 by the already proved
zeroth-power comparison, retaining the original full exceptional scheme. -/
theorem exceptionalUnit_h1_subsingleton (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A) :
    Subsingleton
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (SheafOfModules.unit (exceptionalCurve A hd).ringCatSheaf) 1) := by
  let : Subsingleton
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (exceptionalPower A hd 0) 1) := exceptionalPower_H1 A hd hA hRat 0
  exact (moduleCohomologyIso (Over.mk (exceptionalStructureMap A hd))
    (exceptionalPowerZeroIso A hd) 1).symm.injective.subsingleton

/-- The actual finite Cartier representative and its actual ideal cohomology
give every original associated graded dimension. No Hilbert-function premise
or assumed cone presentation occurs in this theorem. -/
theorem exceptional_hilbert_of_finiteCartier (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    {D : Scheme.{u}} (i : D ⟶ exceptionalCurve A hd) [IsClosedImmersion i]
    [IsFinite (i ≫ exceptionalStructureMap A hd)]
    (hI : IsLocallyRankOne (exceptionalCurve A hd) (idealModule i))
    (eL : (dualLineBundle (exceptionalCurve A hd) ⟨idealModule i, hI⟩).val ≅
      (exceptionalLine A hd).val)
    [Subsingleton (moduleCohomology (A ⧸ maximalIdeal A)
      (Over.mk (exceptionalStructureMap A hd)) (idealModule i) 0)]
    (hJ : Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (idealModule i) 1) = 1) (r : ℕ) :
    Module.finrank (ResidueField A)
      (Ideal.associatedGradedQuotientGrading (maximalIdeal A) r) = 2 * r + 1 := by
  let E := exceptionalCurve A hd
  let X := Over.mk (exceptionalStructureMap A hd)
  let : IsFinite (i ≫ X.hom) :=
    inferInstanceAs (IsFinite (i ≫ exceptionalStructureMap A hd))
  let : Subsingleton
      (moduleCohomology (A ⧸ maximalIdeal A) X
        (SheafOfModules.unit X.left.ringCatSheaf) 1) :=
    exceptionalUnit_h1_subsingleton A hd hA hRat
  let : Subsingleton (moduleCohomology (A ⧸ maximalIdeal A) X (idealModule i) 0) :=
    inferInstanceAs (Subsingleton (moduleCohomology (A ⧸ maximalIdeal A)
      (Over.mk (exceptionalStructureMap A hd)) (idealModule i) 0))
  have h := finiteCartier_dualIdealPower_cohomology X i hI
    (exceptionalUnit_h0_finrank A hd hA hRat) hJ r
  let eP : exceptionalPower A hd r ≅
      (tensorPowerLineBundle E (dualLineBundle E ⟨idealModule i, hI⟩) r).val :=
    exceptionalPowerTensorIso A hd r ≪≫ (TrivializedPower.powerIso E eL r).symm
  exact ((exceptionalGradedCohomologyEquiv A hd hA hRat r).trans
    (moduleCohomologyIso X eP 0)).finrank_eq.trans h.2

/-- The already constructed full-kernel producer applies to the literal
ordinary chart after the actual exceptional Cartier numerics. Its quadratic
and its exceptional quotient maps are not supplied as hypotheses. -/
theorem exceptional_quadratic_presentation_of_finiteCartier (hd : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    {D : Scheme.{u}} (i : D ⟶ exceptionalCurve A hd) [IsClosedImmersion i]
    [IsFinite (i ≫ exceptionalStructureMap A hd)]
    (hI : IsLocallyRankOne (exceptionalCurve A hd) (idealModule i))
    (eL : (dualLineBundle (exceptionalCurve A hd) ⟨idealModule i, hI⟩).val ≅
      (exceptionalLine A hd).val)
    [Subsingleton (moduleCohomology (A ⧸ maximalIdeal A)
      (Over.mk (exceptionalStructureMap A hd)) (idealModule i) 0)]
    (hJ : Module.finrank (A ⧸ maximalIdeal A)
      (moduleCohomology (A ⧸ maximalIdeal A) (Over.mk (exceptionalStructureMap A hd))
        (idealModule i) 1) = 1)
    (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun a =>
      (Localization.Away.CaseOne.orderedGenerators t g a : A)) = maximalIdeal A) :
    ∃ q : MvPolynomial (Fin 3) (ResidueField A),
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧
      RingHom.ker (Localization.Away.CaseOne.canonicalConeMap t g) = Ideal.span {q} ∧
      (t : A) ≠ 0 ∧ MvPolynomial.FirstCoordinate.dehom q ≠ 0 ∧
      (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2 ∧
      Nonempty (Localization.Away.CaseOne.Presentation A t g
        (MvPolynomial.FirstCoordinate.dehom q)) :=
  Localization.Away.CaseOne.exists_presentation_of_hilbert t g hgen
    (exceptional_hilbert_of_finiteCartier A hd hA hRat i hI eL hJ)

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

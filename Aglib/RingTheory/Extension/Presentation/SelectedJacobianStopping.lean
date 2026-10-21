/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.SelectedChartLocalDomain
public import Aglib.RingTheory.Etale.PolynomialChartTrdeg
public import Aglib.RingTheory.AlgebraicIndependent.Injective
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Stopping at the actual selected-Jacobian chart

The original coefficient map is faithful. The number of remaining variables
is the transcendence degree of the original algebra, not a dimension premise
on its local ring. The actual surjection from the selected-equation local ring
is proved injective and transports formal smoothness to the target local ring.
-/

@[expose] public noncomputable section

universe u w

namespace Algebra.Presentation

variable {R B : Type u} {σ : Type w} {ι τ : Type}
variable [CommRing R] [IsDomain R] [IsRegularRing R]
variable [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B]
variable [Finite ι] [Finite τ]
variable (P : Presentation R B ι σ) (e : τ → σ) (a : τ → ι)
variable (ha : Function.Injective a)

/-- A selected minor with the expected remaining transcendence degree stops
at every actual prime of its target principal open. Faithfulness of R → B
is essential; domain assumptions alone do not exclude vertical quotients. -/
theorem isSmoothAt_selectedJacobianTarget
    (hdeg : Algebra.trdeg R B = (Nat.card ι - Nat.card τ : ℕ))
    (q : Ideal (P.SelectedJacobianTarget e a ha)) [q.IsPrime] :
    Algebra.IsSmoothAt R q := by
  let C := P.SelectedJacobianSource e a ha
  let E := P.SelectedJacobianTarget e a ha
  let Q : Ideal C := q.comap (P.selectedJacobianQuotientMap e a ha).toRingHom
  let A := Localization.AtPrime Q
  let D := Localization.AtPrime q
  let n := Nat.card ι - Nat.card τ
  let T := MvPolynomial (Fin n) R
  let f : A →ₐ[R] D := P.selectedJacobianLocalMap e a ha q
  have hf : Function.Surjective f := P.selectedJacobianLocalMap_surjective e a ha q
  let : IsDomain A := P.selectedJacobianSource_local_isDomain e a ha Q
  let : IsDomain D := NoZeroDivisors.to_isDomain D
  let : Module.Flat B D := Module.Flat.trans B E D
  let : Module.IsTorsionFree B D := Module.Flat.isTorsionFree
  let : FaithfulSMul B D := Module.IsTorsionFree.to_faithfulSMul (R := B) (A := D)
  let : FaithfulSMul R D := FaithfulSMul.trans R B D
  let : IsStandardSmoothOfRelativeDimension n R C :=
    P.selectedJacobianSource_isStandardSmoothOfRelativeDimension e a ha
  obtain ⟨g, hg⟩ := IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R C
  let : Algebra T C := g.toRingHom.toAlgebra
  let : Algebra.Etale T C := hg
  let : SMul T C := Algebra.toSMul
  let : Module T C := Algebra.toModule
  let : MulAction T C := Algebra.toModule.toDistribMulAction.toMulAction
  let : Algebra T A := OreLocalization.instAlgebra
  let : IsScalarTower T C A := OreLocalization.instIsScalarTower
  let : IsScalarTower R T C := IsScalarTower.of_algHom g
  let : IsScalarTower R T A := IsScalarTower.to₁₂₄ R T C A
  let : Module.Flat T A := Module.Flat.trans T C A
  let : Algebra.EssFiniteType T A := Algebra.EssFiniteType.comp T C A
  let : Algebra.FormallyUnramified T A := Algebra.FormallyUnramified.comp T C A
  have hupper : Algebra.trdeg R A ≤ (n : Cardinal) := by
    simpa only [Cardinal.lift_id] using
      Algebra.FormallyUnramified.lift_trdeg_le_of_polynomial_chart R A n
  have hlower : (n : Cardinal) ≤ Algebra.trdeg R D := by
    rw [← hdeg]
    exact trdeg_le_of_injective (IsScalarTower.toAlgHom R B D)
      (FaithfulSMul.algebraMap_injective B D)
  have htarget : Algebra.trdeg R D ≤ (n : Cardinal) :=
    (trdeg_le_of_surjective f hf).trans hupper
  have hinj : Function.Injective f :=
    f.injective_of_surjective_of_lift_trdeg_le hf
      (htarget.trans_lt (by simp)) (by simpa using hupper.trans hlower)
  let : IsStandardSmooth R C :=
    IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let : Algebra.FormallySmooth R A := inferInstance
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective f ⟨hinj, hf⟩)

end Algebra.Presentation

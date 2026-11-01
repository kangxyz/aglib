/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Artinian.FiniteFreeSplitThickening
public import Aglib.RingTheory.Localization.FiniteIntegralCaptureBase
public import Aglib.RingTheory.GenericFreeness.Noetherian
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Generic split thickenings of finite algebras over Noetherian domains

First localize the original finite algebra at a genuine generic-freeness
denominator. The native localized-module/tensor equivalence supplies its
actual finite basis. Split its original geometric generic fibre, capture the
actual finite coefficients, and use integral lying over for the resulting
finite surjective coefficient base change. Two original principal opens are
retained rather than replaced by another localization model.

Neither a basis nor a split quotient is an input. In particular, the original
unlocalized tensor map is never assumed injective. This is the generic-domain
algebraic producer, not the full Noetherian stratification or scheme theorem.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.FiniteAlgebra

universe u v w x y

/-- The complete original finite-surjective principal-base-change conclusion.
This is an existence proposition over the original rings and maps, not an
additional model or a hypothesis asserting that a splitting has been found. -/
def finiteSplitThickeningOnPrincipalOpen
    (R : Type u) [CommRing R]
    (K : Type v) [Field K] [Algebra R K]
    (Ω : Type w) [Field Ω] [Algebra K Ω]
    (A : Type x) [CommRing A] [Algebra R A] : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ L : IntermediateField K Ω,
    letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
    ∃ b : R, b ≠ 0 ∧ ∃ B : Subalgebra R L, Module.Finite R B ∧
      RingHom.Finite (A := Localization.Away b)
        (B := Localization.Away (algebraMap R B b))
        (IsFractionRing.finiteSubalgebraAwayBaseMap B b).toRingHom ∧
      Function.Surjective (PrimeSpectrum.comap
        (IsFractionRing.finiteSubalgebraAwayBaseMap B b).toRingHom) ∧
      ∃ qC : (Localization.Away (algebraMap R B b)) ⊗[R] A →ₐ[Localization.Away
        (algebraMap R B b)]
          (MaximalSpectrum (Ω ⊗[K] (K ⊗[R] A)) → Localization.Away (algebraMap R B b)),
        Function.Surjective qC ∧ (RingHom.ker qC.toRingHom) ^ n = ⊥

/-- Construct the complete original quotient and both properties of its base
map before substituting a concrete generic-freeness localization. -/
theorem finiteSplitThickeningOnPrincipalOpen_of_basis
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ω : Type w) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (A : Type x) [CommRing A] [Algebra R A] {I : Type y} [Finite I]
    (basis : Module.Basis I R A) : finiteSplitThickeningOnPrincipalOpen R K Ω A := by
  obtain ⟨n, hn, L, hsplit⟩ := exists_finiteFree_splitThickening R K Ω basis
  refine ⟨n, hn, L, ?_⟩
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨b, hb, _hbL, B, hB, qC, hqC, hnC⟩ := hsplit
  have : Module.Finite R B := hB
  have hR : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  exact ⟨b, hb, B, hB, IsFractionRing.finiteSubalgebraAwayBaseMap_finite B b,
    IsFractionRing.finiteSubalgebraAwayBaseMap_comap_surjective B b hR, qC, hqC, hnC⟩

/-- A finite algebra over a Noetherian domain becomes an actual split
thickening after two principal restrictions and an actual finite surjective
base change. The geometric generic-fibre index is the original maximal
spectrum, and zero algebras and empty spectra are permitted. -/
theorem exists_noetherianGeneric_splitThickening
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ a : R, ∃ ha : a ≠ 0,
      letI : IsDomain (Localization.Away a) := Localization.Away.isDomain ha
      finiteSplitThickeningOnPrincipalOpen (Localization.Away a)
        (FractionRing (Localization.Away a))
        (AlgebraicClosure (FractionRing (Localization.Away a)))
        ((Localization.Away a) ⊗[R] A) := by
  classical
  obtain ⟨a, ha, hfree⟩ :=
    Module.Finite.exists_free_localizedModule_away_of_isNoetherianRing (A := R) A
  refine ⟨a, ha, ?_⟩
  let : IsDomain (Localization.Away a) := Localization.Away.isDomain ha
  have : Module.Free (Localization.Away a) (LocalizedModule.Away a A) := hfree
  have : Module.Free (Localization.Away a) ((Localization.Away a) ⊗[R] A) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers a) A)
  exact finiteSplitThickeningOnPrincipalOpen_of_basis (Localization.Away a)
    (FractionRing (Localization.Away a))
    (AlgebraicClosure (FractionRing (Localization.Away a)))
    ((Localization.Away a) ⊗[R] A)
    (Module.Free.chooseBasis (Localization.Away a) ((Localization.Away a) ⊗[R] A))

end Algebra.FiniteAlgebra

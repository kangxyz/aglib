/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.CompletedGlobalStep
public import Aglib.RingTheory.Extension.Presentation.EvaluatedFittingStopping
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Termination of actual global Néron modifications and the smooth π-centre

The fixed local target is Noetherian. Its evaluated Fitting ideals therefore
cannot increase indefinitely. Each nonterminal successor below is the actual
completed global modification from `CompletedGlobalStep`, not an assumed step
function. The source carriers stay in their original universe because the
actual finite centre generators are chosen with index `Fin m`.

The engine assumes only the intrinsic completed-fraction condition. The old
characteristic-zero entry points supply that condition and call the same proofs.

Termination permits unrelated coefficient, source, and common-field universes.
The smoothness corollary deliberately uses the aligned-universe finite-model
problem of the Artin application: its polynomial variables are `Fin n`. This
matches the existing smoothness-exit family, without silently imposing a
universe restriction on the separate arbitrary-source finite-model reduction.
-/

@[expose] public noncomputable section

open IsLocalRing Algebra.NeronModification Algebra.Presentation

namespace PowerSeriesLocalization

section Termination

universe u v w t
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) [Finite ι] (p : R) [Fact (Irreducible p)]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial ι R
local notation "C" => MvPowerSeries ι Rhat
local notation "S" => CompletedRing R ι p

local instance : IsDomain C := NoZeroDivisors.to_isDomain _
/-- The original polynomial action on the fixed completed-series target is
induced by its coefficientwise inclusion. -/
local instance completedTerminationInclusionAlgebra : Algebra P C :=
  (completedPolynomialInclusion R ι).toAlgebra

variable {B : Type w} [CommRing B] [Algebra (MvPolynomial ι R) B]
  [Algebra.FiniteType (MvPolynomial ι R) B]
variable (K : Type t) [Field K] [Algebra B K] [IsFractionRing B K]
  [Algebra (MvPolynomial ι R) K] [IsScalarTower (MvPolynomial ι R) B K]
  [Algebra (FractionRing (MvPolynomial ι R)) K]
  [IsScalarTower (MvPolynomial ι R) (FractionRing (MvPolynomial ι R)) K]

/-- Actual global modifications reach unit evaluated Fitting ideal in the
fixed localized target, retaining the original point and common fraction field.
`CommAlgCat` only bundles the actual source ring and its polynomial action; it
contains no step rule, closure oracle, or smoothness premise. -/
theorem exists_completedGlobal_unitFitting_of_geometricallyReducedFractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    (f : B →ₐ[P] C) (hinj : Function.Injective f)
    (j : K →+* FractionRing C)
    (hj : j.comp (algebraMap B K) = (algebraMap C (FractionRing C)).comp f.toRingHom)
    (r : ℕ) (hr : Algebra.trdeg (FractionRing P) K = (r : Cardinal)) :
    ∃ (B' : CommAlgCat.{w} P) (φ : B →ₐ[P] B') (f' : B' →ₐ[P] C)
      (k' : B' →+* K),
      Algebra.FiniteType P B' ∧ IsDomain B' ∧ Function.Injective f' ∧
      f'.comp φ = f ∧ k'.comp φ.toRingHom = algebraMap B K ∧
      (letI : Algebra B' K := k'.toAlgebra
       IsFractionRing B' K ∧ IsScalarTower P B' K) ∧
      j.comp k' = (algebraMap C (FractionRing C)).comp f'.toRingHom ∧
      (Module.fittingIdeal B' (KaehlerDifferential P B') r).map
        ((algebraMap C S).comp f'.toRingHom) = ⊤ := by
  classical
  let : IsDiscreteValuationRing S := completedRing_isDiscreteValuationRing R ι p
  let Goal : Ideal S → Prop := fun I =>
    ∀ (B₀ : CommAlgCat.{w} P) [Algebra.FiniteType P B₀] [Algebra B₀ K]
      [IsFractionRing B₀ K] [IsScalarTower P B₀ K]
      (f₀ : B₀ →ₐ[P] C) (hf₀ : Function.Injective f₀)
      (hj₀ : j.comp (algebraMap B₀ K) =
        (algebraMap C (FractionRing C)).comp f₀.toRingHom),
      (Module.fittingIdeal B₀ (KaehlerDifferential P B₀) r).map
          ((algebraMap C S).comp f₀.toRingHom) = I →
      ∃ (B' : CommAlgCat.{w} P) (φ : B₀ →ₐ[P] B') (f' : B' →ₐ[P] C)
        (k' : B' →+* K),
        Algebra.FiniteType P B' ∧ IsDomain B' ∧ Function.Injective f' ∧
        f'.comp φ = f₀ ∧ k'.comp φ.toRingHom = algebraMap B₀ K ∧
        (letI : Algebra B' K := k'.toAlgebra
         IsFractionRing B' K ∧ IsScalarTower P B' K) ∧
        j.comp k' = (algebraMap C (FractionRing C)).comp f'.toRingHom ∧
        (Module.fittingIdeal B' (KaehlerDifferential P B') r).map
          ((algebraMap C S).comp f'.toRingHom) = ⊤
  have hfinish : ∀ I : Ideal S, Goal I := by
    intro I
    induction I using WellFoundedGT.induction with
    | ind I ih =>
      dsimp only [Goal]
      intro B₀ hfin₀ hAlg₀ hfrac₀ htower₀ f₀ hf₀ hj₀ hI
      let : Algebra.FiniteType P B₀ := hfin₀
      let : Algebra B₀ K := hAlg₀
      let : IsFractionRing B₀ K := hfrac₀
      let : IsScalarTower P B₀ K := htower₀
      by_cases htop : I = ⊤
      · refine ⟨B₀, AlgHom.id P B₀, f₀, algebraMap B₀ K,
          inferInstance, Function.Injective.isDomain f₀ hf₀, hf₀, ?_, ?_, ?_, hj₀,
          hI.trans htop⟩
        · ext b
          rfl
        · ext b
          rfl
        · have halg : (algebraMap B₀ K).toAlgebra = hAlg₀ := toAlgebra_algebraMap
          exact Eq.mpr (congrArg (fun a : Algebra B₀ K =>
            letI : Algebra B₀ K := a
            IsFractionRing B₀ K ∧ IsScalarTower P B₀ K) halg)
            (show IsFractionRing B₀ K ∧ IsScalarTower P B₀ K from
              ⟨inferInstance, inferInstance⟩)
      · have hproper : (Module.fittingIdeal B₀ (KaehlerDifferential P B₀) r).map
            ((algebraMap C S).comp f₀.toRingHom) ≠ ⊤ := by
          rw [hI]
          exact htop
        -- Finite original centre generators, not generators of the closed
        -- point of C and not a changed auxiliary source.
        obtain ⟨m, g, hgen⟩ := exists_residueCentre_generators (MvPolynomial.C p) f₀
        let M := Modification (algebraMap P B₀ (MvPolynomial.C p)) g
        obtain ⟨fM, kM, hfM, hinjM, hdomM, hfinM, hkM, hfieldM, hjM, hstrict⟩ :=
          exists_completedGlobalStep_of_geometricallyReducedFractionCompletion
            R ι p K g hcoeff f₀ hf₀ j hj₀ r hr hgen hproper
        let : Algebra.FiniteType P M := hfinM
        let : IsDomain M := hdomM
        let : Algebra M K := kM.toAlgebra
        let : IsFractionRing M K := hfieldM.1
        let : IsScalarTower P M K := hfieldM.2
        let I' : Ideal S := (Module.fittingIdeal M (KaehlerDifferential P M) r).map
          ((algebraMap C S).comp fM.toRingHom)
        have hII' : I < I' := by
          rw [← hI]
          exact hstrict
        have hnext := ih I' hII'
        dsimp only [Goal] at hnext
        obtain ⟨B', φ', f', k', hfin', hdom', hinj', hpoint', hfieldpoint',
          hfield', hj', htop'⟩ :=
          hnext (CommAlgCat.of P M) fM hinjM hjM rfl
        let β : B₀ →ₐ[P] M := IsScalarTower.toAlgHom P B₀ M
        refine ⟨B', φ'.comp β, f', k', hfin', hdom', hinj', ?_, ?_,
          hfield', hj', htop'⟩
        · apply AlgHom.ext
          intro b
          exact (DFunLike.congr_fun hpoint' (β b)).trans (hfM b)
        · apply RingHom.ext
          intro b
          exact (DFunLike.congr_fun hfieldpoint' (β b)).trans (hkM b)
  exact hfinish _ (CommAlgCat.of P B) f hinj hj rfl

variable [CharZero R]

/-- Characteristic zero supplies the intrinsic completed-fraction condition
for the same actual global construction. -/
theorem exists_completedGlobal_unitFitting_of_charZero
    (f : B →ₐ[P] C) (hinj : Function.Injective f)
    (j : K →+* FractionRing C)
    (hj : j.comp (algebraMap B K) = (algebraMap C (FractionRing C)).comp f.toRingHom)
    (r : ℕ) (hr : Algebra.trdeg (FractionRing P) K = (r : Cardinal)) :
    ∃ (B' : CommAlgCat.{w} P) (φ : B →ₐ[P] B') (f' : B' →ₐ[P] C)
      (k' : B' →+* K),
      Algebra.FiniteType P B' ∧ IsDomain B' ∧ Function.Injective f' ∧
      f'.comp φ = f ∧ k'.comp φ.toRingHom = algebraMap B K ∧
      (letI : Algebra B' K := k'.toAlgebra
       IsFractionRing B' K ∧ IsScalarTower P B' K) ∧
      j.comp k' = (algebraMap C (FractionRing C)).comp f'.toRingHom ∧
      (Module.fittingIdeal B' (KaehlerDifferential P B') r).map
        ((algebraMap C S).comp f'.toRingHom) = ⊤ := by
  exact exists_completedGlobal_unitFitting_of_geometricallyReducedFractionCompletion R ι p K
    (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R)
    f hinj j hj r hr

end Termination

section SmoothEndpoint

universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (n : ℕ) (p : R) [Fact (Irreducible p)]

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial (Fin n) R
local notation "C" => MvPowerSeries (Fin n) Rhat
local notation "A" => ParameterLocalization.Ring R (Fin n) p
local notation "S" => CompletedRing R (Fin n) p
local notation "qC" => coefficientIdeal Rhat (Fin n) (algebraMap R Rhat p)

local instance : IsDomain C := NoZeroDivisors.to_isDomain _
local instance : Fact (Irreducible (algebraMap R Rhat p)) :=
  ⟨AdicCompletion.irreducible_algebraMap R p (Fact.out : Irreducible p)⟩
/-- The finite-parameter polynomial ring acts on the original completed-series
target by the same coefficientwise inclusion. -/
local instance completedSmoothInclusionAlgebra : Algebra P C :=
  (completedPolynomialInclusion R (Fin n)).toAlgebra

variable {B : Type u} [CommRing B] [Algebra (MvPolynomial (Fin n) R) B]
  [Algebra.FiniteType (MvPolynomial (Fin n) R) B]
variable (K : Type u) [Field K] [Algebra B K] [IsFractionRing B K]
  [Algebra (MvPolynomial (Fin n) R) K] [IsScalarTower (MvPolynomial (Fin n) R) B K]
  [Algebra (FractionRing (MvPolynomial (Fin n) R)) K]
  [IsScalarTower (MvPolynomial (Fin n) R) (FractionRing (MvPolynomial (Fin n) R)) K]

/-- The actual aligned-universe finite-model endpoint: an enlarged global
source, still finite type over the original polynomial ring, is smooth at the
literal kernel of reduction modulo π. Its evaluated Fitting ideal is unit only
in the fixed localization S; no smoothness at the full closed point of C is
asserted or used. -/
theorem exists_completedGlobal_smoothCentre_of_geometricallyReducedFractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    (f : B →ₐ[P] C) (hinj : Function.Injective f)
    (j : K →+* FractionRing C)
    (hj : j.comp (algebraMap B K) = (algebraMap C (FractionRing C)).comp f.toRingHom)
    (r : ℕ) (hr : Algebra.trdeg (FractionRing P) K = (r : Cardinal)) :
    ∃ (B' : CommAlgCat.{u} P) (φ : B →ₐ[P] B') (f' : B' →ₐ[P] C)
      (k' : B' →+* K),
      Algebra.FiniteType P B' ∧ IsDomain B' ∧ Function.Injective f' ∧
      f'.comp φ = f ∧ k'.comp φ.toRingHom = algebraMap B K ∧
      (letI : Algebra B' K := k'.toAlgebra
       IsFractionRing B' K ∧ IsScalarTower P B' K) ∧
      j.comp k' = (algebraMap C (FractionRing C)).comp f'.toRingHom ∧
      (Module.fittingIdeal B' (KaehlerDifferential P B') r).map
        ((algebraMap C S).comp f'.toRingHom) = ⊤ ∧
      ∃ hq : (residueCentre (MvPolynomial.C p) f').IsPrime,
        letI := hq
        Algebra.IsSmoothAt P (residueCentre (MvPolynomial.C p) f') := by
  classical
  obtain ⟨B', φ, f', k', hfin, hdom, hinj', hpoint, hfieldpoint, hfield, hj', htop⟩ :=
    exists_completedGlobal_unitFitting_of_geometricallyReducedFractionCompletion
      R (Fin n) p K hcoeff f hinj j hj r hr
  let : Algebra.FiniteType P B' := hfin
  let : IsDomain B' := hdom
  let : Algebra B' K := k'.toAlgebra
  let : IsFractionRing B' K := hfield.1
  let : IsScalarTower P B' K := hfield.2
  let ρ : C →+* S := algebraMap C S
  let : Algebra P S := (ρ.comp (completedPolynomialInclusion R (Fin n))).toAlgebra
  let : @FaithfulSMul P S (inferInstance : Algebra P S).toSMul :=
    (faithfulSMul_iff_algebraMap_injective P S).mpr (by
      have hmap : algebraMap P S =
          (completedPolynomialMap R (Fin n) p).comp (algebraMap P A) := by
        apply RingHom.ext
        intro a
        exact (completedPolynomialMap_polynomial R (Fin n) p a).symm
      rw [hmap]
      exact (completedPolynomialMap_injective R (Fin n) p).comp
        (IsLocalization.injective A (Ideal.primeCompl_le_nonZeroDivisors
          (ParameterLocalization.parameterIdeal R (Fin n) p))))
  let χ : B' →ₐ[P] S :=
    { __ := ρ.comp f'.toRingHom
      commutes' := by
        intro a
        change ρ (f' (algebraMap P B' a)) =
          ρ (completedPolynomialInclusion R (Fin n) a)
        rw [f'.commutes]
        rfl }
  have hsm : Algebra.IsSmoothAt P ((maximalIdeal S).comap χ.toRingHom) :=
    isSmoothAt_comap_maximalIdeal_of_generic_trdeg_of_map_fittingIdeal_eq_top_of_finiteType
      (K := FractionRing P) (L := K) χ r hr htop
  have hspan : Ideal.span {algebraMap P C (MvPolynomial.C p)} = qC := by
    change Ideal.span {completedPolynomialInclusion R (Fin n) (MvPolynomial.C p)} = _
    simp [completedPolynomialInclusion, coefficientIdeal]
  have hcentre : (maximalIdeal S).comap χ.toRingHom =
      residueCentre (MvPolynomial.C p) f' := by
    ext b
    change algebraMap C S (f' b) ∈ maximalIdeal S ↔
      Ideal.Quotient.mk (Ideal.span {algebraMap P C (MvPolynomial.C p)}) (f' b) = 0
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff S qC,
      Ideal.Quotient.eq_zero_iff_mem, hspan]
  have hq : (residueCentre (MvPolynomial.C p) f').IsPrime := by
    rw [← hcentre]
    infer_instance
  refine ⟨B', φ, f', k', hfin, hdom, hinj', hpoint, hfieldpoint, hfield, hj', htop, hq, ?_⟩
  simpa only [hcentre] using hsm

variable [CharZero R]

/-- Characteristic zero supplies the intrinsic completed-fraction condition
for the same actual global construction. -/
theorem exists_completedGlobal_smoothCentre_of_charZero
    (f : B →ₐ[P] C) (hinj : Function.Injective f)
    (j : K →+* FractionRing C)
    (hj : j.comp (algebraMap B K) = (algebraMap C (FractionRing C)).comp f.toRingHom)
    (r : ℕ) (hr : Algebra.trdeg (FractionRing P) K = (r : Cardinal)) :
    ∃ (B' : CommAlgCat.{u} P) (φ : B →ₐ[P] B') (f' : B' →ₐ[P] C)
      (k' : B' →+* K),
      Algebra.FiniteType P B' ∧ IsDomain B' ∧ Function.Injective f' ∧
      f'.comp φ = f ∧ k'.comp φ.toRingHom = algebraMap B K ∧
      (letI : Algebra B' K := k'.toAlgebra
       IsFractionRing B' K ∧ IsScalarTower P B' K) ∧
      j.comp k' = (algebraMap C (FractionRing C)).comp f'.toRingHom ∧
      (Module.fittingIdeal B' (KaehlerDifferential P B') r).map
        ((algebraMap C S).comp f'.toRingHom) = ⊤ ∧
      ∃ hq : (residueCentre (MvPolynomial.C p) f').IsPrime,
        letI := hq
        Algebra.IsSmoothAt P (residueCentre (MvPolynomial.C p) f') := by
  exact exists_completedGlobal_smoothCentre_of_geometricallyReducedFractionCompletion R n p K
    (AdicCompletion.hasGeometricallyReducedFractionCompletion_of_charZero R)
    f hinj j hj r hr

end SmoothEndpoint

end PowerSeriesLocalization

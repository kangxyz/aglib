/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.TracePairing
public import Aglib.RingTheory.KrullDimension.UnitDetection
public import Aglib.RingTheory.Spectrum.Prime.Bijectivity
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Discriminants and finite-flat purity

The determinant of the native algebra trace pairing detects etaleness of a
finite free algebra over a Noetherian ring. Residue-field base change and the
original module of Kaehler differentials supply the criterion.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace Algebra

/-- Algebra trace commutes with arbitrary scalar extension of a finite free algebra. -/
theorem trace_baseChange_one_tmul {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] (S : Type*) [CommRing S] [Algebra R S] (x : B) :
    trace S (S ⊗[R] B) (1 ⊗ₜ[R] x) = algebraMap R S (trace R B x) := by
  rw [trace_apply, ← baseChange_lmul, LinearMap.trace_baseChange, trace_apply]

/-- The discriminant of a scalar-extended basis is the scalar extension of its discriminant. -/
theorem discr_baseChange {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R B)
    (S : Type*) [CommRing S] [Algebra R S] :
    discr S (TensorProduct.basis S b) = algebraMap R S (discr R b) := by
  let : Module.Free R B := Module.Free.of_basis b
  let : Module.Finite R B := Module.Finite.of_basis b
  rw [discr_def, discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, traceMatrix_apply,
    traceForm_apply, TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, trace_baseChange_one_tmul]

/-- The discriminant criterion over a field, with no domain assumption on the algebra. -/
theorem etale_iff_discr_ne_zero_of_basis {K B ι : Type*} [Field K] [CommRing B]
    [Algebra K B] [Fintype ι] [DecidableEq ι] (b : Basis ι K B) :
    Etale K B ↔ discr K b ≠ 0 := by
  let : Module.Finite K B := Module.Finite.of_basis b
  rw [etale_iff_traceForm_nondegenerate,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b, discr_def, traceMatrix_of_basis]

/-- Over a Noetherian base, a finite free algebra is etale exactly when its
basis discriminant is a unit. -/
theorem etale_iff_isUnit_discr_of_basis {R B ι : Type*}
    [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R B) :
    Etale R B ↔ IsUnit (discr R b) := by
  let : Module.Free R B := Module.Free.of_basis b
  let : Module.Finite R B := Module.Finite.of_basis b
  let : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  constructor
  · intro h
    let := h
    by_contra hu
    obtain ⟨p, hp, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
    let := hp
    have hf : Etale p.ResidueField (p.ResidueField ⊗[R] B) := inferInstance
    have hn := (etale_iff_discr_ne_zero_of_basis (TensorProduct.basis p.ResidueField b)).mp hf
    rw [discr_baseChange] at hn
    exact hn (Ideal.algebraMap_residueField_eq_zero.mpr hmem)
  · intro hu
    have hf (p : Ideal R) [p.IsPrime] : Etale p.ResidueField (p.ResidueField ⊗[R] B) := by
      apply (etale_iff_discr_ne_zero_of_basis (TensorProduct.basis p.ResidueField b)).mpr
      rw [discr_baseChange]
      exact (hu.map (algebraMap R p.ResidueField)).ne_zero
    have : Module.Finite R Ω[B⁄R] := Module.Finite.trans B Ω[B⁄R]
    have : FormallyUnramified R B := by
      constructor
      apply Module.subsingleton_of_subsingleton_residueField_tensorProduct (R := R)
      intro p
      let := hf p.asIdeal
      let : Algebra B (p.asIdeal.ResidueField ⊗[R] B) := TensorProduct.rightAlgebra
      exact (KaehlerDifferential.tensorKaehlerEquivBase R p.asIdeal.ResidueField B
        (p.asIdeal.ResidueField ⊗[R] B)).injective.subsingleton
    exact Etale.of_formallyUnramified_of_flat

/-- Codimension-one purity for a finite free algebra over a Noetherian domain.
The generic etaleness hypothesis also handles zero-dimensional bases. -/
theorem etale_of_generic_and_height_one_etale_of_basis {R B ι : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Finite ι] (b : Basis ι R B)
    (hgeneric : Etale (FractionRing R) (FractionRing R ⊗[R] B))
    (hcodim : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      Etale (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] B)) :
    Etale R B := by
  classical
  let := Fintype.ofFinite ι
  apply (etale_iff_isUnit_discr_of_basis b).mpr
  have hgen : IsUnit (algebraMap R (FractionRing R) (discr R b)) := by
    rw [← discr_baseChange b]
    exact (etale_iff_isUnit_discr_of_basis (TensorProduct.basis (FractionRing R) b)).mp hgeneric
  have hne : discr R b ≠ 0 := by
    intro hzero
    exact hgen.ne_zero (by rw [hzero, map_zero])
  apply (isUnit_iff_isUnit_at_height_one hne).mpr
  intro p hp
  rw [← discr_baseChange b]
  exact (etale_iff_isUnit_discr_of_basis
    (TensorProduct.basis (Localization.AtPrime p.asIdeal) b)).mp (hcodim p hp)

/-- A unit basis discriminant makes the native trace pairing surjective onto the dual. -/
theorem traceForm_surjective_of_isUnit_discr {R B ι : Type*}
    [CommRing R] [CommRing B] [Algebra R B] [Fintype ι] [DecidableEq ι]
    (b : Basis ι R B) (h : IsUnit (discr R b)) :
    Function.Surjective (traceForm R B) := by
  have hm : IsUnit (traceMatrix R b) := (Matrix.isUnit_iff_isUnit_det _).mpr h
  intro f
  obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hm (fun i ↦ f (b i))
  refine ⟨b.equivFun.symm v, b.ext fun i ↦ ?_⟩
  have he := traceMatrix_of_basis_mulVec b (b.equivFun.symm v)
  rw [b.equivFun.apply_symm_apply] at he
  exact (congrFun he i).symm.trans (congrFun hv i)

/-- Finite free etale algebras over a Noetherian ring have a perfect trace pairing:
here the form is explicitly surjective onto the native linear dual. -/
theorem traceForm_surjective_of_etale {R B : Type*}
    [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] [Etale R B] :
    Function.Surjective (traceForm R B) :=
  traceForm_surjective_of_isUnit_discr (Module.Free.chooseBasis R B)
    ((etale_iff_isUnit_discr_of_basis (Module.Free.chooseBasis R B)).mp inferInstance)

/-- Codimension-one purity for a finite flat algebra over a local Noetherian domain.
The fraction-field hypothesis is retained also for zero-dimensional bases. -/
theorem etale_of_generic_and_height_one_etale_of_isLocalRing {R B : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B]
    (hgeneric : Etale (FractionRing R) (FractionRing R ⊗[R] B))
    (hcodim : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      Etale (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] B)) :
    Etale R B := by
  have : Module.Free R B := Module.free_of_flat_of_isLocalRing
  exact etale_of_generic_and_height_one_etale_of_basis
    (Module.Free.chooseBasis R B) hgeneric hcodim

end Algebra

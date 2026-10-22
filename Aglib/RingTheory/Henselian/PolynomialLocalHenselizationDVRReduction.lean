/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.CompletedGlobalImageSmooth
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFieldBase
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCoefficientSplit
public import Aglib.RingTheory.MvPolynomial.SmoothCentreFormalReduction
public import Aglib.RingTheory.Smooth.QuotientImage

/-!
# Actual selected-system reduction under the intrinsic DVR condition

The initial source is the literal polynomial evaluation image in the original
completed power-series ring. Actual global modifications make its π-centre
smooth. The enlarged unknown tuple keeps the original coordinates as its LEFT
summand and adds a finite generating family of the resulting source.

The actual formal kernel quotient is identified with that source by the native
first isomorphism theorem. Its smoothness is transported through the actual
localized algebra equivalence. The selected minor is nonzero after coefficient
reduction, not merely in the formal fraction field. No approximation solver is
assumed, and recovery uses only the left components of a close selected root.
The explicit coefficient premise is geometric reducedness of the actual
completed fraction field with its canonical coefficient action.
-/

@[expose] public noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing Algebra.NeronModification
open PowerSeriesLocalization

universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (n : ℕ)

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "P" => MvPolynomial (Fin n) R
local notation "C" => PolynomialLocalRing.FormalSeries R n
local notation "H" => PolynomialLocalHenselization R n

local instance intrinsicDVRReductionFormalSeriesIsDomain : IsDomain C :=
  NoZeroDivisors.to_isDomain _
/-- The polynomial coefficients act on the actual formal-series target through
the original coefficientwise polynomial inclusion. -/
local instance intrinsicDVRReductionPolynomialAlgebra : Algebra P C :=
  (completedPolynomialInclusion R (Fin n)).toAlgebra

/-- The geometric reduction feeding the existing selected-system solvers.
The extra unknowns are actual global-source generators, while every original
unknown remains literally the corresponding left component. -/
theorem exists_selected_system_at_formal_point_of_geometricallyReducedFractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    (m t : ℕ) (F : Fin t → MvPolynomial (Fin m) P) (y : Fin m → C)
    (hy : ∀ i, eval₂ (PolynomialLocalRing.polynomialToFormalSeries R n).toRingHom
      y (F i) = 0) (c : ℕ) :
    ∃ (ℓ : ℕ) (z : Fin m ⊕ Fin ℓ → C) (r : ℕ)
      (G : Fin r → MvPolynomial (Fin m ⊕ Fin ℓ) P)
      (cols : Fin r ↪ Fin m ⊕ Fin ℓ) (N : ℕ),
      (∀ j, z (Sum.inl j) = y j) ∧ c ≤ N ∧
      (∀ j, eval₂ (PolynomialLocalRing.polynomialToFormalSeries R n).toRingHom
        z (G j) = 0) ∧
      MvPowerSeries.map (residue Rhat)
        (eval₂ (PolynomialLocalRing.polynomialToFormalSeries R n).toRingHom z
          (Matrix.det (Matrix.of fun i j => pderiv (cols j) (G i)))) ≠ 0 ∧
      ∀ x : Fin m ⊕ Fin ℓ → H,
        (∀ j, toFormalSeries R n (x j) - z j ∈ maximalIdeal C ^ N) →
        (∀ j, eval₂ (polynomialToHenselization R n).toRingHom x (G j) = 0) →
        ∀ i, eval₂ (polynomialToHenselization R n).toRingHom
          (fun j => x (Sum.inl j)) (F i) = 0 := by
  classical
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : Fact (Irreducible p) := ⟨hp⟩
  let : Fact (Irreducible (algebraMap R Rhat p)) :=
    ⟨AdicCompletion.irreducible_algebraMap R p hp⟩
  let α : P →+* C := (PolynomialLocalRing.polynomialToFormalSeries R n).toRingHom
  let ψ : P →+* H := (polynomialToHenselization R n).toRingHom
  let τ : H →+* C := (toFormalSeries R n).toRingHom
  have hα : α = algebraMap P C := by
    change (PolynomialLocalRing.polynomialToFormalSeries R n).toRingHom =
      completedPolynomialInclusion R (Fin n)
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [PolynomialLocalRing.polynomialToFormalSeries, completedPolynomialInclusion,
        MvPowerSeries.algebraMap_apply]
    · intro i
      simp [PolynomialLocalRing.polynomialToFormalSeries, completedPolynomialInclusion]
  have hcomp : τ.comp ψ = α := by
    apply RingHom.ext
    intro a
    have h := AlgHom.congr_fun (toFormalSeries_comp_of R n)
      (algebraMap P (PolynomialLocalRing R n) a)
    change toFormalSeries R n (polynomialToHenselization R n a) =
      PolynomialLocalRing.toFormalSeries R n
        (algebraMap P (PolynomialLocalRing R n) a) at h
    exact h.trans (PolynomialLocalRing.toFormalSeries_algebraMap R n a)
  -- The original source is the actual image, not an unrelated quotient model.
  let E₀ : MvPolynomial (Fin m) P →ₐ[P] C := aeval y
  let B := E₀.range
  let f : B →ₐ[P] C := E₀.range.val
  have hinj : Function.Injective f := Subtype.val_injective
  let : Algebra.FiniteType P B :=
    Algebra.FiniteType.of_surjective E₀.rangeRestrict E₀.rangeRestrict_surjective
  let yB : Fin m → B := fun j => E₀.rangeRestrict (X j)
  have hyB (j : Fin m) : f (yB j) = y j := by
    change E₀ (X j) = y j
    exact aeval_X y j
  obtain ⟨B', φ, f', hfin', hdom', hinj', hpoint, hq, hsmooth⟩ :=
    exists_completedGlobal_image_smoothCentre_of_geometricallyReducedFractionCompletion
      R n p hcoeff f hinj
  let : Algebra.FiniteType P B' := hfin'
  let : IsDomain B' := hdom'
  let q : Ideal B' := residueCentre (MvPolynomial.C p) f'
  let : q.IsPrime := hq
  let : Algebra.IsSmoothAt P q := hsmooth
  obtain ⟨ℓ, ⟨Q⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp
    (inferInstance : Algebra.FiniteType P B')
  let v : Fin m ⊕ Fin ℓ → B' := Sum.elim (fun i => φ (yB i)) Q.val
  let z : Fin m ⊕ Fin ℓ → C := fun i => f' (v i)
  have hleft (i : Fin m) : z (Sum.inl i) = y i :=
    (DFunLike.congr_fun hpoint (yB i)).trans (hyB i)
  let E : MvPolynomial (Fin m ⊕ Fin ℓ) P →ₐ[P] B' := aeval v
  have hsurj : Function.Surjective E := by
    intro b
    obtain ⟨a, ha⟩ := Q.aeval_val_surjective b
    refine ⟨rename Sum.inr a, ?_⟩
    rw [show E (rename Sum.inr a) = aeval (v ∘ Sum.inr) a from
      aeval_rename Sum.inr v a]
    exact ha
  let EF : MvPolynomial (Fin m ⊕ Fin ℓ) P →+* C := eval₂Hom (τ.comp ψ) z
  have heval (a : MvPolynomial (Fin m ⊕ Fin ℓ) P) : EF a = f' (E a) := by
    change eval₂ (τ.comp ψ) z a = f' (aeval v a)
    rw [hcomp, hα]
    exact (comp_aeval_apply v f' a).symm
  let qC := coefficientIdeal Rhat (Fin n) (algebraMap R Rhat p)
  have hspan : Ideal.span {algebraMap P C (MvPolynomial.C p)} = qC := by
    change Ideal.span {completedPolynomialInclusion R (Fin n) (MvPolynomial.C p)} = _
    simp [completedPolynomialInclusion, coefficientIdeal, qC]
  have hqpoint : q = qC.comap f'.toRingHom := by
    ext b
    change Ideal.Quotient.mk (Ideal.span {algebraMap P C (MvPolynomial.C p)}) (f' b) = 0 ↔
      f' b ∈ qC
    rw [Ideal.Quotient.eq_zero_iff_mem, hspan]
  have hqCsmooth : Algebra.IsSmoothAt P (qC.comap f'.toRingHom) := by
    simpa only [hqpoint] using (show Algebra.IsSmoothAt P q from hsmooth)
  let hSmoothKer :=
    Algebra.IsSmoothAt.of_quotientKer_of_surjective E hsurj f' hinj' EF heval qC hqCsmooth
  let Fext : Fin t → MvPolynomial (Fin m ⊕ Fin ℓ) P := fun i => rename Sum.inl (F i)
  have hyext (i : Fin t) : eval₂ (τ.comp ψ) z (Fext i) = 0 := by
    rw [hcomp]
    change eval₂ α z (rename Sum.inl (F i)) = 0
    rw [eval₂_rename]
    have hz : z ∘ Sum.inl = y := funext hleft
    rw [hz]
    exact hy i
  let : IsAdicComplete (maximalIdeal C) C :=
    PolynomialLocalRing.formalSeries_isAdicComplete R n
  obtain ⟨r, G, cols, N, hc, hG, hdet, hrecover⟩ :=
    MvPolynomial.exists_selected_system_at_smooth_formal_centre (maximalIdeal C)
      ψ τ (toFormalSeries_injective R n) Fext z hyext qC c
  refine ⟨ℓ, z, r, G, cols, N, hleft, hc, ?_, ?_, ?_⟩
  · simpa only [hcomp] using hG
  · intro hzero
    apply hdet
    rw [hcomp]
    dsimp only [qC]
    rw [← ker_map_residue Rhat (Fin n) (algebraMap R Rhat p)
      (Fact.out : Irreducible (algebraMap R Rhat p))]
    exact hzero
  · intro x hx hxG i
    have h := hrecover x hx hxG i
    change eval₂ ψ x (rename Sum.inl (F i)) = 0 at h
    simpa only [eval₂_rename, Function.comp_def] using h

end PolynomialLocalHenselization

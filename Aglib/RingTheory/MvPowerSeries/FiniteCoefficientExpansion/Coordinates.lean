/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.FiniteCoefficientExpansion.FractionRing

/-!
# Finite expanded-base differentials on the original coordinate ring

One native series-coordinate equivalence transports the selected finite
coefficient-series basis to the original ring. The actual expanded base,
integral nonzero differential and original fraction field are unchanged.
-/

@[expose] public noncomputable section

open Module
open scoped TensorProduct

attribute [local instance 2000] Algebra.toSMul

namespace MvPowerSeries.FiniteCoefficientExpansion

variable {k R K : Type*} [Field k] [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (p : ℕ) [Fact p.Prime] [CharP k p]

omit [IsDomain R] [IsFractionRing R K] [Fact p.Prime] [CharP k p] in
/-- An original coefficient with no pth root in the original fraction field
has no pth root in its actual formal coordinates. -/
theorem not_exists_pow_of_coordinates (e : MvPowerSeries (Fin 2) k ≃+* R)
    (a : R) (ha : ¬ ∃ c : K, c ^ p = algebraMap R K a) :
    ¬ ∃ g : MvPowerSeries (Fin 2) k, g ^ p = e.symm a := by
  rintro ⟨g, hg⟩
  apply ha
  refine ⟨algebraMap R K (e g), ?_⟩
  calc
    algebraMap R K (e g) ^ p = algebraMap R K (e (g ^ p)) := by simp only [map_pow]
    _ = algebraMap R K a := by rw [hg, e.apply_symm_apply]

omit [IsDomain R] in
/-- Transport the single-series supplier through the SAME original ring equivalence.
The new base is expanded E[[X,Y]], not the residue coefficient field. Both the
finite integral differential basis and the fraction differential use this same base.
The original R, K and R → K are not replaced. -/
theorem exists_finite_basis_of_coordinates (e : MvPowerSeries (Fin 2) k ≃+* R)
    (a : R) (ha : ¬ ∃ c : K, c ^ p = algebraMap R K a) :
    ∃ E : Subfield k, ∃ r : ℕ, 0 < r ∧
      (letI : Algebra (MvPowerSeries (Fin 2) E) R :=
          (e.toRingHom.comp (scalarMap (k₀ := E) (k := k) p
            (Fact.out : p.Prime).ne_zero)).toAlgebra;
        letI : Algebra (MvPowerSeries (Fin 2) E) K :=
          ((algebraMap R K).comp (e.toRingHom.comp
            (scalarMap (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero))).toAlgebra;
        Module.Finite (MvPowerSeries (Fin 2) E) R ∧
        ∃ _bR : Basis (Fin r) R (KaehlerDifferential (MvPowerSeries (Fin 2) E) R),
          KaehlerDifferential.D (MvPowerSeries (Fin 2) E) R a ≠ 0 ∧
          Module.finrank K (KaehlerDifferential (MvPowerSeries (Fin 2) E) K) = r ∧
          KaehlerDifferential.D (MvPowerSeries (Fin 2) E) K (algebraMap R K a) ≠ 0) := by
  let S := MvPowerSeries (Fin 2) k
  let f : S := e.symm a
  have hf : ¬ ∃ g : S, g ^ p = f := not_exists_pow_of_coordinates p e a ha
  obtain ⟨E, r, hr, hfinite, ⟨b⟩, hdf⟩ := exists_singleSeries_finite_basis p f hf
  refine ⟨E, r, hr, ?_⟩
  let Λ := MvPowerSeries (Fin 2) E
  let : Algebra Λ S := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  let : Algebra S R := e.toRingHom.toAlgebra
  let : Algebra Λ R := (e.toRingHom.comp
    (scalarMap (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero)).toAlgebra
  let : Algebra Λ K := ((algebraMap R K).comp (e.toRingHom.comp
    (scalarMap (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero))).toAlgebra
  let : IsScalarTower Λ S R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Λ R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eΛ : S ≃ₐ[Λ] R := { e with commutes' := fun _ => rfl }
  let eS : S ≃ₐ[S] R := { e with commutes' := fun _ => rfl }
  let : Module.Finite Λ S := hfinite
  have hfiniteR : Module.Finite Λ R :=
    Module.Finite.of_surjective eΛ.toLinearMap e.surjective
  let : Algebra.FormallyEtale S R := Algebra.FormallyEtale.of_equiv eS
  let d := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Λ S R
  let bR : Basis (Fin r) R (KaehlerDifferential Λ R) := (b.baseChange R).map d
  have hefa : algebraMap S R f = a := e.apply_symm_apply a
  have hcoord (i : Fin r) :
      bR.repr (KaehlerDifferential.D Λ R a) i =
        e (b.repr (KaehlerDifferential.D Λ S f) i) := by
    change (b.baseChange R).repr
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Λ S R).symm
        (KaehlerDifferential.D Λ R a)) i = _
    rw [← hefa, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      Module.Basis.baseChange_repr_tmul]
    simp only [Algebra.smul_def, mul_one]
    rfl
  have hda : KaehlerDifferential.D Λ R a ≠ 0 := by
    intro hz
    apply hdf
    apply b.repr.injective
    apply Finsupp.ext
    intro i
    apply e.injective
    have hi := hcoord i
    simpa only [hz, map_zero, Finsupp.zero_apply] using hi.symm
  refine ⟨hfiniteR, bR, hda, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      KaehlerDifferential.finrank_fraction_of_basis (K := K) bR
  · exact KaehlerDifferential.fraction_D_ne_zero_of_basis (K := K) bR a hda

end MvPowerSeries.FiniteCoefficientExpansion

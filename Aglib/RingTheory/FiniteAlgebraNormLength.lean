/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.FiniteAlgebraLength
public import Mathlib.RingTheory.Norm.Defs

/-!
# Norms of finite algebras and local lengths

Determinants of scalar multiplication are computed through the literal prime
filtration. The resulting residue norms retain the local lengths, including
nilpotent structure and inseparable residue extensions.

The determinant argument is Stacks Project, Tag 0GSX, Lemma 15.122.2;
the norm is the existing determinant norm of Tag 0BD2.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Module

universe u v w w'

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  {M : Type w} [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]

/-- Scalar multiplication has the same determinant on isomorphic modules,
with the given scalar action and its literal restriction to the base field. -/
theorem det_lsmul_restrictScalars_eq_of_equiv
    {N : Type w'} [AddCommGroup N] [Module B N] [Module k N] [IsScalarTower k B N]
    (e : M ≃ₗ[B] N) (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      ((LinearMap.lsmul B N b).restrictScalars k).det := by
  let e' := e.restrictScalars k
  have h : e'.toLinearMap ∘ₗ (LinearMap.lsmul B M b).restrictScalars k ∘ₗ
      e'.symm.toLinearMap = (LinearMap.lsmul B N b).restrictScalars k := by
    ext x
    exact (e.map_smul b (e.symm x)).trans (congrArg (b • ·) (e.apply_symm_apply x))
  rw [← h, LinearMap.det_conj]

/-- Determinant multiplicativity for a submodule stable under the algebra
scalar action, retaining the actual quotient module. -/
theorem det_lsmul_restrictScalars_eq_mul [Module.Finite k M]
    (U : Submodule B M) (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      ((LinearMap.lsmul B U b).restrictScalars k).det *
        ((LinearMap.lsmul B (M ⧸ U) b).restrictScalars k).det := by
  let W := U.restrictScalars k
  let f := (LinearMap.lsmul B M b).restrictScalars k
  have hf : W ≤ W.comap f := fun x hx => U.smul_mem b hx
  have hsub : f.restrict (p := W) (q := W) hf = (LinearMap.lsmul B U b).restrictScalars k := by
    ext x
    rfl
  let e := Submodule.Quotient.restrictScalarsEquiv k U
  have hquot : e.toLinearMap ∘ₗ W.mapQ W f hf ∘ₗ e.symm.toLinearMap =
      (LinearMap.lsmul B (M ⧸ U) b).restrictScalars k := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  rw [LinearMap.det_eq_det_mul_det W f hf, hsub,
    ← LinearMap.det_conj (W.mapQ W f hf) e, hquot]
  rfl

/-- On the literal quotient algebra, the determinant of the original scalar
map is precisely the existing determinant norm of its quotient image. -/
theorem det_lsmul_quotient_eq_norm (p : Ideal B) (b : B) :
    ((LinearMap.lsmul B (B ⧸ p) b).restrictScalars k).det =
      Algebra.norm k (Ideal.Quotient.mk p b) := by
  rw [Algebra.norm_apply]
  congr 1

namespace PrimeFiltrationFrom

variable [Module.Finite k M]

/-- The actual prime filtration computes the determinant of scalar
multiplication. Its factors are norms on the literal prime quotients. -/
theorem det_lsmul_restrictScalars_eq_mul_prod {U : Submodule B M}
    (D : Module.PrimeFiltrationFrom M U) (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      ((LinearMap.lsmul B U b).restrictScalars k).det *
        (D.primes.map fun p => Algebra.norm k (Ideal.Quotient.mk p b)).prod := by
  induction D with
  | top =>
    simpa only [Module.PrimeFiltrationFrom.primes, List.map_nil, List.prod_nil, mul_one] using
      (det_lsmul_restrictScalars_eq_of_equiv (k := k)
        (Submodule.topEquiv (R := B) (M := M)) b).symm
  | @step U V hUV p hp e tail ih =>
    have : Module.Finite k V := Module.Finite.of_injective
      (V.subtype.restrictScalars k) V.subtype_injective
    have hstep := det_lsmul_restrictScalars_eq_mul (k := k) (U.comap V.subtype) b
    rw [det_lsmul_restrictScalars_eq_of_equiv (k := k)
      (Submodule.comapSubtypeEquivOfLe hUV.le) b,
      det_lsmul_restrictScalars_eq_of_equiv (k := k) e b,
      det_lsmul_quotient_eq_norm] at hstep
    rw [hstep] at ih
    simpa only [Module.PrimeFiltrationFrom.primes,
      List.map_cons, List.prod_cons, mul_assoc] using ih

/-- A complete prime filtration gives the determinant as a product of the
existing norms, with one factor for every occurrence in the filtration. -/
theorem det_lsmul_restrictScalars_eq_prod (D : Module.PrimeFiltrationFrom M ⊥) (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      (D.primes.map fun p => Algebra.norm k (Ideal.Quotient.mk p b)).prod := by
  simpa only [LinearMap.det_eq_one_of_subsingleton, one_mul] using
    D.det_lsmul_restrictScalars_eq_mul_prod (k := k) b

end PrimeFiltrationFrom

end Module

namespace Algebra

universe u v w

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]

/-- Group quotient-norm factors by maximal ideal, retaining repeated factors
as powers. No assertion of reducedness is involved. -/
theorem prod_quotient_norms_eq_prod_pow_count [Fintype (MaximalSpectrum B)]
    (ps : List (Ideal B)) (hps : ∀ p ∈ ps, p.IsMaximal) (b : B) :
    (ps.map fun p => Algebra.norm k (Ideal.Quotient.mk p b)).prod =
      ∏ p : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk p.asIdeal b) ^ ps.count p.asIdeal := by
  classical
  induction ps with
  | nil => simp
  | cons q ps ih =>
    have hq := hps q (by simp)
    have hs := ih (fun p hp => hps p (List.mem_cons_of_mem q hp))
    let q' : MaximalSpectrum B := ⟨q, hq⟩
    have hdelta : (∏ p : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk p.asIdeal b) ^
          (if q = p.asIdeal then 1 else 0)) =
        Algebra.norm k (Ideal.Quotient.mk q b) := by
      rw [Finset.prod_eq_single q']
      · simp [q']
      · intro p _ hp
        have hne : q ≠ p.asIdeal := fun h => hp (MaximalSpectrum.ext h.symm)
        simp [hne]
      · simp
    simp only [List.map_cons, List.prod_cons, List.count_cons, beq_iff_eq,
      pow_add, Finset.prod_mul_distrib]
    rw [← hs, hdelta, mul_comm]

end Algebra

namespace Module

universe u v w

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B] {M : Type w} [AddCommGroup M] [Module B M]
  [Module k M] [IsScalarTower k B M] [Module.Finite k M]

include k in
/-- A finite-dimensional module over a finite algebra has genuinely finite
length after localization at each maximal ideal. This precedes conversion of
its length from `ℕ∞` to `ℕ` in the determinant formula. -/
theorem localized_length_ne_top_of_finiteDimensional (p : MaximalSpectrum B) :
    Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[B] M) ≠ ⊤ := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite k B
  have : IsNoetherian B M := isNoetherian_of_tower k inferInstance
  have : IsArtinian B M := isArtinian_of_tower k inferInstance
  obtain ⟨D⟩ := Module.nonempty_primeFiltrationFrom (A := B) M ⊥
  rw [D.localized_length_eq_count_of_finiteLength Module.length_ne_top p]
  exact ENat.natCast_ne_top _

/-- The scalar determinant on a finite-dimensional module is the product of
residue-field norms with the literal local module lengths. The quotient maps
are canonical, and finiteness is established before `ENat.toNat` is used. -/
theorem det_lsmul_eq_prod_norm_pow_localized_length [Fintype (MaximalSpectrum B)]
    (b : B) :
    ((LinearMap.lsmul B M b).restrictScalars k).det =
      ∏ p : MaximalSpectrum B,
        Algebra.norm k (Ideal.Quotient.mk p.asIdeal b) ^
          (Module.length (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal ⊗[B] M)).toNat := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite k B
  have : IsNoetherian B M := isNoetherian_of_tower k inferInstance
  have : IsArtinian B M := isArtinian_of_tower k inferInstance
  have hM : Module.length B M ≠ ⊤ := Module.length_ne_top
  obtain ⟨D⟩ := Module.nonempty_primeFiltrationFrom (A := B) M ⊥
  rw [D.det_lsmul_restrictScalars_eq_prod,
    Algebra.prod_quotient_norms_eq_prod_pow_count D.primes
      (D.primes_isMaximal_of_length_ne_top hM)]
  apply Finset.prod_congr rfl
  intro p _
  have hlength := D.localized_length_eq_count_of_finiteLength hM p
  have hfinite : Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[B] M) ≠ ⊤ := by
    rw [hlength]
    exact ENat.natCast_ne_top _
  have hcount : (Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[B] M)).toNat = D.primes.count p.asIdeal := by
    apply ENat.natCast_inj.mp
    rw [ENat.natCast_toNat hfinite, hlength]
  exact congrArg (fun n => Algebra.norm k (Ideal.Quotient.mk p.asIdeal b) ^ n) hcount.symm

end Module

namespace Algebra

universe u v

variable {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
  [Module.Finite k B]

include k in
/-- Every local ring of a finite-dimensional commutative algebra has finite
length over itself, including the lengths used in the norm formula. -/
theorem local_length_ne_top_of_finite (p : MaximalSpectrum B) :
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≠ ⊤ := by
  rw [← (TensorProduct.AlgebraTensorModule.rid B
    (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).length_eq]
  exact Module.localized_length_ne_top_of_finiteDimensional (k := k) (M := B) p

/-- The norm of any element of a finite-dimensional commutative algebra is
the product of its actual residue-field norms, raised to the local lengths.
This includes nonreduced algebras, inseparable residue fields, and the zero
algebra, whose spectrum is empty and whose determinant norm is one. -/
theorem norm_eq_prod_quotient_norm_pow_local_length [Fintype (MaximalSpectrum B)]
    (b : B) :
    Algebra.norm k b = ∏ p : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal b) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat := by
  have h := Module.det_lsmul_eq_prod_norm_pow_localized_length (k := k) (M := B) b
  have hnorm : (LinearMap.lsmul B B b).restrictScalars k = Algebra.lmul k B b := by
    ext x
    rfl
  rw [hnorm, ← Algebra.norm_apply] at h
  have hlocal (p : MaximalSpectrum B) :
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[B] B) =
        Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) :=
    (TensorProduct.AlgebraTensorModule.rid B
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).length_eq
  simpa only [hlocal] using h

/-- Canonical finite-spectrum form of the norm formula. Finiteness of the
index type follows from the finite-algebra hypothesis; no enumeration or
semilocality hypothesis is supplied independently. -/
theorem norm_eq_prod_quotient_norm_pow_local_length_of_finite (b : B) :
    let : Finite (MaximalSpectrum B) :=
      Module.finiteAlgebra_maximalSpectrum_finite k B
    let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
    Algebra.norm k b = ∏ p : MaximalSpectrum B,
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal b) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat := by
  let : Finite (MaximalSpectrum B) :=
    Module.finiteAlgebra_maximalSpectrum_finite k B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  exact norm_eq_prod_quotient_norm_pow_local_length b

end Algebra

namespace IsLocalRing

universe u

/-- Localization at the maximal ideal of a local ring preserves its literal
self-length, via the canonical localization algebra map. -/
theorem length_localization_maximalIdeal (B : Type u) [CommRing B] [IsLocalRing B] :
    Module.length (Localization.AtPrime (maximalIdeal B))
      (Localization.AtPrime (maximalIdeal B)) = Module.length B B := by
  let L := Localization.AtPrime (maximalIdeal B)
  let e : B ≃ₐ[B] L :=
    IsLocalization.atUnits B (maximalIdeal B).primeCompl
      (fun x => by simpa using! fun a => a)
  have hs : Function.Surjective (algebraMap B L) := e.surjective
  exact (e.toLinearEquiv.length_eq.trans
    (Module.length_eq_of_surjective (S := B) (R := L) (M := L) hs)).symm

end IsLocalRing

namespace Algebra

universe u v

/-- For a finite local algebra the product specializes to its one actual
residue field, with exponent the full length of the algebra over itself. -/
theorem norm_eq_quotient_norm_pow_length {k : Type u} {B : Type v}
    [Field k] [CommRing B] [Algebra k B] [Module.Finite k B] [IsLocalRing B] (b : B) :
    Algebra.norm k b =
      Algebra.norm k (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b) ^
        (Module.length B B).toNat := by
  have h := norm_eq_prod_quotient_norm_pow_local_length (k := k) b
  rw [Fintype.prod_unique] at h
  change Algebra.norm k b =
    Algebra.norm k (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) b) ^
      (Module.length (Localization.AtPrime (IsLocalRing.maximalIdeal B))
        (Localization.AtPrime (IsLocalRing.maximalIdeal B))).toNat at h
  rwa [IsLocalRing.length_localization_maximalIdeal] at h

end Algebra

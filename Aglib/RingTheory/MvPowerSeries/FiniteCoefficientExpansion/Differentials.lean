/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.PurelyInseparable.NonPowerComplement
public import Aglib.RingTheory.Kaehler.BasisOfDerivations
public import Aglib.RingTheory.Kaehler.PureDegreePTrace
public import Aglib.RingTheory.MvPowerSeries.FiniteCoefficientExpansion.Derivation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The actual algebraic differentials over an expanded coefficient base

The finite coefficient-series basis proves algebraic generation. Original
coefficient and spatial derivations are dual to the two or three actual
generators, giving an ordinary Kähler basis with its coordinate formulas.
A non-pth-power series is detected over a coefficient field constructed
from that same series, including over fields of infinite p-rank.
-/

@[expose] public noncomputable section

open Module

namespace MvPowerSeries
namespace FiniteCoefficientExpansion

variable {E k : Type*} [Field E] [Field k] [Algebra E k]

/-- The finite series basis proves actual algebraic generation from coefficient and spatial data. -/
theorem eq_top_of_coefficientBasis_mem {D : Type*} [Finite D]
    (b : Basis D E k) (q : ℕ) (hq : q ≠ 0)
    [Algebra (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)]
    (hmap : algebraMap (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k) = scalarMap q hq)
    (S : Subalgebra (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k))
    (hcoeff : ∀ d, C (b d) ∈ S) (hvar : ∀ i : Fin 2, X i ∈ S) : S = ⊤ := by
  classical
  let := Fintype.ofFinite D
  let B := basisOfAlgebraMap b q hq hmap
  apply top_unique
  intro f hf
  rw [← B.sum_repr f]
  apply S.sum_mem
  intro i hi
  rw [Algebra.smul_def]
  apply S.mul_mem (S.algebraMap_mem _)
  change basisOfAlgebraMap b q hq hmap i ∈ S
  rw [basisOfAlgebraMap_apply]
  change basisVector b i ∈ S
  rw [basisVector_eq_prod]
  exact S.mul_mem (hcoeff i.1) (S.prod_mem fun j hj => S.pow_mem (hvar j) _)

/-- A surjective original coefficient inclusion supplies the constant singleton basis. -/
def surjectiveCoefficientBasis (hs : Function.Surjective (algebraMap E k)) : Basis Unit E k :=
  (Basis.singleton Unit E).map
    (AlgEquiv.ofBijective (Algebra.ofId E k) ⟨(algebraMap E k).injective, hs⟩).toLinearEquiv

@[simp]
theorem surjectiveCoefficientBasis_apply (hs : Function.Surjective (algebraMap E k)) (i : Unit) :
    surjectiveCoefficientBasis hs i = 1 := by
  simp [surjectiveCoefficientBasis, Basis.map_apply, Basis.singleton_apply]

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Formal partial derivatives kill the original expanded base in characteristic p. -/
theorem pderiv_scalarMap (i : Fin 2) (f : MvPowerSeries (Fin 2) E) :
    pderiv (R := k) i (scalarMap p (Fact.out : p.Prime).ne_zero f) = 0 := by
  classical
  apply MvPowerSeries.ext
  intro n
  rw [coeff_pderiv, coeff_zero]
  by_cases hd : p ∣ n i + 1
  · have hz : (n i + 1 : k) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (CharP.cast_eq_zero_iff k p (n i + 1)).mpr hd
    rw [hz, mul_zero]
  · have hn : ¬ p ∣ ((n + Finsupp.single i 1 : Fin 2 →₀ ℕ) i) := by
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using hd
    rw [scalarMap_apply, coeff_expand_of_not_dvd p (Fact.out : p.Prime).ne_zero _ hn,
      zero_mul]

/-- The actual spatial derivative, linear over the specified expanded scalar action. -/
def spatialDerivation (i : Fin 2) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    Derivation (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)
      (MvPowerSeries (Fin 2) k) := by
  letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  let D := pderiv (R := k) i
  refine
    { toFun := D
      map_add' := map_add D
      map_smul' := ?_
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  intro a f
  change D (scalarMap p (Fact.out : p.Prime).ne_zero a * f) =
    scalarMap p (Fact.out : p.Prime).ne_zero a * D f
  rw [D.leibniz, show D (scalarMap p (Fact.out : p.Prime).ne_zero a) = 0 from
    pderiv_scalarMap p i a]
  simp only [smul_eq_mul, mul_zero, add_zero]

@[simp]
theorem spatialDerivation_apply (i : Fin 2) (f : MvPowerSeries (Fin 2) k) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    spatialDerivation (E := E) p i f = pderiv (R := k) i f := rfl

theorem spatialDerivation_X (i j : Fin 2) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    spatialDerivation (E := E) (k := k) p i (X (R := k) j) =
      if i = j then 1 else 0 := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  change pderiv (R := k) i (X j) = _
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact pderiv_X_self
  · rw [ite_eq_right h]
    exact pderiv_X_of_ne (fun h' => h h'.symm)

omit [CharP k p] in
/-- The original two spatial generators generate when the coefficient map is surjective. -/
theorem adjoin_spatial_eq_top (hs : Function.Surjective (algebraMap E k)) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    Algebra.adjoin (MvPowerSeries (Fin 2) E) (Set.range (X (R := k) : Fin 2 → _)) = ⊤ := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  let S := Algebra.adjoin (MvPowerSeries (Fin 2) E) (Set.range (X (R := k) : Fin 2 → _))
  apply eq_top_of_coefficientBasis_mem (surjectiveCoefficientBasis hs) p
    (Fact.out : p.Prime).ne_zero rfl S
  · intro d
    simpa only [surjectiveCoefficientBasis_apply, map_one] using S.one_mem
  · intro i
    exact Algebra.subset_adjoin ⟨i, rfl⟩

/-- The two-variable ordinary Kähler basis, with the original spatial derivatives as coordinates. -/
def twoVariableBasis (hs : Function.Surjective (algebraMap E k)) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    Basis (Fin 2) (MvPowerSeries (Fin 2) k)
      (KaehlerDifferential (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)) := by
  letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  exact KaehlerDifferential.basisOfDerivations X (spatialDerivation (E := E) p)
    (adjoin_spatial_eq_top p hs) (spatialDerivation_X (E := E) p)

@[simp]
theorem twoVariableBasis_apply (hs : Function.Surjective (algebraMap E k)) (i : Fin 2) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    twoVariableBasis p hs i =
      KaehlerDifferential.D (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k) (X i) := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  exact KaehlerDifferential.basisOfDerivations_apply _ _ _ _ i

@[simp]
theorem twoVariableBasis_repr_D (hs : Function.Surjective (algebraMap E k))
    (f : MvPowerSeries (Fin 2) k) (i : Fin 2) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    (twoVariableBasis p hs).repr (KaehlerDifferential.D _ _ f) i = pderiv (R := k) i f := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  exact KaehlerDifferential.basisOfDerivations_repr_D _ _ _ _ f i

/-- The coefficient generator is first; the two original variables occupy successor indices. -/
def threeGenerators (c : k) (i : Fin 3) : MvPowerSeries (Fin 2) k :=
  (finSuccEquiv 2 i).elim (C c) X

@[simp] theorem threeGenerators_zero (c : k) : threeGenerators c 0 = C c := by
  simp [threeGenerators]

@[simp] theorem threeGenerators_succ (c : k) (i : Fin 2) :
    threeGenerators c i.succ = X i := by simp [threeGenerators]

/-- Coefficient and spatial derivatives in the same fixed order as `threeGenerators`. -/
def threeDerivations (δ : Derivation E k k) (i : Fin 3) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    Derivation (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)
      (MvPowerSeries (Fin 2) k) := by
  letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  exact (finSuccEquiv 2 i).elim
    (coefficientDerivationOverExpansion δ p (Fact.out : p.Prime).ne_zero)
    (spatialDerivation (E := E) p)

@[simp]
theorem threeDerivations_zero_apply (δ : Derivation E k k) (f : MvPowerSeries (Fin 2) k) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    threeDerivations p δ 0 f = coefficientDerivation δ f := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  change ((finSuccEquiv 2 0).elim
    (coefficientDerivationOverExpansion δ p (Fact.out : p.Prime).ne_zero)
    (spatialDerivation (E := E) (k := k) p)) f = coefficientDerivation δ f
  rw [finSuccEquiv_zero]
  rfl

@[simp]
theorem threeDerivations_succ_apply (δ : Derivation E k k)
    (i : Fin 2) (f : MvPowerSeries (Fin 2) k) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    threeDerivations p δ i.succ f = pderiv (R := k) i f := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  change ((finSuccEquiv 2 i.succ).elim
    (coefficientDerivationOverExpansion δ p (Fact.out : p.Prime).ne_zero)
    (spatialDerivation (E := E) (k := k) p)) f = pderiv (R := k) i f
  rw [finSuccEquiv_succ]
  rfl

theorem threeDerivations_generators (c : k) (δ : Derivation E k k) (hc : δ c = 1)
    (i j : Fin 3) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    threeDerivations p δ i (threeGenerators c j) = if i = j then 1 else 0 := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [hc]
    · have h : (0 : Fin 3) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simp only [threeGenerators_succ, threeDerivations_zero_apply,
        coefficientDerivation_X, ite_eq_right h]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [threeGenerators_succ, threeDerivations_succ_apply]
      by_cases h : i = j
      · subst j
        rw [ite_eq_left rfl]
        exact pderiv_X_self
      · have hij : i.succ ≠ j.succ := fun h' => h (Fin.succ_inj.mp h')
        rw [ite_eq_right hij]
        exact pderiv_X_of_ne (fun h' => h h'.symm)

omit [CharP k p] in
/-- The passed finite series basis proves generation by the original coefficient and variables. -/
theorem adjoin_three_eq_top (c : k) (b : Basis (Fin p) E k)
    (hb : ∀ i : Fin p, b i = c ^ (i : ℕ)) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    Algebra.adjoin (MvPowerSeries (Fin 2) E) (Set.range (threeGenerators c)) = ⊤ := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  let S := Algebra.adjoin (MvPowerSeries (Fin 2) E) (Set.range (threeGenerators c))
  have hC : C c ∈ S := by
    apply Algebra.subset_adjoin
    exact ⟨0, threeGenerators_zero c⟩
  apply eq_top_of_coefficientBasis_mem b p (Fact.out : p.Prime).ne_zero rfl S
  · intro i
    rw [hb i, map_pow]
    exact S.pow_mem hC _
  · intro i
    apply Algebra.subset_adjoin
    exact ⟨i.succ, threeGenerators_succ c i⟩

/-- The actual rank-three Kähler basis, with coefficient coordinate first. -/
def threeVariableBasis (c : k) (b : Basis (Fin p) E k)
    (hb : ∀ i : Fin p, b i = c ^ (i : ℕ)) (δ : Derivation E k k) (hc : δ c = 1) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    Basis (Fin 3) (MvPowerSeries (Fin 2) k)
      (KaehlerDifferential (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)) := by
  letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  exact KaehlerDifferential.basisOfDerivations (threeGenerators c) (threeDerivations p δ)
    (adjoin_three_eq_top p c b hb) (threeDerivations_generators p c δ hc)

@[simp]
theorem threeVariableBasis_apply (c : k) (b : Basis (Fin p) E k)
    (hb : ∀ i : Fin p, b i = c ^ (i : ℕ)) (δ : Derivation E k k) (hc : δ c = 1)
    (i : Fin 3) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    threeVariableBasis p c b hb δ hc i = KaehlerDifferential.D _ _ (threeGenerators c i) := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  exact KaehlerDifferential.basisOfDerivations_apply _ _ _ _ i

@[simp]
theorem threeVariableBasis_repr_D (c : k) (b : Basis (Fin p) E k)
    (hb : ∀ i : Fin p, b i = c ^ (i : ℕ)) (δ : Derivation E k k) (hc : δ c = 1)
    (f : MvPowerSeries (Fin 2) k) (i : Fin 3) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    (threeVariableBasis p c b hb δ hc).repr (KaehlerDifferential.D _ _ f) i =
      threeDerivations p δ i f := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  exact KaehlerDifferential.basisOfDerivations_repr_D _ _ _ _ f i

omit [Fact p.Prime] in
/-- A specified coefficient outside a p-divisible spatial exponent gives a nonzero partial. -/
theorem pderiv_ne_zero_of_coeff (f : MvPowerSeries (Fin 2) k)
    (n : Fin 2 →₀ ℕ) (i : Fin 2) (hni : ¬ p ∣ n i) (hnf : coeff n f ≠ 0) :
    pderiv (R := k) i f ≠ 0 := by
  classical
  have hpos : 0 < n i := Nat.pos_of_ne_zero (fun h => hni (h.symm ▸ dvd_zero p))
  have hle : Finsupp.single i 1 ≤ n := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Finsupp.single_eq_same] using Nat.succ_le_of_lt hpos
    · simp [hji]
  let m := n - Finsupp.single i 1
  have hm : m + Finsupp.single i 1 = n := tsub_add_cancel_of_le hle
  have hmi : m i + 1 = n i := by
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using congrArg (fun d => d i) hm
  have he : coeff m (pderiv (R := k) i f) = coeff n f * (n i : k) := by
    rw [coeff_pderiv, hm]
    congr 1
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun a : ℕ => (a : k)) hmi
  intro hz
  have hprod : coeff n f * (n i : k) = 0 := by rw [← he, hz, coeff_zero]
  exact (mul_ne_zero hnf ((CharP.cast_eq_zero_iff k p (n i)).not.mpr hni)) hprod

theorem D_ne_zero_of_spatial_coeff (hs : Function.Surjective (algebraMap E k))
    (f : MvPowerSeries (Fin 2) k) (n : Fin 2 →₀ ℕ) (i : Fin 2)
    (hni : ¬ p ∣ n i) (hnf : coeff n f ≠ 0) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    KaehlerDifferential.D (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k) f ≠ 0 := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  intro h
  have hz := congrArg (fun ω => (twoVariableBasis p hs).repr ω i) h
  apply pderiv_ne_zero_of_coeff p f n i hni hnf
  simpa only [twoVariableBasis_repr_D, map_zero, Finsupp.zero_apply] using hz

theorem D_ne_zero_of_coefficient (c : k) (b : Basis (Fin p) E k)
    (hb : ∀ i : Fin p, b i = c ^ (i : ℕ)) (δ : Derivation E k k) (hc : δ c = 1)
    (f : MvPowerSeries (Fin 2) k) (n : Fin 2 →₀ ℕ) (hn : coeff n f = c) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    KaehlerDifferential.D (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k) f ≠ 0 := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  intro h
  have hz := congrArg (fun ω => coeff n ((threeVariableBasis p c b hb δ hc).repr ω 0)) h
  have h10 : (1 : k) = 0 := by
    simpa only [threeVariableBasis_repr_D, threeDerivations_zero_apply,
      coeff_coefficientDerivation, hn, hc, map_zero, Finsupp.zero_apply, coeff_zero] using hz
  exact one_ne_zero h10

/-- The actual two-generator basis has rank two. -/
theorem twoVariable_finrank (hs : Function.Surjective (algebraMap E k)) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    Module.finrank (MvPowerSeries (Fin 2) k)
      (KaehlerDifferential (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)) = 2 := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  rw [Module.finrank_eq_card_basis (twoVariableBasis p hs), Fintype.card_fin]

/-- The actual coefficient-first basis has rank three. -/
theorem threeVariable_finrank (c : k) (b : Basis (Fin p) E k)
    (hb : ∀ i : Fin p, b i = c ^ (i : ℕ)) (δ : Derivation E k k) (hc : δ c = 1) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    Module.finrank (MvPowerSeries (Fin 2) k)
      (KaehlerDifferential (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)) = 3 := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  rw [Module.finrank_eq_card_basis (threeVariableBasis p c b hb δ hc), Fintype.card_fin]

/-- Exterior basis vectors are the ordered wedges of the original two generator differentials. -/
theorem twoVariable_exteriorBasis_apply (hs : Function.Surjective (algebraMap E k))
    (m : ℕ) (s : Set.powersetCard (Fin 2) m) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    (twoVariableBasis p hs).exteriorPower m s =
      exteriorPower.ιMulti_family (MvPowerSeries (Fin 2) k) m
        (fun i : Fin 2 => KaehlerDifferential.D (MvPowerSeries (Fin 2) E)
          (MvPowerSeries (Fin 2) k) (X i)) s := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  rw [exteriorPower.basis_apply]
  congr 1
  funext i
  exact twoVariableBasis_apply p hs i

/-- Exterior basis vectors retain the coefficient-first orientation of the three generators. -/
theorem threeVariable_exteriorBasis_apply (c : k) (b : Basis (Fin p) E k)
    (hb : ∀ i : Fin p, b i = c ^ (i : ℕ)) (δ : Derivation E k k) (hc : δ c = 1)
    (m : ℕ) (s : Set.powersetCard (Fin 3) m) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    (threeVariableBasis p c b hb δ hc).exteriorPower m s =
      exteriorPower.ιMulti_family (MvPowerSeries (Fin 2) k) m
        (fun i : Fin 3 => KaehlerDifferential.D (MvPowerSeries (Fin 2) E)
          (MvPowerSeries (Fin 2) k) (threeGenerators c i)) s := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  rw [exteriorPower.basis_apply]
  congr 1
  funext i
  exact threeVariableBasis_apply p c b hb δ hc i

/-- Wedge coordinates are the determinants of the original spatial derivative matrix. -/
theorem twoVariable_exterior_repr (hs : Function.Surjective (algebraMap E k))
    (m : ℕ) (s : Set.powersetCard (Fin 2) m)
    (f : Fin m → MvPowerSeries (Fin 2) k) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    ((twoVariableBasis p hs).exteriorPower m).repr
        (exteriorPower.ιMulti (MvPowerSeries (Fin 2) k) m
          (fun i => KaehlerDifferential.D (MvPowerSeries (Fin 2) E)
            (MvPowerSeries (Fin 2) k) (f i))) s =
      (Matrix.of fun i j => pderiv (R := k)
        (Set.powersetCard.ofFinEmbEquiv.symm s j) (f i)).det := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  apply congrArg Matrix.det
  funext i j
  change (twoVariableBasis p hs).repr (KaehlerDifferential.D _ _ (f i))
    (Set.powersetCard.ofFinEmbEquiv.symm s j) = _
  exact twoVariableBasis_repr_D p hs (f i) _

/-- Wedge coordinates use the actual coefficient and spatial derivations in their fixed order. -/
theorem threeVariable_exterior_repr (c : k) (b : Basis (Fin p) E k)
    (hb : ∀ i : Fin p, b i = c ^ (i : ℕ)) (δ : Derivation E k k) (hc : δ c = 1)
    (m : ℕ) (s : Set.powersetCard (Fin 3) m)
    (f : Fin m → MvPowerSeries (Fin 2) k) :
    letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    ((threeVariableBasis p c b hb δ hc).exteriorPower m).repr
        (exteriorPower.ιMulti (MvPowerSeries (Fin 2) k) m
          (fun i => KaehlerDifferential.D (MvPowerSeries (Fin 2) E)
            (MvPowerSeries (Fin 2) k) (f i))) s =
      (Matrix.of fun i j => threeDerivations p δ
        (Set.powersetCard.ofFinEmbEquiv.symm s j) (f i)).det := by
  let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  apply congrArg Matrix.det
  funext i j
  change (threeVariableBasis p c b hb δ hc).repr (KaehlerDifferential.D _ _ (f i))
    (Set.powersetCard.ofFinEmbEquiv.symm s j) = _
  exact threeVariableBasis_repr_D p c b hb δ hc (f i) _

/-- The coefficient derivation is obtained from the constructed original monic presentation. -/
def nonPowerCoefficientDerivation (F : Subfield k) (c : k)
    (hF : Maximal (fun G : Subfield k => (frobenius k p).fieldRange ≤ G ∧ c ∉ G) F) :
    Derivation F k k :=
  KaehlerDifferential.pureDegreePDerivation (Subfield.nonPowerComplementPresentation p F c hF)

@[simp]
theorem nonPowerCoefficientDerivation_self (F : Subfield k) (c : k)
    (hF : Maximal (fun G : Subfield k => (frobenius k p).fieldRange ≤ G ∧ c ∉ G) F) :
    nonPowerCoefficientDerivation p F c hF c = 1 := by
  simpa only [nonPowerCoefficientDerivation, Subfield.nonPowerComplementPresentation_root]
    using KaehlerDifferential.pureDegreePDerivation_root
      (Subfield.nonPowerComplementPresentation p F c hF)

/-- The actual Kähler basis attached to the field constructed from the specified coefficient. -/
def nonPowerDifferentialBasis (F : Subfield k) (c : k)
    (hF : Maximal (fun G : Subfield k => (frobenius k p).fieldRange ≤ G ∧ c ∉ G) F) :
    letI := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
    Basis (Fin 3) (MvPowerSeries (Fin 2) k)
      (KaehlerDifferential (MvPowerSeries (Fin 2) F) (MvPowerSeries (Fin 2) k)) := by
  letI := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
  exact threeVariableBasis p c (Subfield.nonPowerComplementBasis p F c hF)
    (Subfield.nonPowerComplementBasis_apply p F c hF)
    (nonPowerCoefficientDerivation p F c hF) (nonPowerCoefficientDerivation_self p F c hF)

theorem nonPower_D_ne_zero (F : Subfield k) (c : k)
    (hF : Maximal (fun G : Subfield k => (frobenius k p).fieldRange ≤ G ∧ c ∉ G) F)
    (f : MvPowerSeries (Fin 2) k) (n : Fin 2 →₀ ℕ) (hn : coeff n f = c) :
    letI := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
    KaehlerDifferential.D (MvPowerSeries (Fin 2) F) (MvPowerSeries (Fin 2) k) f ≠ 0 := by
  let := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero
  exact D_ne_zero_of_coefficient p c (Subfield.nonPowerComplementBasis p F c hF)
    (Subfield.nonPowerComplementBasis_apply p F c hF)
    (nonPowerCoefficientDerivation p F c hF) (nonPowerCoefficientDerivation_self p F c hF) f n hn

/-- The literal Frobenius coefficient criterion constructs a root series coefficientwise. -/
theorem exists_pow_eq_of_coeff (f : MvPowerSeries (Fin 2) k)
    (hzero : ∀ n : Fin 2 →₀ ℕ, ∀ i : Fin 2, ¬ p ∣ n i → coeff n f = 0)
    (hcoeff : ∀ n, coeff n f ∈ (frobenius k p).fieldRange) :
    ∃ g : MvPowerSeries (Fin 2) k, g ^ p = f := by
  classical
  have hc : ∀ n, ∃ a : k, a ^ p = coeff n f := fun n => hcoeff n
  choose a ha using hc
  let g : MvPowerSeries (Fin 2) k := fun n => a (p • n)
  refine ⟨g, MvPowerSeries.ext fun n => ?_⟩
  by_cases hd : ∀ i, p ∣ n i
  · let m : Fin 2 →₀ ℕ := n.mapRange (fun b => b / p) (Nat.zero_div p)
    have hn : n = p • m := by
      ext i
      simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, m]
      exact (Nat.mul_div_cancel' (hd i)).symm
    rw [hn, ← map_frobenius_expand p (Fact.out : p.Prime).ne_zero,
      coeff_map, coeff_expand_smul]
    exact ha (p • m)
  · push Not at hd
    obtain ⟨i, hi⟩ := hd
    rw [← map_frobenius_expand p (Fact.out : p.Prime).ne_zero, coeff_map,
      coeff_expand_of_not_dvd p (Fact.out : p.Prime).ne_zero _ hi, map_zero, hzero n i hi]

/-- A non-pth-power series selects its actual expanded coefficient base
and nonzero differential.
The left branch has the canonical top coefficient field and the constructed rank-two basis;
the right branch has the maximal avoiding field and the constructed rank-three basis. -/
theorem exists_singleSeries_base (f : MvPowerSeries (Fin 2) k)
    (hf : ¬ ∃ g : MvPowerSeries (Fin 2) k, g ^ p = f) :
    (letI := scalarAlgebra (k₀ := (⊤ : Subfield k)) (k := k) p (Fact.out : p.Prime).ne_zero;
      KaehlerDifferential.D (MvPowerSeries (Fin 2) (⊤ : Subfield k))
        (MvPowerSeries (Fin 2) k) f ≠ 0) ∨
    ∃ n : Fin 2 →₀ ℕ, ∃ F : Subfield k,
      ∃ _hF : Maximal (fun G : Subfield k => (frobenius k p).fieldRange ≤ G ∧ coeff n f ∉ G) F,
      (letI := scalarAlgebra (k₀ := F) (k := k) p (Fact.out : p.Prime).ne_zero;
        KaehlerDifferential.D (MvPowerSeries (Fin 2) F) (MvPowerSeries (Fin 2) k) f ≠ 0) := by
  classical
  by_cases hsp : ∃ n : Fin 2 →₀ ℕ, ∃ i : Fin 2, ¬ p ∣ n i ∧ coeff n f ≠ 0
  · obtain ⟨n, i, hni, hnf⟩ := hsp
    left
    have hs : Function.Surjective (algebraMap (⊤ : Subfield k) k) :=
      fun x => ⟨⟨x, by simp⟩, rfl⟩
    exact D_ne_zero_of_spatial_coeff p hs f n i hni hnf
  · have hzero : ∀ n : Fin 2 →₀ ℕ, ∀ i : Fin 2, ¬ p ∣ n i → coeff n f = 0 := by
      intro n i hni
      by_contra hnf
      exact hsp ⟨n, i, hni, hnf⟩
    have hc : ∃ n, coeff n f ∉ (frobenius k p).fieldRange := by
      by_contra h
      push Not at h
      exact hf (exists_pow_eq_of_coeff p f hzero h)
    obtain ⟨n, hn⟩ := hc
    obtain ⟨F, hF, -⟩ := Subfield.exists_nonPowerComplement p (coeff n f) hn
    exact Or.inr ⟨n, F, hF, nonPower_D_ne_zero p F (coeff n f) hF f n rfl⟩

end FiniteCoefficientExpansion
end MvPowerSeries

namespace KaehlerDifferential

/-- Localization preserves a nonzero actual differential when the displayed ordinary basis
has no torsion under the actual denominators. The original scalar square is retained. -/
theorem map_D_ne_zero_of_basis_localization
    {R S A B ι : Type*} [CommRing R] [CommRing S] [CommRing A] [IsDomain A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B]
    (M : Submonoid R) [IsLocalization M S]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) B]
    (b : Basis ι A (KaehlerDifferential R A))
    (hM : ∀ s : M, algebraMap R A (s : R) ≠ 0)
    (a : A) (ha : D R A a ≠ 0) : D S B (algebraMap A B a) ≠ 0 := by
  have hinj : Function.Injective (map R S A B) := by
    change Function.Injective ((map R S A B).restrictScalars R)
    apply (IsLocalizedModule.injective_iff_isRegular M ((map R S A B).restrictScalars R)).mpr
    intro s ω η h
    change (s : R) • ω = (s : R) • η at h
    have hA : algebraMap R A (s : R) • ω = algebraMap R A (s : R) • η := by
      simpa only [IsScalarTower.algebraMap_smul] using h
    apply b.repr.injective
    ext i
    apply mul_left_cancel₀ (hM s)
    have hi := congrArg (fun z => b.repr z i) hA
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using hi
  intro hz
  apply ha
  apply hinj
  rw [map_D, map_zero]
  exact hz

end KaehlerDifferential

namespace MvPowerSeries.FiniteCoefficientExpansion

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Choose the finite coefficient complement before localization or modification.
The base action is expansion by p, not the constant-field action. -/
theorem exists_singleSeries_finite_basis (f : MvPowerSeries (Fin 2) k)
    (hf : ¬ ∃ g : MvPowerSeries (Fin 2) k, g ^ p = f) :
    ∃ E : Subfield k, ∃ r : ℕ, 0 < r ∧
      (letI := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero;
        Module.Finite (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k) ∧
        Nonempty (Module.Basis (Fin r) (MvPowerSeries (Fin 2) k)
          (KaehlerDifferential (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k))) ∧
        KaehlerDifferential.D (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k) f ≠ 0) := by
  obtain h | ⟨n, E, hE, h⟩ := exists_singleSeries_base p f hf
  · refine ⟨⊤, 2, by decide, ?_⟩
    let := scalarAlgebra (k₀ := (⊤ : Subfield k)) (k := k) p
      (Fact.out : p.Prime).ne_zero
    have hs : Function.Surjective (algebraMap (⊤ : Subfield k) k) :=
      fun x => ⟨⟨x, by simp⟩, rfl⟩
    exact ⟨module_finite (surjectiveCoefficientBasis hs) p (Fact.out : p.Prime).ne_zero,
      ⟨twoVariableBasis p hs⟩, h⟩
  · refine ⟨E, 3, by decide, ?_⟩
    let := scalarAlgebra (k₀ := E) (k := k) p (Fact.out : p.Prime).ne_zero
    exact ⟨module_finite (Subfield.nonPowerComplementBasis p E (coeff n f) hE)
      p (Fact.out : p.Prime).ne_zero,
      ⟨nonPowerDifferentialBasis p E (coeff n f) hE⟩, h⟩

end MvPowerSeries.FiniteCoefficientExpansion

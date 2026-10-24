/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.PureDegreePTrace.Presentation
public import Aglib.LinearAlgebra.ExteriorPower.ScalarExtension
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.Data.Finset.Piecewise

/-!
# The actual degree-p trace on exterior differential forms

The original coefficient epsilon is applied after the alternating insertion
map on actual Kähler differentials. The root-last formulas, their uniqueness,
and scalar and localization comparisons retain these same maps.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- An alternating map that kills one input in a submodule is unchanged by
replacing one input with another representative of the same quotient class. -/
theorem map_update_of_mkQ_eq [DecidableEq (Fin n)]
    (K : Submodule R M) (f : M [⋀^Fin n]→ₗ[R] N)
    (hK : ∀ (v : Fin n → M) (i : Fin n), v i ∈ K → f v = 0)
    (v : Fin n → M) (i : Fin n) (x y : M) (hxy : K.mkQ x = K.mkQ y) :
    f (Function.update v i x) = f (Function.update v i y) := by
  have hz : K.mkQ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hmem : x - y ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hz
  have hf := hK (Function.update v i (x - y)) i (by simpa only [Function.update_self] using hmem)
  rw [f.map_update_sub] at hf
  exact sub_eq_zero.mp hf

/-- Finite tuples of equal quotient classes give equal values of the original map. -/
theorem map_eq_of_mkQ_eq (K : Submodule R M) (f : M [⋀^Fin n]→ₗ[R] N)
    (hK : ∀ (v : Fin n → M) (i : Fin n), v i ∈ K → f v = 0)
    (v w : Fin n → M) (hvw : ∀ i, K.mkQ (v i) = K.mkQ (w i)) : f v = f w := by
  classical
  have hs : ∀ s : Finset (Fin n), f (s.piecewise v w) = f w := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.piecewise_empty]
    | @insert i s his ih =>
      rw [Finset.piecewise_insert]
      rw [map_update_of_mkQ_eq K f hK (s.piecewise v w) i (v i) (w i) (hvw i)]
      have hu : Function.update (s.piecewise v w) i (w i) = s.piecewise v w :=
        Function.update_eq_self_iff.mpr (Finset.piecewise_eq_of_notMem s v w his).symm
      rw [hu]
      exact ih
  simpa only [Finset.piecewise_univ] using hs Finset.univ

/-- Descend a finite alternating map through the native module quotient.
The relation condition is verified for wedging with `da` at its use below. -/
def liftQuotientFin (K : Submodule R M) (f : M [⋀^Fin n]→ₗ[R] N)
    (hK : ∀ (v : Fin n → M) (i : Fin n), v i ∈ K → f v = 0) :
    (M ⧸ K) [⋀^Fin n]→ₗ[R] N := by
  classical
  let rep : (M ⧸ K) → M := Function.surjInv K.mkQ_surjective
  have hrep : ∀ x, K.mkQ (rep x) = x := Function.rightInverse_surjInv K.mkQ_surjective
  refine
    { toFun := fun v => f (rep ∘ v)
      map_update_add' := ?_
      map_update_smul' := ?_
      map_eq_zero_of_eq' := ?_ }
  · intro _ v i x y
    simp only [Function.comp_update]
    have he : K.mkQ (rep (x + y)) = K.mkQ (rep x + rep y) := by
      rw [hrep, map_add, hrep, hrep]
    rw [map_update_of_mkQ_eq K f hK (rep ∘ v) i _ _ he, f.map_update_add]
  · intro _ v i r x
    simp only [Function.comp_update]
    have he : K.mkQ (rep (r • x)) = K.mkQ (r • rep x) := by
      rw [hrep, map_smul, hrep]
    rw [map_update_of_mkQ_eq K f hK (rep ∘ v) i _ _ he, f.map_update_smul]
  · intro v i j hij hne
    exact f.map_eq_zero_of_eq (rep ∘ v) (congrArg rep hij) hne

/-- The quotient lift retains the original alternating map on every actual wedge tuple. -/
@[simp]
theorem liftQuotientFin_mkQ (K : Submodule R M) (f : M [⋀^Fin n]→ₗ[R] N)
    (hK : ∀ (v : Fin n → M) (i : Fin n), v i ∈ K → f v = 0) (v : Fin n → M) :
    liftQuotientFin K f hK (K.mkQ ∘ v) = f v := by
  classical
  change f (fun i => Function.surjInv K.mkQ_surjective (K.mkQ (v i))) = f v
  apply map_eq_of_mkQ_eq K f hK
  intro i
  exact Function.rightInverse_surjInv K.mkQ_surjective (K.mkQ (v i))

end AlternatingMap

namespace KaehlerDifferential

variable {Λ R : Type*} [CommRing Λ] [CommRing R] [Algebra Λ R] (a : R)

local notation "P" => KaehlerDifferential Λ R
local notation "L" => Submodule.span R ({D Λ R a} : Set P)
local notation "Pbar" => P ⧸ L

/-- Append the original relation differential, with the reviewed wedge order. -/
def pureDegreePRelationAlternating (n : ℕ) : P [⋀^Fin n]→ₗ[R] (⋀[R]^(n + 1) P) :=
  ((-1 : ℤ) ^ n) • (exteriorPower.ιMulti R (n + 1)).curryLeft (D Λ R a)

theorem pureDegreePRelationAlternating_apply (n : ℕ) (v : Fin n → P) :
    pureDegreePRelationAlternating (Λ := Λ) a n v =
      exteriorPower.ιMulti R (n + 1) (Fin.snoc v (D Λ R a)) := by
  change ((-1 : ℤ) ^ n) •
    exteriorPower.ιMulti R (n + 1) (Matrix.vecCons (D Λ R a) v) = _
  simpa only [Fin.val_last, Fin.insertNth_last'] using
    ((exteriorPower.ιMulti R (n + 1)).map_insertNth (Fin.last n) (D Λ R a) v).symm

/-- A relation in any input produces a repeated `da`, including in characteristic two. -/
theorem pureDegreePRelationAlternating_relation (n : ℕ) (v : Fin n → P)
    (i : Fin n) (hi : v i ∈ L) : pureDegreePRelationAlternating (Λ := Λ) a n v = 0 := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hi
  have hv : v = Function.update v i (r • D Λ R a) := by
    rw [hr, Function.update_eq_self]
  have hz : pureDegreePRelationAlternating (Λ := Λ) a n
      (Function.update v i (D Λ R a)) = 0 := by
    change ((-1 : ℤ) ^ n) • exteriorPower.ιMulti R (n + 1)
      (Matrix.vecCons (D Λ R a) (Function.update v i (D Λ R a))) = 0
    have hne : (0 : Fin (n + 1)) ≠ i.succ := by
      intro heq
      have hval : (0 : ℕ) = (i : ℕ) + 1 := congrArg Fin.val heq
      omega
    have he : exteriorPower.ιMulti R (n + 1)
        (Matrix.vecCons (D Λ R a) (Function.update v i (D Λ R a))) = 0 :=
      (exteriorPower.ιMulti R (n + 1)).map_eq_zero_of_eq _
        (i := 0) (j := i.succ) (by simp) hne
    rw [he, smul_zero]
  calc
    pureDegreePRelationAlternating (Λ := Λ) a n v =
        pureDegreePRelationAlternating (Λ := Λ) a n
          (Function.update v i (r • D Λ R a)) := congrArg _ hv
    _ = r • pureDegreePRelationAlternating (Λ := Λ) a n
        (Function.update v i (D Λ R a)) :=
      (pureDegreePRelationAlternating (Λ := Λ) a n).map_update_smul v i r (D Λ R a)
    _ = 0 := by rw [hz, smul_zero]

/-- The actual relation quotient carries the descended alternating map. -/
def pureDegreePRelationQuotientAlternating (n : ℕ) :
    Pbar [⋀^Fin n]→ₗ[R] (⋀[R]^(n + 1) P) :=
  AlternatingMap.liftQuotientFin L (pureDegreePRelationAlternating (Λ := Λ) a n)
    (pureDegreePRelationAlternating_relation (Λ := Λ) a n)

/-- The descended map out of the native exterior power of the relation quotient. -/
def pureDegreePRelationExterior (n : ℕ) :
    (⋀[R]^n Pbar) →ₗ[R] (⋀[R]^(n + 1) P) :=
  exteriorPower.alternatingMapLinearEquiv (pureDegreePRelationQuotientAlternating (Λ := Λ) a n)

@[simp]
theorem pureDegreePRelationExterior_ιMulti (n : ℕ) (v : Fin n → P) :
    pureDegreePRelationExterior (Λ := Λ) a n (exteriorPower.ιMulti R n ((Submodule.mkQ L) ∘ v)) =
      exteriorPower.ιMulti R (n + 1) (Fin.snoc v (D Λ R a)) := by
  rw [pureDegreePRelationExterior, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change AlternatingMap.liftQuotientFin L (pureDegreePRelationAlternating (Λ := Λ) a n)
    (pureDegreePRelationAlternating_relation (Λ := Λ) a n) ((Submodule.mkQ L) ∘ v) = _
  rw [AlternatingMap.liftQuotientFin_mkQ, pureDegreePRelationAlternating_apply]

variable {S : Type*} [CommRing S] [Algebra R S]

local notation "E" => S ⊗[R] Pbar

/-- Tensor and grade the actual exterior map before the coefficient extraction. -/
def pureDegreePTensorRelationAlternating (n : ℕ) :
    E [⋀^Fin n]→ₗ[S] (S ⊗[R] (⋀[R]^(n + 1) P)) :=
  LinearMap.compAlternatingMap
    (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := S) (M := S))
      ((pureDegreePRelationExterior (Λ := Λ) a n).comp (ExteriorAlgebra.degreeComponent n)))
    (LinearMap.compAlternatingMap
      (ExteriorAlgebra.tensorMap (R := R) (S := S) (M := Pbar)).toLinearMap
      (ExteriorAlgebra.ιMulti S n))

theorem pureDegreePTensorRelationAlternating_one_tmul (n : ℕ) (v : Fin n → P) :
    pureDegreePTensorRelationAlternating (Λ := Λ) (S := S) a n
      (fun i => 1 ⊗ₜ[R] (Submodule.mkQ L) (v i)) =
        1 ⊗ₜ[R] exteriorPower.ιMulti R (n + 1) (Fin.snoc v (D Λ R a)) := by
  change TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := S) (M := S))
    ((pureDegreePRelationExterior (Λ := Λ) a n).comp (ExteriorAlgebra.degreeComponent n))
      (ExteriorAlgebra.tensorMap
        (ExteriorAlgebra.ιMulti S n (fun i => 1 ⊗ₜ[R] (Submodule.mkQ L) (v i)))) = _
  rw [ExteriorAlgebra.tensorMap_ιMulti_one, TensorProduct.AlgebraTensorModule.map_tmul,
    LinearMap.id_apply, LinearMap.comp_apply, ExteriorAlgebra.degreeComponent_ιMulti]
  exact congrArg (fun η : ⋀[R]^(n + 1) P => (1 : S) ⊗ₜ[R] η)
    (pureDegreePRelationExterior_ιMulti (Λ := Λ) a n v)

variable [Algebra Λ S] [IsScalarTower Λ R S] {p : ℕ} [CharP R p]
variable {a}

/-- The insertion map on the actual differential module, retaining the root-last sign. -/
def pureDegreePExteriorAlternating
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ) :
    (KaehlerDifferential Λ S) [⋀^Fin (n + 1)]→ₗ[S] (S ⊗[R] (⋀[R]^(n + 1) P)) :=
  let b : (E × S) [⋀^Fin n]→ₗ[S] (S ⊗[R] (⋀[R]^(n + 1) P)) :=
    AlternatingMap.compLinearMap (pureDegreePTensorRelationAlternating (Λ := Λ) (S := S) a n)
      (LinearMap.fst S E S)
  let c : (E × S) →ₗ[S] ((E × S) [⋀^Fin n]→ₗ[S] (S ⊗[R] (⋀[R]^(n + 1) P))) :=
    (LinearMap.toSpanSingleton S _ b).comp (LinearMap.snd S E S)
  AlternatingMap.compLinearMap (((-1 : ℤ) ^ n) • AlternatingMap.alternatizeUncurryFin c)
    (pureDegreePDifferentialSplit (Λ := Λ) h)

/-- Lift the insertion map through the native exterior universal property. -/
def pureDegreePExteriorLift
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ) :
    (⋀[S]^(n + 1) (KaehlerDifferential Λ S)) →ₗ[S] (S ⊗[R] (⋀[R]^(n + 1) P)) :=
  exteriorPower.alternatingMapLinearEquiv (pureDegreePExteriorAlternating (Λ := Λ) h n)

/-- Apply the already constructed power-basis coefficient to a tensor coefficient. -/
def pureDegreePTensorCoeff
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (N : Type*) [AddCommGroup N] [Module R N] : S ⊗[R] N →ₗ[R] N :=
  (TensorProduct.lid R N).toLinearMap.comp
    (TensorProduct.map (pureDegreePCoeff h) (LinearMap.id (R := R) (M := N)))

omit [CharP R p] in
@[simp]
theorem pureDegreePTensorCoeff_tmul
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (N : Type*) [AddCommGroup N] [Module R N] (s : S) (v : N) :
    pureDegreePTensorCoeff h N (s ⊗ₜ[R] v) = pureDegreePCoeff h s • v := by
  calc
    pureDegreePTensorCoeff h N (s ⊗ₜ[R] v) =
        TensorProduct.lid R N (pureDegreePCoeff h s ⊗ₜ[R] v) := by
      rw [pureDegreePTensorCoeff, LinearMap.comp_apply, TensorProduct.map_tmul,
        LinearMap.id_apply]
      exact congrFun (LinearEquiv.coe_toLinearMap (TensorProduct.lid R N)) _
    _ = pureDegreePCoeff h s • v := TensorProduct.lid_tmul v (pureDegreePCoeff h s)

/-- The actual positive-degree differential trace: insertion followed by the original epsilon. -/
def pureDegreePTraceExterior
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ) :
    (⋀[S]^(n + 1) (KaehlerDifferential Λ S)) →ₗ[R] (⋀[R]^(n + 1) P) :=
  (pureDegreePTensorCoeff h (⋀[R]^(n + 1) P)).comp
    ((pureDegreePExteriorLift (Λ := Λ) h n).restrictScalars R)

/-- The alternating insertion formula uses the actual two differential components. -/
theorem pureDegreePExteriorAlternating_apply
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    (v : Fin (n + 1) → KaehlerDifferential Λ S) :
    pureDegreePExteriorAlternating (Λ := Λ) h n v =
      ((-1 : ℤ) ^ n) • ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        (pureDegreePRootDifferential (Λ := Λ) h (v i) •
          pureDegreePTensorRelationAlternating (Λ := Λ) (S := S) a n
            (fun j => pureDegreePCoefficientDifferential (Λ := Λ) h (v (i.succAbove j)))) := by
  let b : (E × S) [⋀^Fin n]→ₗ[S] (S ⊗[R] (⋀[R]^(n + 1) P)) :=
    AlternatingMap.compLinearMap (pureDegreePTensorRelationAlternating (Λ := Λ) (S := S) a n)
      (LinearMap.fst S E S)
  let c : (E × S) →ₗ[S] ((E × S) [⋀^Fin n]→ₗ[S] (S ⊗[R] (⋀[R]^(n + 1) P))) :=
    (LinearMap.toSpanSingleton S _ b).comp (LinearMap.snd S E S)
  change ((-1 : ℤ) ^ n) • AlternatingMap.alternatizeUncurryFin c
    (pureDegreePDifferentialSplit (Λ := Λ) h ∘ v) = _
  exact congrArg (fun x => ((-1 : ℤ) ^ n) • x)
    (AlternatingMap.alternatizeUncurryFin_apply c (pureDegreePDifferentialSplit (Λ := Λ) h ∘ v))

/-- With base differentials first, only the final root component contributes. -/
theorem pureDegreePExteriorAlternating_snoc
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    (v : Fin n → P) (ω : KaehlerDifferential Λ S) :
    pureDegreePExteriorAlternating (Λ := Λ) h n
      (Fin.snoc (fun i => map Λ Λ R S (v i)) ω) =
        pureDegreePRootDifferential (Λ := Λ) h ω ⊗ₜ[R]
          exteriorPower.ιMulti R (n + 1) (Fin.snoc v (D Λ R a)) := by
  classical
  rw [pureDegreePExteriorAlternating_apply, Finset.sum_eq_single (Fin.last n)]
  · rw [Fin.snoc_last]
    have hv : (fun j : Fin n => pureDegreePCoefficientDifferential (Λ := Λ) h
        (Fin.snoc (α := fun _ : Fin (n + 1) => KaehlerDifferential Λ S)
          (fun i => map Λ Λ R S (v i)) ω ((Fin.last n).succAbove j))) =
        (fun j => 1 ⊗ₜ[R] (Submodule.mkQ L) (v j)) := by
      funext j
      rw [Fin.succAbove_last_apply, Fin.snoc_castSucc, pureDegreePCoefficientDifferential_map]
    rw [hv, pureDegreePTensorRelationAlternating_one_tmul]
    change ((-1 : ℤ) ^ n) • (((-1 : ℤ) ^ n) •
      (pureDegreePRootDifferential (Λ := Λ) h ω •
        (1 ⊗ₜ[R] exteriorPower.ιMulti R (n + 1) (Fin.snoc v (D Λ R a))))) = _
    have hs : ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by
      rw [← pow_add]
      exact (show Even (n + n) from ⟨n, rfl⟩).neg_one_pow
    rw [smul_smul, hs, one_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · intro i _ hi
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      exact (hi rfl).elim
    · intro _
      rw [Fin.snoc_castSucc, pureDegreePRootDifferential_map, zero_smul, smul_zero]
  · intro hi
    exact (hi (Finset.mem_univ (Fin.last n))).elim

/-- Pulled-up differential tuples have zero insertion component. -/
theorem pureDegreePExteriorAlternating_map
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    (v : Fin (n + 1) → P) :
    pureDegreePExteriorAlternating (Λ := Λ) h n (fun i => map Λ Λ R S (v i)) = 0 := by
  rw [pureDegreePExteriorAlternating_apply]
  simp only [pureDegreePRootDifferential_map, zero_smul, smul_zero,
    Finset.sum_const_zero]

/-- The trace on original wedges is its constructed insertion map followed by epsilon. -/
theorem pureDegreePTraceExterior_ιMulti
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    (v : Fin (n + 1) → KaehlerDifferential Λ S) :
    pureDegreePTraceExterior (Λ := Λ) h n (exteriorPower.ιMulti S (n + 1) v) =
      pureDegreePTensorCoeff h (⋀[R]^(n + 1) P)
        (pureDegreePExteriorAlternating (Λ := Λ) h n v) := by
  change pureDegreePTensorCoeff h (⋀[R]^(n + 1) P)
    (exteriorPower.alternatingMapLinearEquiv (pureDegreePExteriorAlternating (Λ := Λ) h n)
      (exteriorPower.ιMulti S (n + 1) v)) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- The original exterior trace has the one-form projection formula with the base forms first. -/
theorem pureDegreePTraceExterior_snoc
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    (v : Fin n → P) (ω : KaehlerDifferential Λ S) :
    pureDegreePTraceExterior (Λ := Λ) h n
      (exteriorPower.ιMulti S (n + 1) (Fin.snoc (fun i => map Λ Λ R S (v i)) ω)) =
        exteriorPower.ιMulti R (n + 1) (Fin.snoc v (pureDegreePTraceOne Λ h ω)) := by
  rw [pureDegreePTraceExterior_ιMulti, pureDegreePExteriorAlternating_snoc,
    pureDegreePTensorCoeff_tmul, pureDegreePTraceOne_apply]
  change pureDegreePCoeff h (pureDegreePRootDifferential (Λ := Λ) h ω) •
    exteriorPower.ιMulti R (n + 1) (Fin.snoc v (D Λ R a)) =
      exteriorPower.ιMulti R (n + 1)
        (Fin.snoc v (pureDegreePCoeff h (pureDegreePRootDifferential (Λ := Λ) h ω) • D Λ R a))
  symm
  simpa only [Fin.update_snoc_last] using
    (exteriorPower.ιMulti R (n + 1)).map_update_smul (Fin.snoc v (D Λ R a)) (Fin.last n)
      (pureDegreePCoeff h (pureDegreePRootDifferential (Λ := Λ) h ω)) (D Λ R a)

/-- The reviewed power-basis formula is an equation on the actual exterior power. -/
theorem pureDegreePTraceExterior_root_pow [Fact p.Prime]
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    (v : Fin n → P) {i : ℕ} (hi : i < p) :
    pureDegreePTraceExterior (Λ := Λ) h n
      (exteriorPower.ιMulti S (n + 1)
        (Fin.snoc (fun j => map Λ Λ R S (v j)) (h.root ^ i • D Λ S h.root))) =
      if i = p - 1 then exteriorPower.ιMulti R (n + 1) (Fin.snoc v (D Λ R a)) else 0 := by
  rw [pureDegreePTraceExterior_snoc, pureDegreePTraceOne_root_pow_smul_D Λ h hi]
  split_ifs with he
  · rfl
  · exact (exteriorPower.ιMulti R (n + 1)).map_coord_zero
      (Fin.last n) (Fin.snoc_last ..)

/-- Every original S-multiple of a pulled-up wedge is killed. -/
theorem pureDegreePTraceExterior_smul_map_wedge
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    (s : S) (v : Fin (n + 1) → P) :
    pureDegreePTraceExterior (Λ := Λ) h n
      (s • exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i))) = 0 := by
  change pureDegreePTensorCoeff h (⋀[R]^(n + 1) P)
    (pureDegreePExteriorLift (Λ := Λ) h n
      (s • exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i)))) = 0
  rw [map_smul]
  change pureDegreePTensorCoeff h (⋀[R]^(n + 1) P)
    (s • exteriorPower.alternatingMapLinearEquiv (pureDegreePExteriorAlternating (Λ := Λ) h n)
      (exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i)))) = 0
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    pureDegreePExteriorAlternating_map, smul_zero, map_zero]

end KaehlerDifferential

namespace KaehlerDifferential

variable {Λ R S : Type*} [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
  {p : ℕ} [CharP R p] {a : R}

local notation "P" => KaehlerDifferential Λ R
local notation "L" => Submodule.span R ({D Λ R a} : Set P)
local notation "Pbar" => P ⧸ L
local notation "E" => S ⊗[R] Pbar

/-- The original base differentials and root differential span the original module over S. -/
theorem pureDegreeP_span_map_root
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    Submodule.span S (Set.range (map Λ Λ R S) ∪ {D Λ S h.root}) = ⊤ := by
  let V := Submodule.span S (Set.range (map Λ Λ R S) ∪ {D Λ S h.root})
  have hbase : ∀ e : E, pureDegreePBaseDifferential (Λ := Λ) h e ∈ V := by
    intro e
    induction e using TensorProduct.inductionOn with
    | tmul s η =>
      refine Submodule.Quotient.induction_on L η ?_
      intro θ
      have hθ : pureDegreePQuotientDifferential (Λ := Λ) h (Submodule.Quotient.mk θ) =
          map Λ Λ R S θ := Submodule.liftQ_apply _ _ _
      rw [pureDegreePBaseDifferential_tmul, hθ]
      exact Submodule.smul_mem _ s (Submodule.subset_span (Or.inl ⟨θ, rfl⟩))
    | add e e' he he' =>
      rw [map_add]
      exact Submodule.add_mem _ he he'
  have hroot : D Λ S h.root ∈ V := Submodule.subset_span (Or.inr (by simp))
  apply Submodule.eq_top_iff'.mpr
  intro ω
  obtain ⟨⟨e, s⟩, rfl⟩ := pureDegreePDifferentialMerge_surjective (Λ := Λ) h ω
  change pureDegreePBaseDifferential (Λ := Λ) h e + s • D Λ S h.root ∈ V
  exact Submodule.add_mem _ (hbase e) (Submodule.smul_mem _ s hroot)

/-- The two kinds of original wedges determine a restricted-linear exterior trace. -/
theorem pureDegreePTraceExterior_ext
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    {N : Type*} [AddCommGroup N] [Module R N]
    (f g : (⋀[S]^(n + 1) (KaehlerDifferential Λ S)) →ₗ[R] N)
    (hbase : ∀ (s : S) (v : Fin (n + 1) → P),
      f (s • exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i))) =
        g (s • exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i))))
    (hroot : ∀ (s : S) (v : Fin n → P),
      f (s • exteriorPower.ιMulti S (n + 1)
        (Fin.snoc (fun i => map Λ Λ R S (v i)) (D Λ S h.root))) =
      g (s • exteriorPower.ιMulti S (n + 1)
        (Fin.snoc (fun i => map Λ Λ R S (v i)) (D Λ S h.root)))) : f = g := by
  classical
  apply exteriorPower.restrictLinearMap_ext_of_span (n + 1)
    (Set.range (map Λ Λ R S) ∪ {D Λ S h.root}) (pureDegreeP_span_map_root (Λ := Λ) h)
  intro v hv s
  have hpre : ∀ i, v i ≠ D Λ S h.root → ∃ η : P, map Λ Λ R S η = v i := by
    intro i hi
    rcases hv (Set.mem_range_self i) with he | he
    · exact he
    · exact (hi (Set.mem_singleton_iff.mp he)).elim
  by_cases hz : ∃ i, v i = D Λ S h.root
  · obtain ⟨i, hi⟩ := hz
    by_cases hz' : ∃ j, j ≠ i ∧ v j = D Λ S h.root
    · obtain ⟨j, hji, hj⟩ := hz'
      have he : exteriorPower.ιMulti S (n + 1) v = 0 :=
        (exteriorPower.ιMulti S (n + 1)).map_eq_zero_of_eq v (hi.trans hj.symm) hji.symm
      rw [he, smul_zero, map_zero, map_zero]
    · have hsingle : ∀ j, j ≠ i → v j ≠ D Λ S h.root := by
        intro j hji hj
        exact hz' ⟨j, hji, hj⟩
      by_cases hilast : i = Fin.last n
      · subst i
        choose η hη using fun j : Fin n => hpre j.castSucc (hsingle _ (Fin.castSucc_lt_last j).ne)
        have he : v = Fin.snoc (fun j => map Λ Λ R S (η j)) (D Λ S h.root) := by
          funext j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · rw [Fin.snoc_last]
            exact hi
          · rw [Fin.snoc_castSucc]
            exact (hη k).symm
        rw [he]
        exact hroot s η
      · let σ := Equiv.swap i (Fin.last n)
        have hidx : ∀ j : Fin n, σ j.castSucc ≠ i := by
          intro j he
          apply (Fin.castSucc_lt_last j).ne
          apply σ.injective
          exact he.trans (Equiv.swap_apply_right i (Fin.last n)).symm
        choose η hη using fun j : Fin n => hpre (σ j.castSucc) (hsingle _ (hidx j))
        have he : v ∘ σ = Fin.snoc (fun j => map Λ Λ R S (η j)) (D Λ S h.root) := by
          funext j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · rw [Function.comp_apply, Fin.snoc_last]
            change v (Equiv.swap i (Fin.last n) (Fin.last n)) = D Λ S h.root
            rw [Equiv.swap_apply_right]
            exact hi
          · rw [Function.comp_apply, Fin.snoc_castSucc]
            exact (hη k).symm
        have hfg := hroot s η
        rw [← he, (exteriorPower.ιMulti S (n + 1)).map_swap v hilast,
          smul_neg, map_neg, map_neg] at hfg
        exact neg_inj.mp hfg
  · choose η hη using fun i => hpre i (fun hi => hz ⟨i, hi⟩)
    have he : v = fun i => map Λ Λ R S (η i) := funext fun i => (hη i).symm
    rw [he]
    exact hbase s η

end KaehlerDifferential

namespace KaehlerDifferential

variable (Λ R S : Type*) [CommRing Λ] [CommRing R] [CommRing S]
  [Algebra Λ R] [Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]

/-- The actual Kähler map on native exterior powers, with its original source scalars. -/
def mapExterior (n : ℕ) :
    (⋀[R]^n (KaehlerDifferential Λ R)) →ₗ[R] (⋀[S]^n (KaehlerDifferential Λ S)) :=
  exteriorPower.mapAlgebra (S := S) n (map Λ Λ R S)

/-- The actual pulled-up exterior forms, retaining the original tensor product and scalar action. -/
def mapExteriorBaseChange (n : ℕ) :
    S ⊗[R] (⋀[R]^n (KaehlerDifferential Λ R)) →ₗ[S]
      (⋀[S]^n (KaehlerDifferential Λ S)) :=
  (mapExterior Λ R S n).liftBaseChange S

@[simp]
theorem mapExteriorBaseChange_tmul (n : ℕ) (s : S)
    (v : ⋀[R]^n (KaehlerDifferential Λ R)) :
    mapExteriorBaseChange Λ R S n (s ⊗ₜ[R] v) = s • mapExterior Λ R S n v :=
  LinearMap.liftBaseChange_tmul _ _ _ _

@[simp]
theorem mapExterior_ιMulti (n : ℕ) (v : Fin n → KaehlerDifferential Λ R) :
    mapExterior Λ R S n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => map Λ Λ R S (v i)) :=
  exteriorPower.mapAlgebra_ιMulti n (map Λ Λ R S) v

theorem mapExterior_snoc (n : ℕ) (v : Fin n → KaehlerDifferential Λ R)
    (ω : KaehlerDifferential Λ R) :
    mapExterior Λ R S (n + 1) (exteriorPower.ιMulti R (n + 1) (Fin.snoc v ω)) =
      exteriorPower.ιMulti S (n + 1)
        (Fin.snoc (fun i => map Λ Λ R S (v i)) (map Λ Λ R S ω)) := by
  rw [mapExterior_ιMulti]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- Exterior differentials use the actual module localization, proved through tensor base change. -/
theorem mapExterior_isLocalizedModule (U : Submonoid R) [IsLocalization U S] (n : ℕ) :
    IsLocalizedModule U (mapExterior Λ R S n) := by
  let : IsLocalizedModule U (map Λ Λ R S) :=
    KaehlerDifferential.isLocalizedModule_map (R := Λ) (S := R) (T := S) U
  exact exteriorPower.isLocalizedModule_mapAlgebra U n (map Λ Λ R S)

variable {Λ R S}
variable {T : Type*} [CommRing T] [Algebra S T] [Algebra R T] [Algebra Λ T]
  [IsScalarTower R S T] [IsScalarTower Λ S T] [IsScalarTower Λ R T]

private theorem exterior_map_tower_apply (η : KaehlerDifferential Λ R) :
    map Λ Λ S T (map Λ Λ R S η) = map Λ Λ R T η := by
  have he : ((map Λ Λ S T).restrictScalars R).comp (map Λ Λ R S) = map Λ Λ R T := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro r
    change map Λ Λ S T (map Λ Λ R S (D Λ R r)) = map Λ Λ R T (D Λ R r)
    simp only [map_D, ← IsScalarTower.algebraMap_apply R S T]
  exact LinearMap.congr_fun he η

theorem mapExterior_base_tower (n : ℕ) (v : Fin n → KaehlerDifferential Λ R) :
    mapExterior Λ S T n
      (exteriorPower.ιMulti S n (fun i => map Λ Λ R S (v i))) =
        exteriorPower.ιMulti T n (fun i => map Λ Λ R T (v i)) := by
  rw [mapExterior_ιMulti]
  congr 1
  funext i
  exact exterior_map_tower_apply (v i)

theorem mapExterior_snoc_tower (n : ℕ) (v : Fin n → KaehlerDifferential Λ R)
    (ω : KaehlerDifferential Λ S) :
    mapExterior Λ S T (n + 1)
      (exteriorPower.ιMulti S (n + 1) (Fin.snoc (fun i => map Λ Λ R S (v i)) ω)) =
        exteriorPower.ιMulti T (n + 1)
          (Fin.snoc (fun i => map Λ Λ R T (v i)) (map Λ Λ S T ω)) := by
  rw [mapExterior_snoc]
  congr 1
  congr 1
  funext i
  exact exterior_map_tower_apply (v i)

section PureDegreeP

variable {p : ℕ} [Fact p.Prime] [CharP R p] {a b : R}

/-- Coordinate independence is an equality through the actual map on exterior differentials. -/
theorem pureDegreePTraceExterior_naturality
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    (h' : IsAdjoinRootMonic T ((X : R[X]) ^ p - C b)) (n : ℕ) :
    (pureDegreePTraceExterior (Λ := Λ) h' n).comp
        ((mapExterior Λ S T (n + 1)).restrictScalars R) =
      pureDegreePTraceExterior (Λ := Λ) h n := by
  apply pureDegreePTraceExterior_ext (Λ := Λ) h n
  · intro s v
    change pureDegreePTraceExterior (Λ := Λ) h' n
      (mapExterior Λ S T (n + 1)
        (s • exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i)))) = _
    rw [map_smul, mapExterior_base_tower, ← IsScalarTower.algebraMap_smul T s,
      pureDegreePTraceExterior_smul_map_wedge, pureDegreePTraceExterior_smul_map_wedge]
  · intro s v
    have he : s • exteriorPower.ιMulti S (n + 1)
        (Fin.snoc (fun i => map Λ Λ R S (v i)) (D Λ S h.root)) =
        exteriorPower.ιMulti S (n + 1)
          (Fin.snoc (fun i => map Λ Λ R S (v i)) (s • D Λ S h.root)) :=
      ((exteriorPower.ιMulti S (n + 1)).toMultilinearMap.snoc_smul
        (fun i => map Λ Λ R S (v i)) s (D Λ S h.root)).symm
    change pureDegreePTraceExterior (Λ := Λ) h' n
      (mapExterior Λ S T (n + 1) _) = pureDegreePTraceExterior (Λ := Λ) h n _
    rw [he, mapExterior_snoc_tower, pureDegreePTraceExterior_snoc,
      pureDegreePTraceExterior_snoc]
    exact congrArg (fun ω => exteriorPower.ιMulti R (n + 1) (Fin.snoc v ω))
      (LinearMap.congr_fun (pureDegreePTraceOne_naturality Λ h h') (s • D Λ S h.root))

section BaseChange

variable {R' : Type*} [CommRing R'] [Algebra R R'] [Algebra R' T]
  [Algebra Λ R'] [IsScalarTower Λ R R'] [IsScalarTower Λ R' T]
  [IsScalarTower R R' T] [CharP R' p]

/-- The scalar-square equation for the actual exterior traces; no naturality input is assumed. -/
theorem pureDegreePTraceExterior_baseChange
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    {b' : R'} (h' : IsAdjoinRootMonic T ((X : R'[X]) ^ p - C b')) (n : ℕ) :
    ((pureDegreePTraceExterior (Λ := Λ) h' n).restrictScalars R).comp
        ((mapExterior Λ S T (n + 1)).restrictScalars R) =
      (mapExterior Λ R R' (n + 1)).comp (pureDegreePTraceExterior (Λ := Λ) h n) := by
  apply pureDegreePTraceExterior_ext (Λ := Λ) h n
  · intro s v
    change pureDegreePTraceExterior (Λ := Λ) h' n
      (mapExterior Λ S T (n + 1)
        (s • exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i)))) =
      mapExterior Λ R R' (n + 1)
        (pureDegreePTraceExterior (Λ := Λ) h n
          (s • exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i))))
    rw [pureDegreePTraceExterior_smul_map_wedge, map_zero, map_smul,
      mapExterior_base_tower, ← IsScalarTower.algebraMap_smul T s]
    have he : (fun i => map Λ Λ R T (v i)) =
        (fun i => map Λ Λ R' T (map Λ Λ R R' (v i))) := by
      funext i
      exact (exterior_map_tower_apply (R := R) (S := R') (T := T) (v i)).symm
    rw [he]
    exact pureDegreePTraceExterior_smul_map_wedge (Λ := Λ) h' n
      (algebraMap S T s) (fun i => map Λ Λ R R' (v i))
  · intro s v
    have he : s • exteriorPower.ιMulti S (n + 1)
        (Fin.snoc (fun i => map Λ Λ R S (v i)) (D Λ S h.root)) =
        exteriorPower.ιMulti S (n + 1)
          (Fin.snoc (fun i => map Λ Λ R S (v i)) (s • D Λ S h.root)) :=
      ((exteriorPower.ιMulti S (n + 1)).toMultilinearMap.snoc_smul
        (fun i => map Λ Λ R S (v i)) s (D Λ S h.root)).symm
    change pureDegreePTraceExterior (Λ := Λ) h' n
      (mapExterior Λ S T (n + 1) _) =
        mapExterior Λ R R' (n + 1) (pureDegreePTraceExterior (Λ := Λ) h n _)
    rw [he, mapExterior_snoc_tower, pureDegreePTraceExterior_snoc, mapExterior_snoc]
    have hbase : (fun i => map Λ Λ R T (v i)) =
        (fun i => map Λ Λ R' T (map Λ Λ R R' (v i))) := by
      funext i
      exact (exterior_map_tower_apply (R := R) (S := R') (T := T) (v i)).symm
    rw [hbase, pureDegreePTraceExterior_snoc]
    exact congrArg (fun ω => exteriorPower.ιMulti R' (n + 1)
      (Fin.snoc (fun i => map Λ Λ R R' (v i)) ω))
      (LinearMap.congr_fun (pureDegreePTraceOne_baseChange Λ h h') (s • D Λ S h.root))

/-- The exterior trace on the actual localized algebra is the native localized linear map. -/
theorem pureDegreePTraceExterior_localization (U : Submonoid R)
    [IsLocalization U R'] [IsLocalization (Algebra.algebraMapSubmonoid S U) T]
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a))
    {b' : R'} (h' : IsAdjoinRootMonic T ((X : R'[X]) ^ p - C b')) (n : ℕ) :
    let _ : IsLocalizedModule (Algebra.algebraMapSubmonoid S U)
        (mapExterior Λ S T (n + 1)) :=
      mapExterior_isLocalizedModule Λ S T (Algebra.algebraMapSubmonoid S U) (n + 1)
    let _ : IsLocalizedModule U ((mapExterior Λ S T (n + 1)).restrictScalars R) :=
      IsLocalizedModule.restrictScalars U (mapExterior Λ S T (n + 1))
    let _ : IsLocalizedModule U (mapExterior Λ R R' (n + 1)) :=
      mapExterior_isLocalizedModule Λ R R' U (n + 1)
    IsLocalizedModule.mapExtendScalars U
      ((mapExterior Λ S T (n + 1)).restrictScalars R)
      (mapExterior Λ R R' (n + 1)) R' (pureDegreePTraceExterior (Λ := Λ) h n) =
        pureDegreePTraceExterior (Λ := Λ) h' n := by
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid S U)
      (mapExterior Λ S T (n + 1)) :=
    mapExterior_isLocalizedModule Λ S T (Algebra.algebraMapSubmonoid S U) (n + 1)
  let : IsLocalizedModule U ((mapExterior Λ S T (n + 1)).restrictScalars R) :=
    IsLocalizedModule.restrictScalars U (mapExterior Λ S T (n + 1))
  let : IsLocalizedModule U (mapExterior Λ R R' (n + 1)) :=
    mapExterior_isLocalizedModule Λ R R' U (n + 1)
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext U
    ((mapExterior Λ S T (n + 1)).restrictScalars R) (mapExterior Λ R R' (n + 1))
  apply LinearMap.ext
  intro ω
  change IsLocalizedModule.map U ((mapExterior Λ S T (n + 1)).restrictScalars R)
      (mapExterior Λ R R' (n + 1)) (pureDegreePTraceExterior (Λ := Λ) h n)
        (((mapExterior Λ S T (n + 1)).restrictScalars R) ω) =
      pureDegreePTraceExterior (Λ := Λ) h' n
        (((mapExterior Λ S T (n + 1)).restrictScalars R) ω)
  exact (IsLocalizedModule.map_apply U
      ((mapExterior Λ S T (n + 1)).restrictScalars R)
      (mapExterior Λ R R' (n + 1)) (pureDegreePTraceExterior (Λ := Λ) h n) ω).trans
    (LinearMap.congr_fun (pureDegreePTraceExterior_baseChange h h' n) ω).symm

end BaseChange

end PureDegreeP

section One

variable {p : ℕ} [CharP R p] {a : R}

/-- All S-multiples of arbitrary pulled-up exterior forms are killed. -/
theorem pureDegreePTraceExterior_smul_map
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ) (s : S)
    (v : ⋀[R]^(n + 1) (KaehlerDifferential Λ R)) :
    pureDegreePTraceExterior (Λ := Λ) h n (s • mapExterior Λ R S (n + 1) v) = 0 := by
  have hv : v ∈ Submodule.span R
      (Set.range (exteriorPower.ιMulti R (n + 1) (M := KaehlerDifferential Λ R))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, rfl⟩ := hv
    rw [mapExterior_ιMulti]
    exact pureDegreePTraceExterior_smul_map_wedge (Λ := Λ) h n s w
  | zero => simp
  | add v w _ _ hv hw => rw [map_add, smul_add, map_add, hv, hw, add_zero]
  | smul r v _ hv =>
    rw [(mapExterior Λ R S (n + 1)).map_smul r v, smul_comm s r,
      (pureDegreePTraceExterior (Λ := Λ) h n).map_smul r
        (s • mapExterior Λ R S (n + 1) v), hv, smul_zero]

/-- The entire original map from the tensor product of base forms is annihilated. -/
theorem pureDegreePTraceExterior_mapBaseChange
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ) :
    (pureDegreePTraceExterior (Λ := Λ) h n).comp
      ((mapExteriorBaseChange Λ R S (n + 1)).restrictScalars R) = 0 := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul s v =>
    change pureDegreePTraceExterior (Λ := Λ) h n
      (mapExteriorBaseChange Λ R S (n + 1) (s ⊗ₜ[R] v)) = 0
    rw [mapExteriorBaseChange_tmul, pureDegreePTraceExterior_smul_map]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The reviewed formulas uniquely determine the constructed exterior trace. -/
theorem pureDegreePTraceExterior_unique [Fact p.Prime]
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) (n : ℕ)
    (f : (⋀[S]^(n + 1) (KaehlerDifferential Λ S)) →ₗ[R]
      (⋀[R]^(n + 1) (KaehlerDifferential Λ R)))
    (hbase : ∀ (s : S) (v : Fin (n + 1) → KaehlerDifferential Λ R),
      f (s • exteriorPower.ιMulti S (n + 1) (fun i => map Λ Λ R S (v i))) = 0)
    (hpow : ∀ (v : Fin n → KaehlerDifferential Λ R) i, i < p →
      f (exteriorPower.ιMulti S (n + 1)
        (Fin.snoc (fun j => map Λ Λ R S (v j)) (h.root ^ i • D Λ S h.root))) =
      if i = p - 1 then
        exteriorPower.ιMulti R (n + 1) (Fin.snoc v (D Λ R a)) else 0) :
    f = pureDegreePTraceExterior (Λ := Λ) h n := by
  let : Nontrivial R :=
    CharP.nontrivial_of_char_ne_one (R := R) (Fact.out : p.Prime).ne_one
  apply pureDegreePTraceExterior_ext (Λ := Λ) h n f (pureDegreePTraceExterior (Λ := Λ) h n)
  · intro s v
    rw [hbase, pureDegreePTraceExterior_smul_map_wedge]
  · intro s v
    let j : S →ₗ[R] (⋀[S]^(n + 1) (KaehlerDifferential Λ S)) :=
      (LinearMap.toSpanSingleton S _
        (exteriorPower.ιMulti S (n + 1)
          (Fin.snoc (fun i => map Λ Λ R S (v i)) (D Λ S h.root)))).restrictScalars R
    have he : f.comp j = (pureDegreePTraceExterior (Λ := Λ) h n).comp j := by
      apply h.basis.ext
      intro i
      have hi : (i : ℕ) < p := by
        simpa only [natDegree_X_pow_sub_C] using i.isLt
      change f (h.basis i • exteriorPower.ιMulti S (n + 1)
          (Fin.snoc (fun j => map Λ Λ R S (v j)) (D Λ S h.root))) =
        pureDegreePTraceExterior (Λ := Λ) h n
          (h.basis i • exteriorPower.ιMulti S (n + 1)
            (Fin.snoc (fun j => map Λ Λ R S (v j)) (D Λ S h.root)))
      rw [h.basis_apply]
      have hw : h.root ^ (i : ℕ) • exteriorPower.ιMulti S (n + 1)
          (Fin.snoc (fun j => map Λ Λ R S (v j)) (D Λ S h.root)) =
          exteriorPower.ιMulti S (n + 1)
            (Fin.snoc (fun j => map Λ Λ R S (v j)) (h.root ^ (i : ℕ) • D Λ S h.root)) :=
        ((exteriorPower.ιMulti S (n + 1)).toMultilinearMap.snoc_smul
          (fun j => map Λ Λ R S (v j)) (h.root ^ (i : ℕ)) (D Λ S h.root)).symm
      rw [hw, hpow v i hi, pureDegreePTraceExterior_root_pow h n v hi]
    exact LinearMap.congr_fun he s

/-- Degree one recovers the already constructed trace under the native degree-one equivalences. -/
theorem pureDegreePTraceExterior_one
    (h : IsAdjoinRootMonic S ((X : R[X]) ^ p - C a)) :
    (exteriorPower.oneEquiv R (KaehlerDifferential Λ R)).toLinearMap.comp
      ((pureDegreePTraceExterior (Λ := Λ) h 0).comp
        ((exteriorPower.oneEquiv S (KaehlerDifferential Λ S)).symm.toLinearMap.restrictScalars R)) =
      pureDegreePTraceOne Λ h := by
  apply LinearMap.ext
  intro ω
  let v : Fin 0 → KaehlerDifferential Λ R := Fin.elim0
  have hzero : (0 : Fin 1) = Fin.last 0 := rfl
  have hs : (exteriorPower.oneEquiv S (KaehlerDifferential Λ S)).symm ω =
      exteriorPower.ιMulti S 1
        (Fin.snoc (α := fun _ : Fin 1 => KaehlerDifferential Λ S)
          (fun i => map Λ Λ R S (v i)) ω) := by
    apply (exteriorPower.oneEquiv S (KaehlerDifferential Λ S)).injective
    rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_ιMulti, hzero, Fin.snoc_last]
  change exteriorPower.oneEquiv R (KaehlerDifferential Λ R)
    (pureDegreePTraceExterior (Λ := Λ) h 0
      ((exteriorPower.oneEquiv S (KaehlerDifferential Λ S)).symm ω)) = _
  rw [hs, pureDegreePTraceExterior_snoc, exteriorPower.oneEquiv_ιMulti, hzero, Fin.snoc_last]

end One

end KaehlerDifferential

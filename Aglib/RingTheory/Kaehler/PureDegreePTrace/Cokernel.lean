/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.PureDegreePTrace.IntegralClosure
public import Aglib.RingTheory.MvPowerSeries.FiniteCoefficientExpansion.FractionRing
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Generic differential ranks and the actual integral-trace cokernel

The original presentation derives a nonzero relation differential from equal
actual one-form ranks, then supplies the nonzero top wedge and generic lines.
Surjectivity of the actual localized integral transpose and finiteness of its
actual target give one nonzero annihilator of its original cokernel.
-/

@[expose] public noncomputable section

open Polynomial
open scoped nonZeroDivisors TensorProduct

attribute [local instance 2000] Algebra.toSMul

namespace exteriorPower

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- In the actual top degree, a nonzero vector can occur as the last factor
of a nonzero wedge. The basis is constructed from that original vector. -/
theorem exists_snoc_ne_zero_of_finrank_eq (n : ℕ)
    (hdim : Module.finrank K V = n + 1) {x : V} (hx : x ≠ 0) :
    ∃ v : Fin n → V, ιMulti K (n + 1) (Fin.snoc v x) ≠ 0 := by
  classical
  let : FiniteDimensional K V := .of_finrank_pos (by rw [hdim]; exact Nat.succ_pos n)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K hx
  obtain ⟨s, b, i, hi, _⟩ := exists_basis_of_pairing_ne_zero hf
  let : Fintype s := FiniteDimensional.fintypeBasisIndex b
  let e : s ≃ Fin (n + 1) :=
    Fintype.equivFinOfCardEq ((Module.finrank_eq_card_basis b).symm.trans hdim)
  let c := b.reindex e
  let d : Module.Basis (Fin (n + 1)) K V := c.reindex (Equiv.swap (e i) (Fin.last n))
  have hd : d (Fin.last n) = x := by
    simp only [d, c, Module.Basis.reindex_apply, Equiv.symm_swap,
      Equiv.swap_apply_right, e.symm_apply_apply]
    exact hi.symm
  let v : Fin n → V := fun j => d j.castSucc
  have htuple : Fin.snoc v x = (d : Fin (n + 1) → V) := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.snoc_last]
      exact hd.symm
    · rw [Fin.snoc_castSucc]
  refine ⟨v, ?_⟩
  rw [htuple]
  intro hzero
  let ell : (⋀[K]^(n + 1) V) →ₗ[K] K := alternatingMapLinearEquiv d.det
  have he : ell (ιMulti K (n + 1) d) = 1 := by
    rw [alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self]
  rw [hzero, map_zero] at he
  exact zero_ne_one he

end exteriorPower

namespace KaehlerDifferential

variable {Λ K L : Type*} [CommRing Λ] [Field K] [Field L]
  [Algebra Λ K] [Algebra K L] [Algebra Λ L] [IsScalarTower Λ K L]
  {p : ℕ} [CharP K p] {a : K}

/-- Equal actual differential dimensions on the two original fields force
da to be nonzero: otherwise the passed presentation adds a new free direction. -/
theorem pureDegreeP_D_ne_zero_of_equal_finrank
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ)
    (hK : Module.finrank K (KaehlerDifferential Λ K) = n + 1)
    (hL : Module.finrank L (KaehlerDifferential Λ L) = n + 1) :
    D Λ K a ≠ 0 := by
  let : FiniteDimensional K (KaehlerDifferential Λ K) :=
    .of_finrank_pos (by rw [hK]; exact Nat.succ_pos n)
  intro hzero
  let U := Submodule.span K ({D Λ K a} : Set (KaehlerDifferential Λ K))
  have hU : Module.finrank K U = 0 := by simp [U, hzero]
  have hquot : Module.finrank K ((KaehlerDifferential Λ K) ⧸ U) = n + 1 := by
    have he := U.finrank_quotient_add_finrank
    rw [hU, add_zero, hK] at he
    exact he
  have he := (pureDegreePDifferentialDecomposition (Λ := Λ) h).finrank_eq
  change Module.finrank L (KaehlerDifferential Λ L) =
    Module.finrank L ((L ⊗[K] ((KaehlerDifferential Λ K) ⧸ U)) × L) at he
  rw [Module.finrank_prod, Module.finrank_baseChange, hquot, Module.finrank_self, hL] at he
  omega

/-- The actual Kähler decomposition transports the original differential
dimension when da is nonzero. No dimension of the upper module is assumed. -/
theorem pureDegreeP_finrank_of_nonzero_differential
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ)
    (hdim : Module.finrank K (KaehlerDifferential Λ K) = n + 1)
    (hda : D Λ K a ≠ 0) :
    Module.finrank L (KaehlerDifferential Λ L) = n + 1 := by
  let : FiniteDimensional K (KaehlerDifferential Λ K) :=
    .of_finrank_pos (by rw [hdim]; exact Nat.succ_pos n)
  let U := Submodule.span K ({D Λ K a} : Set (KaehlerDifferential Λ K))
  have hquot : Module.finrank K ((KaehlerDifferential Λ K) ⧸ U) = n := by
    have he := Submodule.finrank_quotient_add_finrank
      (Submodule.span K ({D Λ K a} : Set (KaehlerDifferential Λ K)))
    rw [finrank_span_singleton hda, hdim] at he
    change Module.finrank K ((KaehlerDifferential Λ K) ⧸
      Submodule.span K ({D Λ K a} : Set (KaehlerDifferential Λ K))) = n
    omega
  calc
    Module.finrank L (KaehlerDifferential Λ L) =
        Module.finrank L ((L ⊗[K] ((KaehlerDifferential Λ K) ⧸ U)) × L) :=
      (pureDegreePDifferentialDecomposition (Λ := Λ) h).finrank_eq
    _ = n + 1 := by
      rw [Module.finrank_prod, Module.finrank_baseChange, hquot, Module.finrank_self]

/-- Genuine original rank and nonzero-da data produce all three generic
inputs of the differential transpose theorem. -/
theorem exists_pureDegreeP_topExterior_trace_data
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (n : ℕ)
    (hdim : Module.finrank K (KaehlerDifferential Λ K) = n + 1)
    (hda : D Λ K a ≠ 0) :
    ∃ v : Fin n → KaehlerDifferential Λ K,
      exteriorPower.ιMulti K (n + 1) (Fin.snoc v (D Λ K a)) ≠ 0 ∧
      Module.finrank K (⋀[K]^(n + 1) (KaehlerDifferential Λ K)) = 1 ∧
      Module.finrank L (⋀[L]^(n + 1) (KaehlerDifferential Λ L)) = 1 := by
  let : FiniteDimensional K (KaehlerDifferential Λ K) :=
    .of_finrank_pos (by rw [hdim]; exact Nat.succ_pos n)
  have hupper := pureDegreeP_finrank_of_nonzero_differential h n hdim hda
  let : FiniteDimensional L (KaehlerDifferential Λ L) :=
    .of_finrank_pos (by rw [hupper]; exact Nat.succ_pos n)
  obtain ⟨v, hv⟩ := exteriorPower.exists_snoc_ne_zero_of_finrank_eq n hdim hda
  refine ⟨v, hv, ?_, ?_⟩
  · rw [exteriorPower.finrank_eq, hdim, Nat.choose_self]
  · rw [exteriorPower.finrank_eq, hupper, Nat.choose_self]

end KaehlerDifferential

namespace LinearMap

/-- One nonzero original-ring scalar annihilates the literal native cokernel.
Keeping the module abstract here fixes its quotient dictionary before specialization. -/
def HasNonzeroCokernelAnnihilator {R Source Target : Type*} [CommRing R]
    [AddCommGroup Source] [Module R Source] [AddCommGroup Target] [Module R Target]
    (f : Source →ₗ[R] Target) : Prop :=
  ∃ s : R, s ≠ 0 ∧ ∀ x : Target ⧸ f.range, s • x = 0

/-- Literal cokernel annihilation gives the same fixed-scalar image containment. -/
theorem HasNonzeroCokernelAnnihilator.exists_smul_mem_range
    {R Source Target : Type*} [CommRing R]
    [AddCommGroup Source] [Module R Source] [AddCommGroup Target] [Module R Target]
    {f : Source →ₗ[R] Target} (h : HasNonzeroCokernelAnnihilator f) :
    ∃ s : R, s ≠ 0 ∧ ∀ x : Target, s • x ∈ f.range := by
  obtain ⟨s, hs, hann⟩ := h
  refine ⟨s, hs, fun x => ?_⟩
  apply (Submodule.Quotient.mk_eq_zero f.range).mp
  exact ((Submodule.mkQ f.range).map_smul s x).trans (hann (Submodule.mkQ f.range x))

variable {A M N : Type*} [CommRing A] [IsDomain A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [Module.Finite A N]

/-- A finite target and surjectivity of the actual generic map give one
nonzero annihilator of the original cokernel. The source need not be finite. -/
theorem exists_nonzero_annihilator_coker_of_localized_surjective
    (f : M →ₗ[A] N) (hf : Function.Surjective (LocalizedModule.map A⁰ f)) :
    ∃ s : A, s ≠ 0 ∧ ∀ x : N ⧸ f.range, s • x = 0 := by
  let C := N ⧸ f.range
  let : Subsingleton (LocalizedModule A⁰ C) :=
    (localizedMap_surjective_iff_subsingleton_localized_coker A⁰ f).mp hf
  have htor : Module.IsTorsion A C := by
    intro x
    have he : LocalizedModule.mkLinearMap A⁰ C x =
        LocalizedModule.mkLinearMap A⁰ C 0 := Subsingleton.elim _ _
    obtain ⟨s, hs⟩ :=
      (IsLocalizedModule.eq_iff_exists A⁰ (LocalizedModule.mkLinearMap A⁰ C)).mp he
    exact ⟨s, by simpa only [smul_zero] using hs⟩
  obtain ⟨s, hs, hsreg⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htor
  refine ⟨s, nonZeroDivisors.ne_zero hsreg, ?_⟩
  intro x
  exact (Submodule.mem_annihilator.mp hs) x (Submodule.mem_top)

/-- Package the literal cokernel statement while its module dictionaries are abstract. -/
theorem hasNonzeroCokernelAnnihilator_of_localized_surjective
    (R Source Target : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup Source] [Module R Source] [AddCommGroup Target] [Module R Target]
    [Module.Finite R Target]
    (f : Source →ₗ[R] Target) (hf : Function.Surjective (LocalizedModule.map R⁰ f)) :
    HasNonzeroCokernelAnnihilator (R := R) (Source := Source) (Target := Target) f :=
  exists_nonzero_annihilator_coker_of_localized_surjective f hf

/-- The same original annihilator says that every target value has an
original source preimage after multiplication by one fixed nonzero scalar. -/
theorem exists_nonzero_smul_mem_range_of_localized_surjective
    (f : M →ₗ[A] N) (hf : Function.Surjective (LocalizedModule.map A⁰ f)) :
    ∃ s : A, s ≠ 0 ∧ ∀ x : N, s • x ∈ f.range := by
  obtain ⟨s, hs, hann⟩ := exists_nonzero_annihilator_coker_of_localized_surjective f hf
  refine ⟨s, hs, ?_⟩
  intro x
  have he : Submodule.mkQ f.range (s • x) = 0 :=
    ((Submodule.mkQ f.range).map_smul s x).trans (hann (Submodule.mkQ f.range x))
  exact (Submodule.Quotient.mk_eq_zero f.range).mp he

end LinearMap

namespace KaehlerDifferential

variable (Λ A K L : Type*) [CommRing Λ]
  [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra Λ A] [Algebra Λ K] [Algebra Λ L]
  [IsScalarTower Λ A K] [IsScalarTower Λ K L] [IsScalarTower Λ A L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  [Module.Finite A (integralClosure A L)]
  {p : ℕ} [Fact p.Prime] [CharP K p] {a : K} (n : ℕ)

local notation "B" => integralClosure A L
local notation "M" => (⋀[A]^(n + 1) (KaehlerDifferential Λ A))
local notation "V" => (⋀[K]^(n + 1) (KaehlerDifferential Λ K))
local notation "W" => (⋀[L]^(n + 1) (KaehlerDifferential Λ L))
local notation "H" => (B →ₗ[A] Module.Dual A (Module.Dual A M))

/-- One fixed nonzero scalar annihilates the actual global transpose cokernel.
All generic surjectivity is obtained from the original differential trace. -/
theorem exists_nonzero_annihilator_integralClosureTraceTranspose_coker
    [Module.Finite A M]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    (v : Fin n → KaehlerDifferential Λ K)
    (hv : exteriorPower.ιMulti K (n + 1) (Fin.snoc v (D Λ K a)) ≠ 0)
    (hV : Module.finrank K V = 1) (hW : Module.finrank L W = 1) :
    LinearMap.HasNonzeroCokernelAnnihilator (R := A)
      (Source := ⋀[B]^(n + 1) (KaehlerDifferential Λ B)) (Target := H)
      (integralClosureTraceTranspose Λ A K L n hdegree h) := by
  let : Module.Finite A H := by
    let : IsNoetherian A (Module.Dual A M) := isNoetherian_linearMap A A M
    let : Module.Finite A (Module.Dual A M) := Module.IsNoetherian.finite A _
    let : IsNoetherian A (Module.Dual A (Module.Dual A M)) :=
      isNoetherian_linearMap A A (Module.Dual A M)
    let : IsNoetherian A H :=
      isNoetherian_linearMap A (Module.Dual A (Module.Dual A M)) B
    exact Module.IsNoetherian.finite A H
  apply LinearMap.hasNonzeroCokernelAnnihilator_of_localized_surjective
  let : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  let : IsNoetherian A (Module.Dual A M) := isNoetherian_linearMap A A M
  let : Module.Finite A (Module.Dual A M) := Module.IsNoetherian.finite A _
  let : Module.FinitePresentation A (Module.Dual A M) :=
    Module.finitePresentation_of_finite A _
  let : IsLocalizedModule A⁰ (mapExterior Λ A K (n + 1)) :=
    mapExterior_isLocalizedModule Λ A K A⁰ (n + 1)
  let : FiniteDimensional K V :=
    Module.Finite.of_isLocalizedModule A⁰ (mapExterior Λ A K (n + 1))
  let j := Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1))
  let : IsLocalizedModule A⁰ j :=
    Module.Dual.doubleDualToFraction_isLocalizedModule (K := K) (mapExterior Λ A K (n + 1))
  let : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    integralClosure.isLocalization A K L
  let fB := (Algebra.linearMap B L).restrictScalars A
  let : IsLocalizedModule A⁰ fB :=
    IsLocalizedModule.restrictScalars A⁰ (Algebra.linearMap B L)
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid B A⁰)
      (mapExterior Λ B L (n + 1)) :=
    mapExterior_isLocalizedModule Λ B L (Algebra.algebraMapSubmonoid B A⁰) (n + 1)
  let fN := (mapExterior Λ B L (n + 1)).restrictScalars A
  let : IsLocalizedModule A⁰ fN :=
    IsLocalizedModule.restrictScalars A⁰ (mapExterior Λ B L (n + 1))
  let : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  let fH := integralClosureTraceHomToFraction Λ A K L n
  let : IsLocalizedModule A⁰ fH :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _
  let c := integralClosureTraceTranspose Λ A K L n hdegree h
  have hsurj : Function.Surjective (IsLocalizedModule.map A⁰ fN fH c) :=
    (integralClosureTraceTranspose_generic_bijective Λ A K L n hdegree h v hv hV hW).2
  exact (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective fN fH).mp hsurj

/-- B4 can supply actual Kähler dimension and nonzero da; the source wedge
and both generic line dimensions are then derived by the actual presentation. -/
theorem exists_nonzero_annihilator_integralClosureTraceTranspose_coker_of_nonzero_differential
    [Module.Finite A M]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    (hdim : Module.finrank K (KaehlerDifferential Λ K) = n + 1)
    (hda : D Λ K a ≠ 0) :
    LinearMap.HasNonzeroCokernelAnnihilator (R := A)
      (Source := ⋀[B]^(n + 1) (KaehlerDifferential Λ B)) (Target := H)
      (integralClosureTraceTranspose Λ A K L n hdegree h) := by
  obtain ⟨v, hv, hV, hW⟩ := exists_pureDegreeP_topExterior_trace_data h n hdim hda
  exact exists_nonzero_annihilator_integralClosureTraceTranspose_coker
    Λ A K L n hdegree h v hv hV hW

/-- When B4 supplies the two actual equal generic differential dimensions,
the presentation itself derives da≠0 before the cokernel argument is used. -/
theorem exists_nonzero_annihilator_integralClosureTraceTranspose_coker_of_equal_finrank
    [Module.Finite A M]
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    (hK : Module.finrank K (KaehlerDifferential Λ K) = n + 1)
    (hL : Module.finrank L (KaehlerDifferential Λ L) = n + 1) :
    LinearMap.HasNonzeroCokernelAnnihilator (R := A)
      (Source := ⋀[B]^(n + 1) (KaehlerDifferential Λ B)) (Target := H)
      (integralClosureTraceTranspose Λ A K L n hdegree h) :=
  exists_nonzero_annihilator_integralClosureTraceTranspose_coker_of_nonzero_differential
    Λ A K L n hdegree h hK (pureDegreeP_D_ne_zero_of_equal_finrank h n hK hL)

/-- The actual integral differential basis supplies both generic inputs over the
unchanged base. No separating family of the formal fraction field is required. -/
theorem exists_nonzero_annihilator_integralClosureTraceTranspose_coker_of_basis
    (hdegree : Module.finrank K L = p)
    (a₀ : A)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C (algebraMap A K a₀)))
    (b : Module.Basis (Fin (n + 1)) A (KaehlerDifferential Λ A))
    (hda : D Λ A a₀ ≠ 0) :
    letI := finite_exterior_of_basis b (n + 1);
    LinearMap.HasNonzeroCokernelAnnihilator (R := A)
      (Source := ⋀[B]^(n + 1) (KaehlerDifferential Λ B)) (Target := H)
      (integralClosureTraceTranspose Λ A K L n hdegree h) := by
  let := finite_exterior_of_basis b (n + 1)
  apply exists_nonzero_annihilator_integralClosureTraceTranspose_coker_of_nonzero_differential
    Λ A K L n hdegree h
  · simpa only [Fintype.card_fin] using finrank_fraction_of_basis (K := K) b
  · exact fraction_D_ne_zero_of_basis b a₀ hda


/-- The actual basis supplies one fixed nonzero scalar carrying every target
functional into the image of the original trace transpose. -/
theorem exists_nonzero_smul_mem_range_integralClosureTraceTranspose_of_basis
    (hdegree : Module.finrank K L = p) (a₀ : A)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C (algebraMap A K a₀)))
    (b : Module.Basis (Fin (n + 1)) A (KaehlerDifferential Λ A))
    (hda : D Λ A a₀ ≠ 0) :
    letI := finite_exterior_of_basis b (n + 1);
    ∃ s : A, s ≠ 0 ∧ ∀ x : H,
      s • x ∈ (integralClosureTraceTranspose Λ A K L n hdegree h).range := by
  let := finite_exterior_of_basis b (n + 1)
  exact (exists_nonzero_annihilator_integralClosureTraceTranspose_coker_of_basis
    Λ A K L n hdegree a₀ h b hda).exists_smul_mem_range

end KaehlerDifferential

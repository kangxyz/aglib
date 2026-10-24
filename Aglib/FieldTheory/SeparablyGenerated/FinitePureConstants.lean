/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Finite coefficients and actual constant-field composita

Finite separable algebraic witnesses over a compositum descend to finitely
many constants. All intermediate fields in these statements belong to the
same ambient field, so the original inclusions are retained.

Finite purely inseparable constants are constructed inside the relative
perfect closure of the original coefficient field in the same ambient field.
The literal compositum retains both inclusions and the tensor multiplication map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- An element of a compositum uses only finitely many elements of its first field. -/
theorem exists_finset_left_of_mem_sup (P M : IntermediateField k Ω) {x : Ω}
    (hx : x ∈ P ⊔ M) :
    ∃ c : Finset Ω, (c : Set Ω) ⊆ P ∧ x ∈ adjoin k (c : Set Ω) ⊔ M := by
  classical
  obtain ⟨s, hs, hxs⟩ := exists_finset_of_mem_adjoin
    (show x ∈ adjoin k ((P : Set Ω) ∪ M) from hx)
  refine ⟨s.filter (· ∈ P), ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · apply (show adjoin k (s : Set Ω) ≤
        adjoin k ((s.filter (· ∈ P) : Finset Ω) : Set Ω) ⊔ M from ?_) hxs
    apply adjoin_le_iff.mpr
    intro a ha
    by_cases haP : a ∈ P
    · apply (show adjoin k ((s.filter (· ∈ P) : Finset Ω) : Set Ω) ≤
          adjoin k ((s.filter (· ∈ P) : Finset Ω) : Set Ω) ⊔ M from le_sup_left)
      exact subset_adjoin k _ (Finset.mem_filter.mpr ⟨ha, haP⟩)
    · apply (show M ≤ adjoin k ((s.filter (· ∈ P) : Finset Ω) : Set Ω) ⊔ M
        from le_sup_right)
      exact (hs ha).resolve_left haP

/-- A finite family in a compositum can use the same finite set of constants. -/
theorem exists_finset_left_of_finset_mem_sup (P M : IntermediateField k Ω)
    (s : Finset Ω) (hs : (s : Set Ω) ⊆ (P ⊔ M : IntermediateField k Ω)) :
    ∃ c : Finset Ω, (c : Set Ω) ⊆ P ∧
      (s : Set Ω) ⊆ (adjoin k (c : Set Ω) ⊔ M : IntermediateField k Ω) := by
  classical
  choose c hcP hcx using fun x : s => exists_finset_left_of_mem_sup P M (hs x.2)
  let d := Finset.univ.biUnion c
  have hcd (x : s) : (c x : Set Ω) ⊆ d := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, ha⟩
  refine ⟨d, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp ha
    exact hcP x hx
  · intro x hx
    exact (sup_le_sup_right (adjoin.mono k _ _ (hcd ⟨x, hx⟩)) M) (hcx ⟨x, hx⟩)

/-- A separable polynomial over one embedded field descends whenever all its
coefficients belong to another embedded field. -/
theorem isSeparable_of_minpoly_coeff_mem (P E : IntermediateField k Ω) {x : Ω}
    (hx : IsSeparable P x)
    (hc : ∀ n, ((minpoly P x).coeff n : Ω) ∈ E) : IsSeparable E x := by
  let p := minpoly P x
  have hlift : p.map (algebraMap P Ω) ∈ Polynomial.lifts (algebraMap E Ω) := by
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro n
    refine ⟨⟨(p.coeff n : Ω), hc n⟩, ?_⟩
    simp only [Polynomial.coeff_map]
    rfl
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp hlift
  have hqsep : q.Separable := by
    apply (Polynomial.separable_map (algebraMap E Ω)).mp
    rw [hq]
    exact Polynomial.Separable.map (f := algebraMap P Ω) hx
  have hqzero : Polynomial.aeval x q = 0 := by
    change q.eval₂ (algebraMap E Ω) x = 0
    rw [← Polynomial.eval_map, hq, Polynomial.eval_map]
    exact minpoly.aeval P x
  exact hqsep.of_dvd (minpoly.dvd E x hqzero)

/-- Separability of an algebraic element over a compositum uses only finitely
many constants from the first factor. The ambient element is unchanged. -/
theorem exists_finset_left_of_isSeparable_sup (P M : IntermediateField k Ω) {x : Ω}
    (hx : IsSeparable (P ⊔ M : IntermediateField k Ω) x) :
    ∃ c : Finset Ω, (c : Set Ω) ⊆ P ∧
      IsSeparable (adjoin k (c : Set Ω) ⊔ M : IntermediateField k Ω) x := by
  classical
  let p := minpoly (P ⊔ M : IntermediateField k Ω) x
  let s := p.coeffs.image ((↑) : (P ⊔ M : IntermediateField k Ω) → Ω)
  have hs : (s : Set Ω) ⊆ (P ⊔ M : IntermediateField k Ω) := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact b.2
  obtain ⟨c, hcP, hc⟩ := exists_finset_left_of_finset_mem_sup P M s hs
  refine ⟨c, hcP, isSeparable_of_minpoly_coeff_mem (P ⊔ M)
    (adjoin k (c : Set Ω) ⊔ M) hx ?_⟩
  intro n
  by_cases hn : p.coeff n = 0
  · change (p.coeff n : Ω) ∈ adjoin k (c : Set Ω) ⊔ M
    rw [hn]
    exact (adjoin k (c : Set Ω) ⊔ M).zero_mem
  · exact hc (Finset.mem_image.mpr ⟨p.coeff n, Polynomial.coeff_mem_coeffs hn, rfl⟩)

end IntermediateField

namespace Algebra.FinitePureConstants

variable (k K Ω : Type*) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]

/-- The literal compositum in the specified ambient field, retaining its coefficient action. -/
abbrev compositum (E : IntermediateField k Ω) : IntermediateField E Ω :=
  IntermediateField.adjoin E (Set.range (algebraMap K Ω))

/-- The original field embeds in the literal compositum by its original ambient inclusion. -/
def originalMap (E : IntermediateField k Ω) : K →ₐ[k] compositum k K Ω E :=
  (IsScalarTower.toAlgHom k K Ω).codRestrict
    ((compositum k K Ω E).restrictScalars k).toSubalgebra
    (fun x => IntermediateField.subset_adjoin E _ ⟨x, rfl⟩)

@[simp]
theorem coe_originalMap (E : IntermediateField k Ω) (x : K) :
    (originalMap k K Ω E x : Ω) = algebraMap K Ω x := rfl

/-- The original-field action is induced by the actual embedding, rather than an arbitrary map. -/
abbrev originalAlgebra (E : IntermediateField k Ω) : Algebra K (compositum k K Ω E) :=
  (originalMap k K Ω E).toRingHom.toAlgebra

/-- This is the commuting square of the original coefficient field and original extension. -/
theorem original_isScalarTower (E : IntermediateField k Ω) :
    letI := originalAlgebra k K Ω E
    IsScalarTower k K (compositum k K Ω E) := by
  let := originalAlgebra k K Ω E
  exact IsScalarTower.of_algebraMap_eq fun x => ((originalMap k K Ω E).commutes x).symm

/-- The compositum maps to the ambient field compatibly with the original inclusion. -/
theorem ambient_isScalarTower (E : IntermediateField k Ω) :
    letI := originalAlgebra k K Ω E
    IsScalarTower K (compositum k K Ω E) Ω := by
  let := originalAlgebra k K Ω E
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [Algebra k K] [IsScalarTower k K Ω] in
/-- Least-field characterization with the coefficient action unchanged. -/
theorem compositum_le_iff (E : IntermediateField k Ω) (L : IntermediateField E Ω) :
    compositum k K Ω E ≤ L ↔ Set.range (algebraMap K Ω) ⊆ L :=
  IntermediateField.adjoin_le_iff

/-- As a field over the original base, the compositum is the supremum of the
actual coefficient field and the actual image of the original extension. -/
theorem compositum_restrictScalars (E : IntermediateField k Ω) :
    (compositum k K Ω E).restrictScalars k =
      E ⊔ (IsScalarTower.toAlgHom k K Ω).fieldRange := by
  calc
    (compositum k K Ω E).restrictScalars k =
        E ⊔ IntermediateField.adjoin k (Set.range (algebraMap K Ω)) :=
      IntermediateField.restrictScalars_adjoin_eq_sup k E _
    _ = E ⊔ (IsScalarTower.toAlgHom k K Ω).fieldRange := by
      apply congrArg (fun F : IntermediateField k Ω => E ⊔ F)
      change IntermediateField.adjoin k
        ((IsScalarTower.toAlgHom k K Ω).fieldRange : Set Ω) =
          (IsScalarTower.toAlgHom k K Ω).fieldRange
      exact IntermediateField.adjoin_self k (IsScalarTower.toAlgHom k K Ω).fieldRange

omit [Algebra k K] [IsScalarTower k K Ω] in
/-- The same ambient subfield is obtained by adjoining the constants to the
original field. This equality retains both original inclusions. -/
theorem compositum_toSubfield (E : IntermediateField k Ω) :
    (compositum k K Ω E).toSubfield =
      (IntermediateField.adjoin K (E : Set Ω)).toSubfield := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_subfield
    · rintro x ⟨e, rfl⟩
      exact IntermediateField.subset_adjoin K _ e.2
    · rintro x ⟨a, rfl⟩
      exact (IntermediateField.adjoin K (E : Set Ω)).algebraMap_mem a
  · apply IntermediateField.adjoin_le_subfield
    · rintro x ⟨a, rfl⟩
      exact IntermediateField.subset_adjoin E _ ⟨a, rfl⟩
    · intro x hx
      exact (compositum k K Ω E).algebraMap_mem ⟨x, hx⟩

/-- Switching the description of the compositum fixes every ambient element
and respects the actual original-field action. -/
def compositumSwap (E : IntermediateField k Ω) :
    letI := originalAlgebra k K Ω E
    compositum k K Ω E ≃ₐ[K] IntermediateField.adjoin K (E : Set Ω) := by
  letI := originalAlgebra k K Ω E
  exact
    { RingEquiv.subfieldCongr (compositum_toSubfield k K Ω E) with
      commutes' := fun _ => rfl }

/-- Purely inseparable constants remain purely inseparable after adjoining
them to the original field in the same ambient field. -/
theorem isPurelyInseparable_adjoin (E : IntermediateField k Ω)
    [IsPurelyInseparable k E] :
    IsPurelyInseparable K (IntermediateField.adjoin K (E : Set Ω)) := by
  let q := ringExpChar k
  let : ExpChar K q := expChar_of_injective_algebraMap
    (RingHom.injective (algebraMap k K)) q
  apply (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem K Ω q).mpr
  intro x hx
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k q (⟨x, hx⟩ : E)
  refine ⟨n, algebraMap k K a, ?_⟩
  rw [← IsScalarTower.algebraMap_apply k K Ω]
  simpa only [map_pow, ← IsScalarTower.algebraMap_apply k E Ω,
    IntermediateField.algebraMap_apply, Subtype.coe_mk] using
    congrArg (algebraMap E Ω) ha

/-- The literal compositum has the required pure original-field extension. -/
theorem compositum_isPurelyInseparable (E : IntermediateField k Ω)
    [IsPurelyInseparable k E] :
    letI := originalAlgebra k K Ω E
    IsPurelyInseparable K (compositum k K Ω E) := by
  let := originalAlgebra k K Ω E
  let := isPurelyInseparable_adjoin k K Ω E
  exact (compositumSwap k K Ω E).symm.isPurelyInseparable

/-- Finite purely inseparable constants give a finite extension of the
original field under its specified action. -/
theorem compositum_finiteDimensional (E : IntermediateField k Ω)
    [FiniteDimensional k E] [IsPurelyInseparable k E] :
    letI := originalAlgebra k K Ω E
    FiniteDimensional K (compositum k K Ω E) := by
  let := originalAlgebra k K Ω E
  let := isPurelyInseparable_adjoin k K Ω E
  have hfg : E.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  let : Algebra.EssFiniteType K (IntermediateField.adjoin K (E : Set Ω)) := by
    apply IntermediateField.essFiniteType_iff.mpr
    obtain ⟨s, hs⟩ := hfg
    refine ⟨s, ?_⟩
    rw [← hs, IntermediateField.adjoin_adjoin_right]
  let : FiniteDimensional K (IntermediateField.adjoin K (E : Set Ω)) :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact FiniteDimensional.of_injective (compositumSwap k K Ω E).toLinearMap
    (compositumSwap k K Ω E).injective

/-- Multiplication of the specified images of the original and constant fields. -/
def tensorMap (E : IntermediateField k Ω) : K ⊗[k] E →ₐ[k] Ω :=
  Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k K Ω) E.val

@[simp]
theorem tensorMap_tmul (E : IntermediateField k Ω) (a : K) (b : E) :
    tensorMap k K Ω E (a ⊗ₜ[k] b) = algebraMap K Ω a * (b : Ω) := rfl

theorem tensorMap_includeLeft (E : IntermediateField k Ω) (a : K) :
    tensorMap k K Ω E
      (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := K) (B := E) a) =
        algebraMap K Ω a := by
  change algebraMap K Ω a * (1 : Ω) = algebraMap K Ω a
  exact mul_one _

/-- The image is the actual compositum, as a subalgebra of the given ambient field. -/
theorem tensorMap_range (E : IntermediateField k Ω) [Algebra.IsAlgebraic k E] :
    (tensorMap k K Ω E).range =
      ((compositum k K Ω E).restrictScalars k).toSubalgebra := by
  rw [compositum_restrictScalars, tensorMap, Algebra.TensorProduct.productMap_range,
    IntermediateField.sup_toSubalgebra_of_isAlgebraic_left, E.range_val]
  exact sup_comm (IsScalarTower.toAlgHom k K Ω).range E.toSubalgebra

/-- A tensor element is killed precisely when it is nilpotent. This uses
pure inseparability of the constants, with no separability hypothesis on K/k. -/
theorem tensorMap_eq_zero_iff (E : IntermediateField k Ω)
    [IsPurelyInseparable k E] (x : K ⊗[k] E) :
    tensorMap k K Ω E x = 0 ↔ IsNilpotent x := by
  constructor
  · intro hx
    obtain ⟨n, hn, a, ha⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct x
    change (a ⊗ₜ[k] (1 : E)) = x ^ n at ha
    have ha0 : a = 0 := by
      apply (algebraMap K Ω).injective
      rw [map_zero]
      calc
        algebraMap K Ω a = tensorMap k K Ω E (a ⊗ₜ[k] (1 : E)) := by
          rw [tensorMap_tmul, OneMemClass.coe_one, mul_one]
        _ = tensorMap k K Ω E (x ^ n) := congrArg (tensorMap k K Ω E) ha
        _ = tensorMap k K Ω E x ^ n := (tensorMap k K Ω E).map_pow x n
        _ = 0 := by rw [hx, zero_pow (Nat.ne_of_gt hn)]
    refine ⟨n, ?_⟩
    rw [← ha, ha0, _root_.TensorProduct.zero_tmul]
  · rintro ⟨n, hn⟩
    have hz : tensorMap k K Ω E x ^ n = 0 := by
      have hpow : tensorMap k K Ω E (x ^ n) = tensorMap k K Ω E x ^ n :=
        (tensorMap k K Ω E).map_pow x n
      calc
        tensorMap k K Ω E x ^ n = tensorMap k K Ω E (x ^ n) := hpow.symm
        _ = tensorMap k K Ω E 0 := congrArg (tensorMap k K Ω E) hn
        _ = 0 := (tensorMap k K Ω E).map_zero
    exact eq_zero_of_pow_eq_zero hz

/-- The reduced tensor quotient uses the kernel of the specified multiplication map. -/
theorem tensorMap_ker (E : IntermediateField k Ω) [IsPurelyInseparable k E] :
    RingHom.ker (tensorMap k K Ω E).toRingHom = nilradical (K ⊗[k] E) := by
  ext x
  change tensorMap k K Ω E x = 0 ↔ IsNilpotent x
  exact tensorMap_eq_zero_iff k K Ω E x

end Algebra.FinitePureConstants

namespace IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- Algebraic separability persists upon enlarging an embedded coefficient field. -/
theorem isSeparable_of_le {P Q : IntermediateField k Ω} (hPQ : P ≤ Q) {x : Ω}
    (hx : IsSeparable P x) : IsSeparable Q x := by
  let : Algebra P Q := (inclusion hPQ).toAlgebra
  let : IsScalarTower P Q Ω := .of_algebraMap_eq' rfl
  exact hx.tower_top Q

/-- A finite family of separable algebraic witnesses uses one finite constant set. -/
theorem exists_finset_left_of_finset_isSeparable_sup (P M : IntermediateField k Ω)
    (s : Finset Ω) (hs : ∀ x ∈ s, IsSeparable (P ⊔ M : IntermediateField k Ω) x) :
    ∃ c : Finset Ω, (c : Set Ω) ⊆ P ∧
      ∀ x ∈ s, IsSeparable (adjoin k (c : Set Ω) ⊔ M : IntermediateField k Ω) x := by
  classical
  choose c hcP hcx using fun x : s => exists_finset_left_of_isSeparable_sup P M (hs x x.2)
  let d := Finset.univ.biUnion c
  have hcd (x : s) : (c x : Set Ω) ⊆ d := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, ha⟩
  refine ⟨d, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp ha
    exact hcP x hx
  · intro x hx
    exact isSeparable_of_le (sup_le_sup_right (adjoin.mono k _ _ (hcd ⟨x, hx⟩)) M)
      (hcx ⟨x, hx⟩)

omit [Algebra k Ω] in
/-- The fields generated before and after an ambient inclusion have the same
elements under their canonical equivalence. -/
def adjoinEquivImage {F : Type*} [Field F] [Algebra F Ω]
    (N : IntermediateField F Ω) {ι : Type*} (b : ι → N) :
    adjoin F (Set.range b) ≃ₐ[F] adjoin F (Set.range fun i => (b i : Ω)) :=
  ((adjoin F (Set.range b)).equivMap N.val).trans
    (equivOfEq (by rw [adjoin_map, ← Set.range_comp]; rfl))

omit [Algebra k Ω] in
/-- Moving a separating field through an ambient inclusion preserves element separability. -/
theorem isSeparable_adjoin_image_iff {F : Type*} [Field F] [Algebra F Ω]
    (N : IntermediateField F Ω) {ι : Type*} (b : ι → N) (x : N) :
    IsSeparable (adjoin F (Set.range b)) x ↔
      IsSeparable (adjoin F (Set.range fun i => (b i : Ω))) (x : Ω) := by
  let B := adjoin F (Set.range b)
  let T := adjoin F (Set.range fun i => (b i : Ω))
  let e : B ≃ₐ[F] T := adjoinEquivImage N b
  have he (a : B) : (e a : Ω) = ((a : N) : Ω) := rfl
  let f := IsScalarTower.toAlgHom B N Ω
  constructor
  · intro hx
    have hx' : IsSeparable B (x : Ω) := hx.map f f.injective
    exact IsSeparable.of_equiv_equiv e.toRingEquiv (RingEquiv.refl Ω)
      (by ext a; exact he a) hx'
  · intro hx
    have hx' : IsSeparable B (x : Ω) :=
      IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl Ω)
        (by
          ext a
          change ((e.symm a : N) : Ω) = (a : Ω)
          simpa only [AlgEquiv.apply_symm_apply] using (he (e.symm a)).symm) hx
    exact IsSeparable.of_algHom B f hx'

/-- The adjoin and supremum descriptions have the same algebraic separability predicate. -/
theorem isSeparable_adjoin_iff_sup (P : IntermediateField k Ω) (s : Set Ω) (x : Ω) :
    IsSeparable (adjoin P s) x ↔
      IsSeparable (P ⊔ adjoin k s : IntermediateField k Ω) x := by
  let e : adjoin P s ≃+* (P ⊔ adjoin k s : IntermediateField k Ω) :=
    RingEquiv.subfieldCongr (congrArg IntermediateField.toSubfield
      (restrictScalars_adjoin_eq_sup k P s))
  exact ⟨IsSeparable.of_equiv_equiv e (RingEquiv.refl Ω) rfl,
    IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl Ω) rfl⟩

omit [Algebra k Ω] in
open scoped algebraAdjoinAdjoin in
/-- An algebraically independent family separating the generators separates their field. -/
theorem isSeparablyGenerated_adjoin_of_separating_family
    {F : Type*} [Field F] [Algebra F Ω] (s : Set Ω) {ι : Type*} (b : ι → Ω)
    (hbmem : ∀ i, b i ∈ adjoin F s) (hb : AlgebraicIndependent F b)
    (hsep : ∀ x ∈ s, IsSeparable (adjoin F (Set.range b)) x) :
    Algebra.IsSeparablyGenerated F (adjoin F s) := by
  let N := adjoin F s
  let bN : ι → N := fun i => ⟨b i, hbmem i⟩
  let B := adjoin F (Set.range bN)
  have hbN : AlgebraicIndependent F bN := AlgebraicIndependent.of_comp N.val hb
  have hN : N ≤ (separableClosure (adjoin F (Set.range b)) Ω).restrictScalars F :=
    adjoin_le_iff.mpr hsep
  let : Algebra.IsSeparable B N := ⟨fun x =>
    (isSeparable_adjoin_image_iff N bN x).mpr (hN x.2)⟩
  let : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range bN)) N :=
    Algebra.IsAlgebraic.trans (Algebra.adjoin F (Set.range bN)) B N
  have htb : IsTranscendenceBasis F bN :=
    hbN.isTranscendenceBasis_iff_isAlgebraic.mpr inferInstance
  exact ⟨Set.range bN, htb.to_subtype_range, inferInstance⟩

/-- One finite purely inseparable constant field contains all prescribed compositum
elements and all prescribed separable algebraic witnesses. -/
theorem exists_finite_pure_constants_for_family (M T : IntermediateField k Ω)
    (t s : Finset Ω)
    (ht : (t : Set Ω) ⊆ (perfectClosure k Ω ⊔ M : IntermediateField k Ω))
    (hs : ∀ x ∈ s, IsSeparable (perfectClosure k Ω ⊔ T : IntermediateField k Ω) x) :
    ∃ E : IntermediateField k Ω,
      E ≤ perfectClosure k Ω ∧ FiniteDimensional k E ∧ IsPurelyInseparable k E ∧
      (t : Set Ω) ⊆ (E ⊔ M : IntermediateField k Ω) ∧
      ∀ x ∈ s, IsSeparable (E ⊔ T : IntermediateField k Ω) x := by
  classical
  obtain ⟨c, hcP, hct⟩ := exists_finset_left_of_finset_mem_sup (perfectClosure k Ω) M t ht
  obtain ⟨d, hdP, hds⟩ := exists_finset_left_of_finset_isSeparable_sup
    (perfectClosure k Ω) T s hs
  let E := adjoin k ((c ∪ d : Finset Ω) : Set Ω)
  have hE : E ≤ perfectClosure k Ω := by
    apply adjoin_le_iff.mpr
    intro x hx
    exact (Finset.mem_union.mp hx).elim (hcP ·) (hdP ·)
  let : IsPurelyInseparable k E := (le_perfectClosure_iff k Ω E).mp hE
  let : Algebra.EssFiniteType k E := essFiniteType_iff.mpr (fg_adjoin_finset _)
  have hfinite : FiniteDimensional k E := Algebra.finite_of_essFiniteType_of_isAlgebraic
  refine ⟨E, hE, hfinite, inferInstance, ?_, ?_⟩
  · exact hct.trans (show (adjoin k (c : Set Ω) ⊔ M : IntermediateField k Ω) ≤ E ⊔ M
      from sup_le_sup_right (adjoin.mono k _ _ (by intro x hx; exact Finset.mem_union_left _ hx)) M)
  · intro x hx
    exact isSeparable_of_le (show (adjoin k (d : Set Ω) ⊔ T : IntermediateField k Ω) ≤ E ⊔ T
      from sup_le_sup_right
        (adjoin.mono k _ _ (by intro x hx; exact Finset.mem_union_right _ hx)) T)
      (hds x hx)

omit [Algebra k Ω] in
/-- A separating family expressed entirely in the ambient field. Keeping this
proposition named preserves its field and algebra instances under specialization. -/
def HasAmbientSeparatingFinset (F : Type*) [Field F] [Algebra F Ω]
    (N : IntermediateField F Ω) : Prop :=
  ∃ t : Finset Ω, (t : Set Ω) ⊆ N ∧ AlgebraicIndependent F ((↑) : t → Ω) ∧
    ∀ x ∈ N, IsSeparable (adjoin F (t : Set Ω)) x

omit [Algebra k Ω] in
/-- A finite separating basis over a perfect field transports through the actual
ambient inclusion, with abstract field data retained throughout the proof.
The finite-subtype range equalities are specialized before their coefficient
fields are formed, so the separability witnesses use explicit transports. -/
theorem hasAmbientSeparatingFinset_of_perfect
    (F : Type*) [Field F] [Algebra F Ω] [PerfectField F]
    (N : IntermediateField F Ω) [Algebra.EssFiniteType F N] :
    HasAmbientSeparatingFinset F N := by
  classical
  obtain ⟨b₀, hb₀, hsep₀⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField F N
  have hb₀range : Set.range ((↑) : b₀ → N) = (b₀ : Set N) :=
    Subtype.range_coe (s := (b₀ : Set N))
  let : Algebra.IsSeparable (adjoin F (b₀ : Set N)) N := hsep₀
  let b : b₀ → Ω := fun i => ((i : N) : Ω)
  have hb : AlgebraicIndependent F b := hb₀.1.map' (f := N.val) N.val.injective
  let t := b₀.image ((↑) : N → Ω)
  have hbt : Set.range b = (t : Set Ω) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨i, i.2, rfl⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨⟨i, hi⟩, rfl⟩
  have ht : (t : Set Ω) ⊆ N := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact i.2
  refine ⟨t, ht, hb.to_subtype_range' (t := (t : Set Ω)) hbt, ?_⟩
  intro x hx
  let xN : N := ⟨x, hx⟩
  have hxsep : IsSeparable (adjoin F (Set.range ((↑) : b₀ → N))) xN :=
    hb₀range.symm ▸ Algebra.IsSeparable.isSeparable (adjoin F (b₀ : Set N)) xN
  have hxambient : IsSeparable (adjoin F (Set.range b)) x :=
    (isSeparable_adjoin_image_iff N ((↑) : b₀ → N) xN).mp hxsep
  exact hbt ▸ hxambient

/-- Transport a finite separating family into the actual ambient field before
specializing the coefficient field to the relative perfect closure. -/
theorem exists_separating_finset_of_perfect_compositum
    (P M : IntermediateField k Ω) [PerfectField P] (hM : M.FG) :
    ∃ t : Finset Ω, (t : Set Ω) ⊆ (P ⊔ M : IntermediateField k Ω) ∧
      AlgebraicIndependent P ((↑) : t → Ω) ∧
      ∀ x ∈ M, IsSeparable (P ⊔ adjoin k (t : Set Ω) : IntermediateField k Ω) x := by
  let L : IntermediateField P Ω := adjoin P (M : Set Ω)
  obtain ⟨a, ha⟩ := hM
  let : Algebra.EssFiniteType P L := essFiniteType_iff.mpr ⟨a, by
    dsimp only [L]
    rw [← ha, adjoin_adjoin_right]⟩
  obtain ⟨t, ht, hb, hsep⟩ := hasAmbientSeparatingFinset_of_perfect P L
  have hL : L.restrictScalars k = P ⊔ M := by
    dsimp only [L]
    rw [restrictScalars_adjoin_eq_sup, adjoin_self]
  refine ⟨t, ?_, hb, ?_⟩
  · intro x hx
    have hxL : x ∈ L.restrictScalars k := ht hx
    exact hL ▸ hxL
  · intro x hx
    exact (isSeparable_adjoin_iff_sup P (t : Set Ω) x).mp
      (hsep x (subset_adjoin P _ hx))

/-- Finitely generated embedded fields become separably generated after a finite
purely inseparable constant extension inside the same perfect ambient field. -/
theorem exists_finite_pure_constants_of_fg [PerfectField Ω]
    (M : IntermediateField k Ω) (hM : M.FG) :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧ IsPurelyInseparable k E ∧
      Algebra.IsSeparablyGenerated E (adjoin E (M : Set Ω)) := by
  classical
  let P : IntermediateField k Ω := perfectClosure k Ω
  obtain ⟨t, ht, hb, hsepM⟩ := exists_separating_finset_of_perfect_compositum P M hM
  have htrange : Set.range ((↑) : t → Ω) = (t : Set Ω) :=
    Subtype.range_coe (s := (t : Set Ω))
  obtain ⟨a, ha⟩ := hM
  have haM : (a : Set Ω) ⊆ M := ha ▸ subset_adjoin k (a : Set Ω)
  let T : IntermediateField k Ω := adjoin k (t : Set Ω)
  obtain ⟨E, hEP, hfin, hpure, htE, hsepE⟩ :=
    exists_finite_pure_constants_for_family M T t a ht (fun x hx => hsepM x (haM hx))
  let : Algebra E P := (inclusion hEP).toAlgebra
  let : IsScalarTower E P Ω := .of_algebraMap_eq' rfl
  have hbE : AlgebraicIndependent E ((↑) : t → Ω) :=
    hb.restrictScalars (algebraMap E P).injective
  have hNE : (adjoin E (M : Set Ω)).restrictScalars k = E ⊔ M := by
    rw [restrictScalars_adjoin_eq_sup, adjoin_self]
  have hbmem (i : t) : (i : Ω) ∈ adjoin E (M : Set Ω) := by
    change (i : Ω) ∈ (adjoin E (M : Set Ω)).restrictScalars k
    rw [hNE]
    exact htE i.2
  let : IsScalarTower k (adjoin E (t : Set Ω)) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsepM' : M ≤ (separableClosure (adjoin E (t : Set Ω)) Ω).restrictScalars k := by
    rw [← ha]
    apply adjoin_le_iff.mpr
    intro x hx
    exact (isSeparable_adjoin_iff_sup E (t : Set Ω) x).mpr (hsepE x hx)
  refine ⟨E, hfin, hpure,
    isSeparablyGenerated_adjoin_of_separating_family (M : Set Ω) ((↑) : t → Ω)
      hbmem hbE ?_⟩
  intro x hx
  have hxsep : IsSeparable (adjoin E (t : Set Ω)) x := hsepM' hx
  exact htrange.symm ▸ hxsep

end IntermediateField

namespace Algebra.FinitePureConstants

variable (k K Ω : Type*) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]

/-- Finite purely inseparable constants for a finitely generated field extension.
Only the ambient field is perfect; the original coefficient field is arbitrary. -/
theorem exists_constants [Algebra.EssFiniteType k K] [PerfectField Ω] :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧ IsPurelyInseparable k E ∧
      Algebra.IsSeparablyGenerated E (compositum k K Ω E) := by
  let f := IsScalarTower.toAlgHom k K Ω
  let : Algebra.EssFiniteType k f.fieldRange :=
    (Algebra.EssFiniteType.iff_of_algEquiv f.equivFieldRange).mp inferInstance
  exact IntermediateField.exists_finite_pure_constants_of_fg f.fieldRange
    (IntermediateField.essFiniteType_iff.mp inferInstance)

end Algebra.FinitePureConstants

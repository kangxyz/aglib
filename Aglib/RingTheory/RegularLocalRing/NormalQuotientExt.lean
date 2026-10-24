/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.ParameterIdeal
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthExt
public import Aglib.RingTheory.RegularLocalRing.FiniteNormalAlgebra
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.RingTheory.Regular.Category

/-!
# Ext concentration for normal local quotients of dimension at most two

For a surjective local map `S → B`, where `S` is regular local of finite
dimension `d` and `B` is a normal Noetherian local domain of dimension `r ≤ 2`,
the original module `Ext^j_S(B,S)` vanishes unless `j + r = d`.

The parameters are constructed in `B` and lifted through the specified map.
Their actual successive scalar quotients over `S` are used in the
contravariant Ext sequence. Finiteness and Nakayama descend concentration
from the finite-length parameter quotient. The ambient dimension is arbitrary;
no Cohen--Macaulay, Gorenstein or projective-dimension hypothesis is assumed.

All concentration statements first use the native standard size `Ext.{u}`
for `ModuleCat.{u} S`, with `S B : Type u`. The last theorem transports that
conclusion to a specified other size using the actual `Ext.chgUniv` equivalence.
The current consumer is the stalk algebra in chosen-embedding concentration
for normal integral surfaces.
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory Abelian IsLocalRing RingTheory.Sequence
open scoped Pointwise

namespace ModuleCat

/-- Vanishing one degree higher for the actual source quotient forces
vanishing for the source. The contravariant map is scalar multiplication
by the same element, and Nakayama applies to the finite Ext module. -/
theorem subsingleton_ext_of_source_quotSMulTop
    {S : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (M : ModuleCat.{u} S) [Module.Finite S M]
    (a : S) (ha : IsSMulRegular M a) (ham : a ∈ maximalIdeal S) (j : ℕ)
    [Subsingleton (Ext.{u} (ModuleCat.of S (QuotSMulTop a M))
      (ModuleCat.of S S) (j + 1))] :
    Subsingleton (Ext.{u} M (ModuleCat.of S S) j) := by
  let T := M.smulShortComplex a
  have hT : T.ShortExact := ha.smulShortComplex_shortExact
  let : Subsingleton (Ext.{u} T.X₃ (ModuleCat.of S S) (j + 1)) := by
    change Subsingleton (Ext.{u} (ModuleCat.of S (QuotSMulTop a M))
      (ModuleCat.of S S) (j + 1))
    infer_instance
  let E := Ext.{u} M (ModuleCat.of S S) j
  have hsurj : Function.Surjective (fun x : E => a • x) := by
    intro x
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁.{u} hT (ModuleCat.of S S)
      x (n₁ := j + 1) (by omega) (Subsingleton.elim _ _)
    refine ⟨y, ?_⟩
    change (Ext.mk₀ (a • 𝟙 M)).comp y (zero_add j) = x at hy
    have hscalar : (Ext.mk₀.{u} (a • 𝟙 M)).comp y (zero_add j) = a • y := by
      rw [Ext.mk₀_smul (R := S)]
      exact (Ext.smul_comp (R := S) (Ext.mk₀.{u} (𝟙 M)) y (zero_add j) a).trans
        (congrArg (fun z => a • z) (Ext.mk₀_id_comp y))
    exact hscalar.symm.trans hy
  have htop : (⊤ : Submodule S E) = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {a}) _
      Module.Finite.fg_top
    · rw [Submodule.ideal_span_singleton_smul]
      intro x _
      obtain ⟨y, rfl⟩ := hsurj x
      exact Submodule.smul_mem_pointwise_smul y a _ Submodule.mem_top
    · rw [Ideal.span_le, Set.singleton_subset_iff,
        IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact ham
  apply subsingleton_of_forall_eq 0
  intro x
  exact (show x ∈ (⊥ : Submodule S E) from htop ▸ Submodule.mem_top)

end ModuleCat

namespace IsRegularLocalRing

/-- Finite-length sources have native Ext into the ring only in the actual
finite dimension of the regular local ring. -/
theorem subsingleton_ext_of_isFiniteLength_ne_dimension
    (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (M : ModuleCat.{u} S) (hM : IsFiniteLength S M)
    (d : ℕ) (hd : ringKrullDim S = (d : ℕ)) (j : ℕ) (hj : j ≠ d) :
    Subsingleton (Ext.{u} M (ModuleCat.of S S) j) := by
  by_cases hjd : j < d
  · exact subsingleton_ext_of_isFiniteLength S M hM d hd j hjd
  · let : IsNoetherian S M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
    let : HasProjectiveDimensionLE M d := (projectiveDimension_le_iff M d).mp
      (projectiveDimension_le_dimension d S hd M)
    exact HasProjectiveDimensionLT.subsingleton M (d + 1) j (by omega)
      (ModuleCat.of S S)

/-- A genuine regular sequence with finite-length quotient gives concentration
in ambient dimension minus its length, using its actual scalar quotients. -/
theorem subsingleton_ext_of_regular_sequence
    (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (M : ModuleCat.{u} S) [Module.Finite S M]
    (rs : List S) (hreg : IsWeaklyRegular M rs)
    (hmem : ∀ a ∈ rs, a ∈ maximalIdeal S)
    (hQ : IsFiniteLength S (M ⧸ (Ideal.ofList rs • ⊤ : Submodule S M)))
    (d : ℕ) (hd : ringKrullDim S = (d : ℕ)) (j : ℕ)
    (hj : j + rs.length ≠ d) :
    Subsingleton (Ext.{u} M (ModuleCat.of S S) j) := by
  induction rs generalizing M j with
  | nil =>
    have heq : (Ideal.ofList ([] : List S) • ⊤ : Submodule S M) = ⊥ := by simp
    have hM : IsFiniteLength S M := (Submodule.quotEquivOfEqBot _ heq).isFiniteLength hQ
    exact subsingleton_ext_of_isFiniteLength_ne_dimension S M hM d hd j (by simpa using hj)
  | cons a rs ih =>
    obtain ⟨ha, hrest⟩ := (isWeaklyRegular_cons_iff M a rs).mp hreg
    let N := ModuleCat.of S (QuotSMulTop a M)
    have hQN : IsFiniteLength S
        (N ⧸ (Ideal.ofList rs • ⊤ : Submodule S N)) :=
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a rs).isFiniteLength hQ
    let : Subsingleton (Ext.{u} N (ModuleCat.of S S) (j + 1)) :=
      ih N hrest (fun b hb => hmem b (List.mem_cons_of_mem a hb)) hQN (j + 1)
        (by simp only [List.length_cons] at hj; omega)
    exact ModuleCat.subsingleton_ext_of_source_quotSMulTop M a ha
      (hmem a (List.mem_cons_self)) j

end IsRegularLocalRing

namespace IsIntegrallyClosed

/-- A normal local domain of dimension at most two has an actual regular
parameter list of its dimension, with maximal radical. -/
theorem exists_regular_parameter_list_of_dimension_le_two
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsDomain B] [IsIntegrallyClosed B]
    (r : ℕ) (hr : ringKrullDim B = (r : ℕ)) (hr2 : r ≤ 2) :
    ∃ rs : List B, rs.length = r ∧
      (∀ a ∈ rs, a ∈ maximalIdeal B) ∧
      (Ideal.ofList rs).radical = maximalIdeal B ∧ IsRegular B rs := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  · obtain ⟨s, hs, hrad⟩ := exists_parameter_finset B 0 hr
    have hs0 : s = ∅ := Finset.card_eq_zero.mp hs
    exact ⟨[], rfl, by simp, by simpa [hs0] using hrad, IsRegular.nil B B⟩
  · let : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr hr.le
    obtain ⟨a, ha, hrad⟩ := exists_principal_parameter_of_dimLE_one B
    have ha0 : a ≠ 0 := by
      intro hz
      have hm : maximalIdeal B = ⊥ := by simpa [hz] using hrad.symm
      have hdim0 := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hm)
      rw [hr] at hdim0
      norm_num at hdim0
    have haReg : IsSMulRegular B a := by
      apply IsSMulRegular.of_right_eq_zero_of_smul
      intro x hx
      change a * x = 0 at hx
      exact (mul_eq_zero.mp hx).resolve_left ha0
    have hmem : ∀ x ∈ [a], x ∈ maximalIdeal B := by
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact ha
    refine ⟨[a], rfl, hmem, ?_,
      IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal B hmem
        (IsWeaklyRegular.cons haReg (IsWeaklyRegular.nil B _))⟩
    simpa only [Ideal.ofList_singleton] using hrad
  · let : Ring.KrullDimLE 2 B := Ring.krullDimLE_iff.mpr hr.le
    have hm : maximalIdeal B ≠ ⊥ := by
      intro hz
      have hdim0 := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hz)
      rw [hr] at hdim0
      norm_num at hdim0
    obtain ⟨a, ha, ha0⟩ := (maximalIdeal B).ne_bot_iff.mp hm
    obtain ⟨b, hb, hparam⟩ := exists_parameter_pair_containing B a ha0 ha
    have hrad : (Ideal.ofList [a, b]).radical = maximalIdeal B := by
      simpa only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq] using hparam
    have hmem : ∀ x ∈ [a, b], x ∈ maximalIdeal B := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · obtain rfl := List.mem_singleton.mp hx
        exact hb
    exact ⟨[a, b], rfl, hmem, hrad,
      isRegular_pair_of_radical_eq_maximalIdeal a b ha0 (by simp [hr]) hrad⟩

end IsIntegrallyClosed

namespace IsLocalRing

/-- A maximal-primary quotient of an actual finite local algebra has finite
length over the source, with the original scalar action. -/
theorem isFiniteLength_quotient_of_radical_eq_maximalIdeal
    {S B : Type u} [CommRing S] [CommRing B]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalRing B]
    [Algebra S B] [Module.Finite S B] [IsLocalHom (algebraMap S B)]
    (I : Ideal B) (hI : I.radical = maximalIdeal B) :
    IsFiniteLength S (B ⧸ I) := by
  let : Module.Finite S (B ⧸ I) :=
    Module.Finite.of_surjective (I.mkQ.restrictScalars S) I.mkQ_surjective
  have hrad : (Module.annihilator S (B ⧸ I)).radical = maximalIdeal S := by
    rw [← Module.comap_annihilator (R₀ := S) (R := B) (M := B ⧸ I),
      Ideal.annihilator_quotient, ← Ideal.comap_radical, hI,
      IsLocalRing.maximalIdeal_comap]
  apply Module.finiteLength_of_support_maximal S (B ⧸ I)
  intro p hp
  have hm : maximalIdeal S ≤ p.asIdeal := by
    rw [← hrad]
    exact p.isPrime.radical_le_iff.mpr (Module.mem_support_iff_of_finite.mp hp)
  have heq : p.asIdeal = maximalIdeal S :=
    le_antisymm (le_maximalIdeal_of_isPrime p.asIdeal) hm
  rw [heq]
  infer_instance

/-- The actual quotient by a lifted parameter list has finite length over the
source. The equivalence uses the mapped ideal and restriction of scalars. -/
theorem isFiniteLength_quotient_ofList_of_radical_eq_maximalIdeal
    {S B : Type u} [CommRing S] [CommRing B]
    [IsNoetherianRing S] [IsLocalRing S] [IsLocalRing B]
    [Algebra S B] [Module.Finite S B] [IsLocalHom (algebraMap S B)]
    (rs : List S)
    (hrad : (Ideal.ofList (rs.map (algebraMap S B))).radical = maximalIdeal B) :
    IsFiniteLength S (B ⧸ (Ideal.ofList rs • ⊤ : Submodule S B)) := by
  let I := Ideal.ofList (rs.map (algebraMap S B))
  have hI : IsFiniteLength S (B ⧸ I) :=
    isFiniteLength_quotient_of_radical_eq_maximalIdeal I hrad
  have heq : (Ideal.ofList rs • ⊤ : Submodule S B) = I.restrictScalars S := by
    rw [Ideal.smul_top_eq_map, Ideal.map_ofList]
  let e : (B ⧸ (Ideal.ofList rs • ⊤ : Submodule S B)) ≃ₗ[S] B ⧸ I :=
    (Submodule.quotEquivOfEq _ _ heq).trans (Submodule.Quotient.restrictScalarsEquiv S I)
  exact e.symm.isFiniteLength hI

end IsLocalRing

namespace IsRegularLocalRing

/-- The original quotient module of a regular local ring by a surjective local
map to a normal local domain of dimension at most two has Ext only in the
ambient dimension minus the target dimension. Its parameters are constructed,
and all scalar actions come from this same map. -/
theorem subsingleton_ext_of_surjective_normal_dimension_le_two
    (S B : Type u) [CommRing S] [CommRing B] [IsRegularLocalRing S]
    [IsLocalRing B] [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra S B] [IsLocalHom (algebraMap S B)]
    (hsurj : Function.Surjective (algebraMap S B))
    (d r : ℕ) (hd : ringKrullDim S = (d : ℕ)) (hr : ringKrullDim B = (r : ℕ))
    (hr2 : r ≤ 2) (j : ℕ) (hj : j + r ≠ d) :
    Subsingleton (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) j) := by
  let : Module.Finite S B := Module.Finite.of_surjective (Algebra.linearMap S B) hsurj
  obtain ⟨ys, hlen, hmem, hrad, hreg⟩ :=
    IsIntegrallyClosed.exists_regular_parameter_list_of_dimension_le_two B r hr hr2
  obtain ⟨rs, hrs⟩ := hsurj.list_map ys
  have hlenS : rs.length = r := by rw [← hlen, ← hrs, List.length_map]
  have hmemS : ∀ a ∈ rs, a ∈ maximalIdeal S := by
    intro a ha
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap S B)]
    change algebraMap S B a ∈ maximalIdeal B
    apply hmem
    rw [← hrs]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hregS : IsWeaklyRegular B rs := by
    apply (isWeaklyRegular_map_algebraMap_iff B B rs).mp
    rw [hrs]
    exact hreg.toIsWeaklyRegular
  have hQS : IsFiniteLength S (B ⧸ (Ideal.ofList rs • ⊤ : Submodule S B)) :=
    isFiniteLength_quotient_ofList_of_radical_eq_maximalIdeal rs (by rwa [hrs])
  exact subsingleton_ext_of_regular_sequence S (ModuleCat.of S B) rs hregS hmemS hQS
    d hd j (by simpa only [hlenS] using hj)

end IsRegularLocalRing

namespace RingHom

/-- The concentration theorem for a specified surjective local ring map.
The source module is formed using the algebra structure induced by `f`. -/
theorem subsingleton_ext_of_surjective_normal_dimension_le_two
    {S B : Type u} [CommRing S] [CommRing B] [IsRegularLocalRing S]
    [IsLocalRing B] [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B]
    (f : S →+* B) [IsLocalHom f] (hf : Function.Surjective f)
    (d r : ℕ) (hd : ringKrullDim S = (d : ℕ)) (hr : ringKrullDim B = (r : ℕ))
    (hr2 : r ≤ 2) (j : ℕ) (hj : j + r ≠ d) :
    letI := f.toAlgebra
    Subsingleton (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) j) := by
  let := f.toAlgebra
  exact IsRegularLocalRing.subsingleton_ext_of_surjective_normal_dimension_le_two
    S B hf d r hd hr hr2 j hj

/-- The same actual quotient concentration in another specified Ext size.
The native change-of-universe equivalence transports the standard-size result;
no definitional equality between Ext sizes is assumed. -/
theorem subsingleton_ext_of_surjective_normal_dimension_le_two_chgUniv
    {S B : Type u} [CommRing S] [CommRing B] [IsRegularLocalRing S]
    [IsLocalRing B] [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B]
    [HasExt.{w} (ModuleCat.{u} S)]
    (f : S →+* B) [IsLocalHom f] (hf : Function.Surjective f)
    (d r : ℕ) (hd : ringKrullDim S = (d : ℕ)) (hr : ringKrullDim B = (r : ℕ))
    (hr2 : r ≤ 2) (j : ℕ) (hj : j + r ≠ d) :
    letI := f.toAlgebra
    Subsingleton (Ext.{w} (ModuleCat.of S B) (ModuleCat.of S S) j) := by
  let := f.toAlgebra
  let : Subsingleton (Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) j) :=
    f.subsingleton_ext_of_surjective_normal_dimension_le_two hf d r hd hr hr2 j hj
  exact (Ext.chgUniv.{u, w} :
    Ext.{w} (ModuleCat.of S B) (ModuleCat.of S S) j ≃
      Ext.{u} (ModuleCat.of S B) (ModuleCat.of S S) j).subsingleton

end RingHom

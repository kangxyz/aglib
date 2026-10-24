/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Order.Zorn
public import Mathlib.RingTheory.IsAdjoinRoot

/-!
# A degree-p coefficient complement for one non-pth-power element

For `c ∉ kᵖ`, a maximal subfield containing `kᵖ` and avoiding `c` has
`k = E(c)`. The actual inclusion `E → k` admits the monic presentation
`X ^ p - C cᵖ`, with root `c`, and the basis `1, c, ..., c ^ (p - 1)`.
Finiteness of the ambient extension is a conclusion, not an input.
-/

@[expose] public noncomputable section

open Module Polynomial

namespace Subfield

variable {k : Type*} [Field k]

private theorem exists_maximal_avoiding (P : Subfield k) (c : k) (hc : c ∉ P) :
    ∃ E : Subfield k, Maximal (fun F : Subfield k => P ≤ F ∧ c ∉ F) E := by
  classical
  apply zorn_le₀ {F : Subfield k | P ≤ F ∧ c ∉ F}
  intro C hC hchain
  rcases C.eq_empty_or_nonempty with hC0 | hCne
  · subst C
    exact ⟨P, ⟨le_rfl, hc⟩, by simp⟩
  · have hdir : DirectedOn (· ≤ ·) C := by
      intro F hF G hG
      by_cases hFG : F = G
      · subst G
        exact ⟨F, hF, le_rfl, le_rfl⟩
      · rcases hchain hF hG hFG with hFG | hGF
        · exact ⟨G, hG, hFG, le_rfl⟩
        · exact ⟨F, hF, le_rfl, hGF⟩
    refine ⟨sSup C, ⟨?_, ?_⟩, fun F hF => le_sSup hF⟩
    · obtain ⟨F, hF⟩ := hCne
      exact (hC hF).1.trans (le_sSup hF)
    · intro hcSup
      obtain ⟨F, hF, hcF⟩ := (Subfield.mem_sSup_of_directedOn hCne hdir).mp hcSup
      exact (hC hF).2 hcF

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The literal pth power, regarded as an element of a subfield containing the Frobenius image. -/
def frobeniusCoefficient (E : Subfield k) (hE : (frobenius k p).fieldRange ≤ E)
    (x : k) : E :=
  ⟨x ^ p, hE (RingHom.mem_fieldRange.mpr ⟨x, rfl⟩)⟩

@[simp]
theorem coe_frobeniusCoefficient (E : Subfield k)
    (hE : (frobenius k p).fieldRange ≤ E) (x : k) :
    (frobeniusCoefficient p E hE x : k) = x ^ p := rfl

/-- Containment of the Frobenius image gives the original inclusion an exponent-one witness. -/
theorem purelyInseparable_of_frobenius_le (E : Subfield k)
    (hE : (frobenius k p).fieldRange ≤ E) : IsPurelyInseparable E k := by
  apply (isPurelyInseparable_iff_pow_mem E p).mpr
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact ⟨frobeniusCoefficient p E hE x, rfl⟩

private theorem minpoly_of_frobenius_le (E : Subfield k)
    (hE : (frobenius k p).fieldRange ≤ E) (x : k) (hx : x ∉ E) :
    minpoly E x = (X : E[X]) ^ p - C (frobeniusCoefficient p E hE x) := by
  let : IsPurelyInseparable E k := purelyInseparable_of_frobenius_le p E hE
  have hpow : x ^ p ^ 1 ∈ (algebraMap E k).range := by
    rw [pow_one]
    exact ⟨frobeniusCoefficient p E hE x, rfl⟩
  have hle : IsPurelyInseparable.elemExponent E x ≤ 1 :=
    IsPurelyInseparable.elemExponent_le_of_pow_mem' p hpow
  have hne : IsPurelyInseparable.elemExponent E x ≠ 0 := by
    intro hzero
    have hm := IsPurelyInseparable.elemExponent_def' E p x
    rw [hzero, pow_zero, pow_one] at hm
    obtain ⟨a, ha⟩ := hm
    exact hx (ha ▸ a.property)
  have hexp : IsPurelyInseparable.elemExponent E x = 1 :=
    Nat.le_antisymm hle (Nat.one_le_iff_ne_zero.mpr hne)
  have hcoeff : IsPurelyInseparable.elemReduct E x = frobeniusCoefficient p E hE x := by
    apply Subtype.ext
    change algebraMap E k (IsPurelyInseparable.elemReduct E x) = x ^ p
    simpa only [hexp, pow_one] using IsPurelyInseparable.algebraMap_elemReduct_eq' E p x
  rw [IsPurelyInseparable.minpoly_eq' E p x, hexp, pow_one, hcoeff]

private theorem finrank_adjoin_of_frobenius_le (E : Subfield k)
    (hE : (frobenius k p).fieldRange ≤ E) (x : k) (hx : x ∉ E) :
    Module.finrank E (IntermediateField.adjoin E {x}) = p := by
  let : IsPurelyInseparable E k := purelyInseparable_of_frobenius_le p E hE
  rw [IntermediateField.adjoin.finrank (IsPurelyInseparable.isIntegral' E x),
    minpoly_of_frobenius_le p E hE x hx, natDegree_X_pow_sub_C]

/-- A maximal subfield avoiding the specified non-power has that element as a primitive element. -/
theorem adjoin_eq_top_of_maximal_avoiding_frobenius (E : Subfield k) (c : k)
    (hE : Maximal (fun F : Subfield k => (frobenius k p).fieldRange ≤ F ∧ c ∉ F) E) :
    IntermediateField.adjoin E {c} = ⊤ := by
  let : IsPurelyInseparable E k := purelyInseparable_of_frobenius_le p E hE.prop.1
  apply top_unique
  intro x hx
  by_cases hxE : x ∈ E
  · exact (IntermediateField.adjoin E {c}).algebraMap_mem ⟨x, hxE⟩
  · let Ex : IntermediateField E k := IntermediateField.adjoin E {x}
    have hEEx : E ≤ Ex.toSubfield := by
      intro y hy
      exact Ex.algebraMap_mem ⟨y, hy⟩
    have hcEx : c ∈ Ex := by
      by_contra hcEx
      have hprop : (frobenius k p).fieldRange ≤ Ex.toSubfield ∧ c ∉ Ex.toSubfield :=
        ⟨hE.prop.1.trans hEEx, hcEx⟩
      have hExE : Ex.toSubfield ≤ E := (hE.eq_of_le hprop hEEx).ge
      exact hxE (hExE (IntermediateField.mem_adjoin_simple_self E x))
    have hle : IntermediateField.adjoin E {c} ≤ Ex :=
      IntermediateField.adjoin_simple_le_iff.mpr hcEx
    let : FiniteDimensional E Ex :=
      IntermediateField.adjoin.finiteDimensional (IsPurelyInseparable.isIntegral' E x)
    have heq : IntermediateField.adjoin E {c} = Ex :=
      IntermediateField.eq_of_le_of_finrank_eq hle (by
        rw [finrank_adjoin_of_frobenius_le p E hE.prop.1 c hE.prop.2]
        exact (finrank_adjoin_of_frobenius_le p E hE.prop.1 x hxE).symm)
    rw [heq]
    exact IntermediateField.mem_adjoin_simple_self E x

/-- A coefficient not in the Frobenius image has an actual maximal avoiding complement. -/
theorem exists_nonPowerComplement (c : k) (hc : c ∉ (frobenius k p).fieldRange) :
    ∃ E : Subfield k,
      Maximal (fun F : Subfield k => (frobenius k p).fieldRange ≤ F ∧ c ∉ F) E ∧
      IntermediateField.adjoin E {c} = ⊤ := by
  obtain ⟨E, hE⟩ := exists_maximal_avoiding (frobenius k p).fieldRange c hc
  exact ⟨E, hE, adjoin_eq_top_of_maximal_avoiding_frobenius p E c hE⟩

/-- The monic root presentation uses evaluation at the original coefficient under `E.subtype`. -/
def nonPowerComplementPresentation (E : Subfield k) (c : k)
    (hE : Maximal (fun F : Subfield k => (frobenius k p).fieldRange ≤ F ∧ c ∉ F) E) :
    IsAdjoinRootMonic k
      ((X : E[X]) ^ p - C (frobeniusCoefficient p E hE.prop.1 c)) := by
  let : IsPurelyInseparable E k := purelyInseparable_of_frobenius_le p E hE.prop.1
  let h := IsAdjoinRoot.mkOfPrimitiveElement (IsPurelyInseparable.isIntegral' E c)
    (adjoin_eq_top_of_maximal_avoiding_frobenius p E c hE)
  exact
    { map := h.map
      map_surjective := h.map_surjective
      ker_map := by
        simpa only [minpoly_of_frobenius_le p E hE.prop.1 c hE.prop.2] using h.ker_map
      monic := monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero }

@[simp]
theorem nonPowerComplementPresentation_root (E : Subfield k) (c : k)
    (hE : Maximal (fun F : Subfield k => (frobenius k p).fieldRange ≤ F ∧ c ∉ F) E) :
    (nonPowerComplementPresentation p E c hE).root = c := by
  change aeval c (X : E[X]) = c
  simp

/-- The exact coefficient-field basis is indexed by `Fin p` and consists of powers of `c`. -/
def nonPowerComplementBasis (E : Subfield k) (c : k)
    (hE : Maximal (fun F : Subfield k => (frobenius k p).fieldRange ≤ F ∧ c ∉ F) E) :
    Basis (Fin p) E k :=
  (nonPowerComplementPresentation p E c hE).basis.reindex
    (finCongr (by rw [natDegree_X_pow_sub_C]))

@[simp]
theorem nonPowerComplementBasis_apply (E : Subfield k) (c : k)
    (hE : Maximal (fun F : Subfield k => (frobenius k p).fieldRange ≤ F ∧ c ∉ F) E)
    (i : Fin p) : nonPowerComplementBasis p E c hE i = c ^ (i : ℕ) := by
  rw [nonPowerComplementBasis, Basis.reindex_apply, IsAdjoinRootMonic.basis_apply,
    nonPowerComplementPresentation_root]
  rfl

/-- Finiteness of the ambient coefficient extension is derived from the constructed basis. -/
theorem nonPowerComplement_finiteDimensional (E : Subfield k) (c : k)
    (hE : Maximal (fun F : Subfield k => (frobenius k p).fieldRange ≤ F ∧ c ∉ F) E) :
    FiniteDimensional E k :=
  Module.Finite.of_basis (nonPowerComplementBasis p E c hE)

/-- The original ambient coefficient extension has degree exactly `p`. -/
theorem nonPowerComplement_finrank (E : Subfield k) (c : k)
    (hE : Maximal (fun F : Subfield k => (frobenius k p).fieldRange ≤ F ∧ c ∉ F) E) :
    Module.finrank E k = p := by
  rw [Module.finrank_eq_card_basis (nonPowerComplementBasis p E c hE), Fintype.card_fin]

end Subfield

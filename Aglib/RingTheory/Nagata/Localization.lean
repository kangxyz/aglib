/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.Basic
public import Aglib.RingTheory.IntegralClosure.Localization
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Japanese and Nagata properties under localization

Japanese localization retains the original extension field and the literal
inclusion of integral closures. Nagata localization applies it to the actual
prime quotient maps and derives Noetherianity by localization.

All rings and tested fields lie in one ambient universe, with auxiliary test
universe zero. Neither result uses finite-type Nagata stability or a
complete-ring normalization theorem.
-/

@[expose] public noncomputable section

universe u

private theorem isFractionRing_of_domain_localization
    {R S K : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [CommRing K] [Algebra R S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] (M : Submonoid R) [IsLocalization M S]
    [IsFractionRing S K] : IsFractionRing R K := by
  have hM : M ≤ nonZeroDivisors R := by
    intro x hx
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    exact (IsLocalization.map_units S ⟨x, hx⟩).ne_zero (by simp [hzero])
  have hinj := IsLocalization.injective S hM
  have hsub : (nonZeroDivisors S).comap (algebraMap R S) = nonZeroDivisors R :=
    le_antisymm (comap_nonZeroDivisors_le_of_injective hinj)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
  change IsLocalization (nonZeroDivisors R) K
  rw [← hsub]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors S) K (fun _ hx => hx.mem_nonZeroDivisors)

/-- A domain localization of a Japanese domain is Japanese, retaining
the original coefficient maps and without assuming Noetherianity. -/
theorem IsJapaneseRing.of_isLocalization
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (h : IsJapaneseRing.{u, 0} R) : IsJapaneseRing.{u, 0} S := by
  intro L hL hFL hSL hT hfin
  let : IsFractionRing R (FractionRing S) :=
    isFractionRing_of_domain_localization (R := R) (S := S) (K := FractionRing S) M
  let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R (FractionRing S) L :=
    IsScalarTower.to₁₃₄ R S (FractionRing S) L
  let : Module.Finite R (integralClosure R L) :=
    h.finite_integralClosure_of_isFractionRing (FractionRing S) L
  let : IsLocalizedModule M (integralClosure.scalarExtensionHom R S L).toLinearMap :=
    integralClosure.scalarExtensionHom_isLocalizedModule R S L M
  exact Module.Finite.of_isLocalizedModule (Rₚ := S) M
    (integralClosure.scalarExtensionHom R S L).toLinearMap

/-- Every localization of a Nagata ring is Nagata. The localization may
be the zero ring; no injectivity or domain hypothesis is imposed here. -/
theorem IsNagataRing.of_isLocalization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (h : IsNagataRing.{u, 0} R) : IsNagataRing.{u, 0} S := by
  refine ⟨IsLocalization.isNoetherianRing M S h.isNoetherianRing, ?_⟩
  intro q hq
  let p : Ideal R := q.comap (algebraMap R S)
  let : p.IsPrime := inferInstance
  let : Algebra (R ⧸ p) (S ⧸ q) := inferInstance
  let : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ p) M) (S ⧸ q) :=
    IsLocalization.of_surjective M S
      (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective rfl (by
        rw [Ideal.mk_ker, Ideal.mk_ker]
        exact (IsLocalization.map_under M S q).ge)
  exact IsJapaneseRing.of_isLocalization
    (Algebra.algebraMapSubmonoid (R ⧸ p) M) (h.isJapaneseRing_quotient p)

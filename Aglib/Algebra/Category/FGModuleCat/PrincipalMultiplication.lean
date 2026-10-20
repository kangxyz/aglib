/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Principal multiplication and its quotient in finite modules

Short exactness requires a nonzero scalar in a Noetherian domain; localization retains the
original maps.

Source: `lean/R5Lab/Aglib/Algebra/Category/FGModuleCat/PrincipalMultiplication.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `65cb7c1e5bc34aa9181c446020dfc54b613a292f9ef388f517ac9666ff690f83`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open _root_.ModuleCat (finiteModuleExactStructure)
attribute [local instance] Abelian.hasFiniteBiproducts
namespace FGModuleCat.PrincipalMultiplication
universe u

section ModuleSequence
variable (R : Type u) [CommRing R] (π : R)

abbrev rankOne : FGModuleCat.{u} R := FGModuleCat.of R R
abbrev principalQuotient : FGModuleCat.{u} R := FGModuleCat.of R (R ⧸ Ideal.span {π})

def mulPi : rankOne R ⟶ rankOne R := FGModuleCat.ofHom (LinearMap.mulLeft R π)
def quotientPi : rankOne R ⟶ principalQuotient R π :=
  FGModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span {π})).toLinearMap

@[simp] theorem mulPi_apply [IsDomain R] [IsNoetherianRing R] (x : R) : mulPi R π x = π*x := rfl
@[simp] theorem quotientPi_apply [IsDomain R] [IsNoetherianRing R] (x : R) :
    quotientPi R π x = Ideal.Quotient.mk (Ideal.span {π}) x := rfl

lemma mulPi_comp_quotientPi [IsDomain R] [IsNoetherianRing R] : mulPi R π ≫ quotientPi R π = 0 := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (Ideal.span {π}) (π*x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨x, rfl⟩)

/-- The literal principal multiplication/quotient complex in finite modules. -/
def multiplicationSequence [IsDomain R] [IsNoetherianRing R] : ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk (mulPi R π) (quotientPi R π) (mulPi_comp_quotientPi R π)

/-- Injectivity uses only pi != 0 in the domain. -/
theorem mulPi_injective
    [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) : Function.Injective (mulPi R π) := by
  intro x y h
  exact mul_left_cancel₀ hπ h

/-- This is the actual short exact sequence R --pi--> R -> R/(pi). -/
theorem multiplicationSequence_shortExact [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    (multiplicationSequence R π).ShortExact := by
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  have hm : Mono (U.map (mulPi R π)) :=
    (ModuleCat.mono_iff_injective _).mpr (mulPi_injective R π hπ)
  have he : Epi (U.map (quotientPi R π)) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (show Function.Surjective (Ideal.Quotient.mk (Ideal.span {π})) from
        Ideal.Quotient.mk_surjective)
  refine
    { exact := ?_
      mono_f := U.mono_of_mono_map hm
      epi_g := U.epi_of_epi_map he }
  apply ((multiplicationSequence R π).exact_map_iff_of_faithful U).mp
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  apply Submodule.ext
  intro r
  change R at r
  change (∃ x : R, π*x=r) ↔ Ideal.Quotient.mk (Ideal.span {π}) r = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩

/-- The selected multiplication sequence is a conflation in the original finite-module structure. -/
theorem multiplication_conflation [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    (finiteModuleExactStructure.{u,u} R).conflation (multiplicationSequence R π) :=
  multiplicationSequence_shortExact R π hπ

/-- Pi kills the ACTUAL quotient module; this is the support data before localization. -/
theorem pi_annihilates_quotient
    [IsDomain R] [IsNoetherianRing R] (q : R ⧸ Ideal.span {π}) : π • q = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mk (Ideal.span {π}) (π*r) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨r, rfl⟩)

/-- The actual quotient object belongs to the original Serre kernel of principal localization. -/
theorem quotient_is_supported [IsDomain R] [IsNoetherianRing R] :
    _root_.ModuleCat.FiniteLocalization.torsion (Submonoid.powers π) (principalQuotient R π) := by
  apply (ModuleCat.FiniteLocalization.torsion_powers_iff_uniform
    π (principalQuotient R π)).mpr
  refine ⟨1, ?_⟩
  intro q
  simpa using pi_annihilates_quotient R π q

/-- The original localization sends multiplication by pi to a genuine isomorphism. -/
theorem localized_mulPi_isIso [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    IsIso ((_root_.ModuleCat.FiniteLocalization.functor (Submonoid.powers π)).map (mulPi R π)) := by
  have hs := (multiplicationSequence_shortExact R π hπ).map_of_exact
    (_root_.ModuleCat.FiniteLocalization.functor (Submonoid.powers π))
  exact hs.isIso_f_iff.mpr (quotient_is_supported R π)

/-- This is the actual localized multiplication automorphism, not a chosen unit-group map. -/
def localizedPiAut [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    Aut ((_root_.ModuleCat.FiniteLocalization.functor (Submonoid.powers π)).obj (rankOne R)) :=
  letI := localized_mulPi_isIso R π hπ
  asIso ((_root_.ModuleCat.FiniteLocalization.functor (Submonoid.powers π)).map (mulPi R π))

end ModuleSequence
end FGModuleCat.PrincipalMultiplication

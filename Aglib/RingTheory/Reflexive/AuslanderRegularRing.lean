/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Reflexive.Auslander
public import Aglib.RingTheory.Reflexive.Localization
public import Aglib.RingTheory.Localization.EndomorphismPi
public import Aglib.RingTheory.KrullDimension.LocalDrop
public import Aglib.RingTheory.RegularLocalRing.Localization

/-!
# The Auslander criterion over a local regular ring

Induction on the finite local dimension supplies punctured freeness from the
actual localized endomorphism decomposition. The ambient `IsRegularRing`
hypothesis ensures that the induction applies to every prime localization.
This does not assert regularity of arbitrary localizations from an isolated
`IsRegularLocalRing` hypothesis, or global freeness over a nonlocal ring.
-/

@[expose] public section

noncomputable section

universe u

namespace ModuleCat

/-- The local regular-ring Auslander criterion with an explicit dimension. -/
theorem free_of_endomorphism_equiv_of_isRegularRing_of_dimension (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsRegularRing R],
      ringKrullDim R = (d : ℕ) →
      ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
        (r : ℕ), (Module.End R M ≃ₗ[R] (Fin r → M)) → Module.Free R M := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro R instR instLocal instRegular hd M instFinite instReflexive r eEnd
    let : IsRegularLocalRing R :=
      IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
    apply free_of_endomorphism_equiv_of_free_punctured R M r eEnd
    intro p hp
    obtain ⟨n, hn, hdim⟩ := IsLocalRing.exists_ringKrullDim_localization_lt d hd p hp
    let Rₚ := Localization.AtPrime p.asIdeal
    let Mₚ := LocalizedModule p.asIdeal.primeCompl M
    let : IsRegularRing Rₚ := IsRegularRing.regular_localization R Rₚ p.asIdeal.primeCompl
    let : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule
      p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    let : IsNoetherian R (Module.Dual R M) := isNoetherian_linearMap R R M
    let : Module.Finite R (Module.Dual R M) :=
      Module.IsNoetherian.finite R (Module.Dual R M)
    let : Module.FinitePresentation R (Module.Dual R M) :=
      Module.finitePresentation_of_finite R (Module.Dual R M)
    let : Module.IsReflexive Rₚ Mₚ := Module.IsReflexive.of_isLocalizedModule
      p.asIdeal.primeCompl Rₚ (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    exact ih n hn Rₚ hdim (ModuleCat.of Rₚ Mₚ) r
      (Module.End.localizedEquivPi p.asIdeal.primeCompl Rₚ
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) eEnd)

/-- A finite reflexive module over a local regular ring is free if its actual
endomorphism module is a finite power of itself. -/
theorem free_of_endomorphism_equiv_of_isRegularRing
    (R : Type u) [CommRing R] [IsLocalRing R] [IsRegularRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (eEnd : Module.End R M ≃ₗ[R] (Fin r → M)) : Module.Free R M := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
  exact free_of_endomorphism_equiv_of_isRegularRing_of_dimension
    (IsLocalRing.maximalIdeal R).spanFinrank R
    ((isRegularLocalRing_iff R).mp inferInstance).symm M r eEnd

/-- Every prime localization satisfies the free criterion. The original module
need not be free globally, and the coefficient ring need not be local. -/
theorem free_localizedModule_of_endomorphism_equiv_of_isRegularRing
    (R : Type u) [CommRing R] [IsRegularRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.IsReflexive R M]
    (r : ℕ) (eEnd : Module.End R M ≃ₗ[R] (Fin r → M))
    (p : Ideal R) [p.IsPrime] :
    Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  let Rₚ := Localization.AtPrime p
  let Mₚ := LocalizedModule p.primeCompl M
  let : IsRegularRing Rₚ := IsRegularRing.regular_localization R Rₚ p.primeCompl
  let : Module.Finite Rₚ Mₚ := Module.Finite.of_isLocalizedModule
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let : IsNoetherian R (Module.Dual R M) := isNoetherian_linearMap R R M
  let : Module.Finite R (Module.Dual R M) :=
    Module.IsNoetherian.finite R (Module.Dual R M)
  let : Module.FinitePresentation R (Module.Dual R M) :=
    Module.finitePresentation_of_finite R (Module.Dual R M)
  let : Module.IsReflexive Rₚ Mₚ := Module.IsReflexive.of_isLocalizedModule
    p.primeCompl Rₚ (LocalizedModule.mkLinearMap p.primeCompl M)
  exact free_of_endomorphism_equiv_of_isRegularRing Rₚ (ModuleCat.of Rₚ Mₚ) r
    (Module.End.localizedEquivPi p.primeCompl Rₚ
      (LocalizedModule.mkLinearMap p.primeCompl M) eEnd)

end ModuleCat

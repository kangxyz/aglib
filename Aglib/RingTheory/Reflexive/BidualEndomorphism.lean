/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.EndomorphismLocalization
public import Aglib.RingTheory.Reflexive.EvaluationLocalization
public import Aglib.RingTheory.Support.FiniteDefect

/-! The actual endomorphism action on a bidual and its finite defects
under punctured reflexivity. -/

@[expose] public section

noncomputable section

namespace Module.Dual

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The canonical action on the bidual, obtained by transposing the original action twice. -/
def doubleTranspose : Module.End R M →ₗ[R] Module.End R (Dual R (Dual R M)) :=
  transpose.comp transpose

/-- The action on the bidual extends the original action through evaluation. -/
@[simp]
theorem doubleTranspose_eval (f : Module.End R M) (x : M) :
    doubleTranspose R M f (eval R M x) = eval R M (f x) := rfl

/-- If evaluation becomes bijective, the original double-transpose endomorphism map
becomes bijective after the same localization. -/
theorem localized_doubleTranspose_bijective
    [Module.FinitePresentation R M] [Module.FinitePresentation R (Dual R (Dual R M))]
    (S : Submonoid R) (h : Function.Bijective (LocalizedModule.map S (eval R M))) :
    Function.Bijective (LocalizedModule.map S (doubleTranspose R M)) := by
  apply LinearMap.localized_endomorphismMap_bijective (Rₛ := Localization S)
    (Nₛ := LocalizedModule S (Dual R (Dual R M))) S
    (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S (Dual R (Dual R M)))
    (eval R M) (doubleTranspose R M) ?_ ?_
  · intro f
    apply LinearMap.ext
    intro x
    exact doubleTranspose_eval R M f x
  · unfold LocalizedModule.map at h
    exact h

/-- Punctured reflexivity makes the actual double-transpose action bijective
at every nonclosed prime. -/
theorem localized_doubleTranspose_bijective_punctured
    [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
    (hlocal : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.IsReflexive (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M))
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl (doubleTranspose R M)) := by
  let := Module.finitePresentation_of_finite R M
  let := Module.finitePresentation_of_finite R (Dual R M)
  let := Module.finitePresentation_of_finite R (Dual R (Dual R M))
  let := hlocal p hp
  apply localized_doubleTranspose_bijective
  exact localized_eval_bijective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)

end Module.Dual

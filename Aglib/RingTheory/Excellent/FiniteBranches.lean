/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.RegularMapStability
public import Aglib.RingTheory.AdicCompletion.FiniteSemilocal
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Regular completion maps on original finite-algebra branches

The original completed-base tensor/product equivalence is upgraded to an
algebra equivalence over the finite algebra using its coefficient equation.
A selected factor is its actual idempotent localization. Regular-map stability
then gives regularity of the original local branch's completion map.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace AdicCompletion.FiniteSemilocal

/-- The original tensor/product comparison with the finite algebra's
coefficient action, verified by the existing same-precision coefficient map. -/
def tensorEquivOverAlgebra
    (R S : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [IsNoetherianRing S] [Algebra R S] [Module.Finite R S] :
    (S ⊗[R] AdicCompletion (maximalIdeal R) R) ≃ₐ[S]
      ∀ q : Branch R S, Completed R S q := by
  let := fun q => baseAlgebra R S q
  let : Algebra (AdicCompletion (maximalIdeal R) R)
      (S ⊗[R] AdicCompletion (maximalIdeal R) R) := Algebra.TensorProduct.rightAlgebra
  exact
    { (tensorEquivRight R S).toRingEquiv with
      commutes' := fun s => by
        funext q
        exact tensorEquivRight_tmul_one R S s q }

/-- Every original local branch of a finite algebra has regular actual
completion map when the original local base completion map is regular.
The uncompleted selected localization is not assumed finite over the base. -/
theorem regularMap_completedBranch
    (R S : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S]
    (h : Algebra.IsRegularMap R (AdicCompletion (maximalIdeal R) R))
    (q : Branch R S) :
    Algebra.IsRegularMap (Local R S q) (Completed R S q) := by
  classical
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let C := AdicCompletion (maximalIdeal R) R
  let D := S ⊗[R] C
  let P := ∀ i : Branch R S, Completed R S i
  let e : D ≃ₐ[S] P := tensorEquivOverAlgebra R S
  let ev : P →ₐ[S] Completed R S q := Pi.evalAlgHom S (Completed R S) q
  let φ : D →ₐ[S] Completed R S q := ev.comp e.toAlgHom
  let : Algebra P (Completed R S q) := ev.toRingHom.toAlgebra
  let : Algebra D (Completed R S q) := φ.toRingHom.toAlgebra
  let : IsScalarTower S D (Completed R S q) := IsScalarTower.of_algHom φ
  let d : P := Pi.single q 1
  let : IsLocalization.Away d (Completed R S q) := by
    apply IsLocalization.away_of_isIdempotentElem
      (show IsIdempotentElem d from by
        change d * d = d
        funext i
        change d i * d i = d i
        by_cases hi : i = q
        · subst i
          simp [d]
        · have hz : d i = 0 := Pi.single_eq_of_ne hi 1
          rw [hz, mul_zero])
      (RingHom.ker_evalRingHom (Completed R S) q)
      ((Pi.evalRingHom (Completed R S) q).surjective)
  let δ : D := e.symm d
  let : IsLocalization.Away δ (Completed R S q) :=
    IsLocalization.of_ringEquiv_left e.toRingEquiv
      (M₁ := Submonoid.powers d) (M₂ := Submonoid.powers δ)
      (by simp [δ, Submonoid.map_powers]) (fun _ => rfl)
  have hD : Algebra.IsRegularMap S D := h.baseChange_of_finite R C S
  have hbranch : Algebra.IsRegularMap S (Completed R S q) :=
    hD.localization_target S D (Completed R S q) (Submonoid.powers δ)
  exact hbranch.localization_source S (Local R S q) (Completed R S q)
    (branchIdeal R S q).primeCompl

/-- The same result for a specified original prime over the closed point.
The native branch index is eliminated by its proved original-ideal equation. -/
theorem regularMap_localCompletion
    (R S : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S]
    (h : Algebra.IsRegularMap R (AdicCompletion (maximalIdeal R) R))
    (p : Ideal S) [p.IsPrime]
    (hp : p.comap (algebraMap R S) = maximalIdeal R) :
    Algebra.IsRegularMap (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) := by
  have hbranch := regularMap_completedBranch R S h (branchOfPrime R S p hp)
  let test : PrimeSpectrum S → Prop := fun x =>
    Algebra.IsRegularMap (Localization.AtPrime x.asIdeal)
      (AdicCompletion (maximalIdeal (Localization.AtPrime x.asIdeal))
        (Localization.AtPrime x.asIdeal))
  have he : (⟨branchIdeal R S (branchOfPrime R S p hp), inferInstance⟩ : PrimeSpectrum S) =
      ⟨p, inferInstance⟩ := PrimeSpectrum.ext (branchIdeal_branchOfPrime R S p hp)
  exact Eq.mp (congrArg test he) hbranch

end AdicCompletion.FiniteSemilocal

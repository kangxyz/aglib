/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingAcyclic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange.Higher

/-! # Original lower higher-image vanishing for an open injective summand

Exact native extension by zero makes genuine module restriction preserve
injectives. Relative acyclicity after forgetting scalars then gives the
original source vanishing. Only the specified lower-degree canonical exchange
is used to transport zero; arbitrary inverse image is not assumed to preserve
injectives, and no degree-q exchange is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge

/-- The original higher direct images of the forgotten open restriction of a
genuine injective module vanish in every positive degree. Injectivity is
obtained from the existing exact lower-shriek adjunction, not after forgetting. -/
theorem higherDirectImage_open_moduleInjective_isZero
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I]
    (r : ℕ) (hr : 0 < r) :
    IsZero ((higherDirectImage j r).obj
      ((SheafOfModules.toSheaf (constantRing U Λ)).obj
        ((moduleInverseImage j Λ).obj I))) := by
  let : Injective ((moduleInverseImage j Λ).obj I) :=
    (moduleLowerShriekAdjunction j Λ).map_injective I inferInstance
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact higherDirectImage_moduleInjective_isZero j Λ ((moduleInverseImage j Λ).obj I) s

/-- Lower-degree original exchange isomorphisms transport exactly the source
zero objects needed by the low-degree Leray edge. The interval is empty for
q=1, and no exchange or vanishing in degree q is an input. -/
theorem openSummand_lowerHigherImage_isZero_of_exchange
    {U X V T : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (j' : V ⟶ T) (b : T ⟶ X) (bU : V ⟶ U) (h : j' ≫ b = bU ≫ j)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I]
    (q : ℕ)
    (hIH : ∀ r : ℕ, 1 ≤ r → r < q →
      IsIso ((higherBaseChangeMap j j' b bU h r).app
        ((SheafOfModules.toSheaf (constantRing U Λ)).obj
          ((moduleInverseImage j Λ).obj I)))) :
    ∀ r : ℕ, 1 ≤ r → r < q →
      IsZero ((higherDirectImage j' r).obj ((inverseImage bU).obj
        ((SheafOfModules.toSheaf (constantRing U Λ)).obj
          ((moduleInverseImage j Λ).obj I)))) := by
  intro r hr hrq
  let A := (SheafOfModules.toSheaf (constantRing U Λ)).obj
    ((moduleInverseImage j Λ).obj I)
  let β := (higherBaseChangeMap j j' b bU h r).app A
  let : IsIso β := hIH r hr hrq
  have hz := (inverseImage b).map_isZero
    (higherDirectImage_open_moduleInjective_isZero j Λ I r (by omega))
  exact hz.of_iso (asIso β).symm

end AlgebraicGeometry.Scheme.EtaleCohomology

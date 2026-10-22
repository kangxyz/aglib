/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationMap
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Native henselian rings and their geometric local henselizations

The self-henselization equivalence is constructed from the proved local
universal property. Localization at the maximal ideal is the native
localization at units. No approximation or excellence assumption is used.
-/

@[expose] public noncomputable section

universe u

namespace Henselization

variable (R : Type u) [CommRing R] [HenselianLocalRing R]

/-- For a henselian local ring, its actual henselization unit is an equivalence. -/
def equivOfHenselian : R ≃+* Henselization R := by
  let g : Henselization R →+* R :=
    (existsUnique_local_ringHom (RingHom.id R)).choose
  have hg : IsLocalHom g ∧
      g.comp (algebraMap R (Henselization R)) = RingHom.id R :=
    (existsUnique_local_ringHom (RingHom.id R)).choose_spec.1
  letI : IsLocalHom g := hg.1
  have hleft (r : R) : g (algebraMap R (Henselization R) r) = r :=
    RingHom.congr_fun hg.2 r
  have hright : (algebraMap R (Henselization R)).comp g =
      RingHom.id (Henselization R) := by
    apply local_ringHom_ext
    ext r
    change algebraMap R (Henselization R) (g (algebraMap R (Henselization R) r)) =
      algebraMap R (Henselization R) r
    rw [hleft]
  exact
    { algebraMap R (Henselization R) with
      invFun := g
      left_inv := hleft
      right_inv := fun x => RingHom.congr_fun hright x }

@[simp] theorem equivOfHenselian_apply (r : R) :
    equivOfHenselian R r = algebraMap R (Henselization R) r := rfl

/-- The original coefficient ring is equivalent to the henselization of its
native maximal-ideal localization. -/
def nativeGeometricEquiv :
    R ≃+* Henselization (Localization.AtPrime (IsLocalRing.maximalIdeal R)) :=
  (equivOfHenselian R).trans
    (equivOfRingEquiv
      (IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
        (S := Localization.AtPrime (IsLocalRing.maximalIdeal R)) (by
          intro r hr
          exact IsLocalRing.notMem_maximalIdeal.mp
            (Ideal.mem_primeCompl_iff.mp hr))).toRingEquiv)

end Henselization

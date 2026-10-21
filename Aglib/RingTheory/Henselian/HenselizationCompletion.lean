/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationUniversal
public import Aglib.RingTheory.Henselian.Quadratic
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# The canonical map from henselization to completion

The actual henselization maps to maximal-ideal adic completion by its proved
universal property. Localness and completeness of the target are the native
completion theorems. No Noetherianity of the completion, injectivity, or
completion comparison equivalence is assumed or asserted here.
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace Henselization

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The canonical local algebra map from henselization to adic completion. -/
def toAdicCompletion :
    Henselization R →ₐ[R] AdicCompletion (maximalIdeal R) R := by
  letI : HenselianLocalRing (AdicCompletion (maximalIdeal R) R) :=
    HenselianLocalRing.of_isAdicComplete
  exact (existsUnique_local_algHom R (AdicCompletion (maximalIdeal R) R)).choose

instance toAdicCompletion_isLocalHom : IsLocalHom (toAdicCompletion R).toRingHom := by
  let : HenselianLocalRing (AdicCompletion (maximalIdeal R) R) :=
    HenselianLocalRing.of_isAdicComplete
  exact (existsUnique_local_algHom R (AdicCompletion (maximalIdeal R) R)).choose_spec.1

/-- The canonical map agrees literally with the original completion map on the base. -/
@[simp] theorem toAdicCompletion_comp_of :
    (toAdicCompletion R : Henselization R →+* AdicCompletion (maximalIdeal R) R).comp
        (of R) =
      algebraMap R (AdicCompletion (maximalIdeal R) R) := by
  apply RingHom.ext
  intro r
  exact (toAdicCompletion R).commutes r

/-- Among local maps respecting the original base, the map to completion is unique. -/
theorem toAdicCompletion_unique
    (f : Henselization R →ₐ[R] AdicCompletion (maximalIdeal R) R)
    [IsLocalHom f.toRingHom] : f = toAdicCompletion R := by
  let : HenselianLocalRing (AdicCompletion (maximalIdeal R) R) :=
    HenselianLocalRing.of_isAdicComplete
  exact (existsUnique_local_algHom R (AdicCompletion (maximalIdeal R) R)).choose_spec.2
    f inferInstance

end Henselization

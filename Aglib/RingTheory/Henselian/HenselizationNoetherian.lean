/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationCompletion
public import Aglib.RingTheory.AdicCompletion.NoetherianRing
public import Aglib.RingTheory.Etale.TargetFlat
public import Aglib.RingTheory.Flat.FilteredColimit
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Noetherianity of the actual henselization

The canonical local map to completion is faithfully flat: flatness descends
from the actual pointed etale stages along the actual filtered colimit.
Noetherianity then descends from the Noetherian completion. The proof does not
assume a completion comparison isomorphism or Noetherianity of henselization.
-/

@[expose] public section

noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace Henselization

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Completion is flat over the actual henselization, for the algebra structure
induced by its canonical local algebra map. -/
theorem flat_toAdicCompletion :
    letI : Algebra (Henselization R) (AdicCompletion (maximalIdeal R) R) :=
      (toAdicCompletion R).toRingHom.toAlgebra
    Module.Flat (Henselization R) (AdicCompletion (maximalIdeal R) R) := by
  let : Algebra (Henselization R) (AdicCompletion (maximalIdeal R) R) :=
    (toAdicCompletion R).toRingHom.toAlgebra
  let : Module (ringCocone R).pt (AdicCompletion (maximalIdeal R) R) :=
    inferInstanceAs (Module (Henselization R) (AdicCompletion (maximalIdeal R) R))
  apply Module.Flat.of_isColimit (PointedEtaleNeighborhood.ringDiagram R)
    (ringCoconeIsColimit R) (AdicCompletion (maximalIdeal R) R)
  intro X
  exact Algebra.Etale.flat_of_algHom ((toAdicCompletion R).comp (ι R X))

/-- The actual local henselization-to-completion map is faithfully flat. -/
theorem faithfullyFlat_toAdicCompletion :
    letI : Algebra (Henselization R) (AdicCompletion (maximalIdeal R) R) :=
      (toAdicCompletion R).toRingHom.toAlgebra
    Module.FaithfullyFlat (Henselization R) (AdicCompletion (maximalIdeal R) R) := by
  let : Algebra (Henselization R) (AdicCompletion (maximalIdeal R) R) :=
    (toAdicCompletion R).toRingHom.toAlgebra
  have : Module.Flat (Henselization R) (AdicCompletion (maximalIdeal R) R) :=
    flat_toAdicCompletion R
  have : IsLocalHom (algebraMap (Henselization R)
      (AdicCompletion (maximalIdeal R) R)) := toAdicCompletion_isLocalHom R
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The actual henselization of a Noetherian local ring is Noetherian. -/
theorem isNoetherianRing : IsNoetherianRing (Henselization R) := by
  let S := AdicCompletion (maximalIdeal R) R
  let : Algebra (Henselization R) S := (toAdicCompletion R).toRingHom.toAlgebra
  have : Module.FaithfullyFlat (Henselization R) S := faithfullyFlat_toAdicCompletion R
  have : IsNoetherianRing S := AdicCompletion.isNoetherianRing R (maximalIdeal R)
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (R := Henselization R) (A := S) (M := Henselization R) inferInstance

end Henselization

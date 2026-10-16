/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.BaseChangeLocus

/-!
# Basic-open original proper cohomology base change

For a proper coherent relatively flat coefficient over a Noetherian ring,
surjectivity of the original cohomology comparison at an actual prime's
residue field gives a basic-open neighbourhood where the original comparison
is invertible after every further ring map. The proper supplier internally
chooses one finite Cech model, and every map uses that same model and the
original morphism and coefficient. Neither reducedness nor locality of the
base is assumed. New target rings need not be flat or Noetherian.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (M : X.Modules) (hM : affineLocallyFiniteType X M)
  (hflat : Scheme.Modules.relativeFlat f M)

include hM hflat

/-- An original proper cohomology comparison that is surjective at the actual
residue field of a prime is invertible for every ring map factoring through one
basic-open neighbourhood. The finite Cech model is supplied internally. -/
theorem exists_basicOpen_moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_proper
    (q : ℕ) (p : PrimeSpectrum R)
    (hres : Epi (moduleCohomologyBaseChangeMap f
      (algebraMap R p.asIdeal.ResidueField) M q)) :
    ∃ r ∉ p.asIdeal,
      ∀ (B : Type u) [CommRing B] (τ : Localization.Away r →+* B),
        IsIso (moduleCohomologyBaseChangeMap f
          (τ.comp (algebraMap R (Localization.Away r))) M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.exists_basicOpen_moduleCohomologyBaseChangeMap_isIso_of_epi_residue
    hU hcover Equiv.ulift hflat q p hres

end AlgebraicGeometry.Scheme.Cohomology

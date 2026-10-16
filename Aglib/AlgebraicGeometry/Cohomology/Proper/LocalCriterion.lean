/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.LocalCriterion

/-!
# Original proper cohomology and base-change criteria over a local base

The proved proper finite-cover supplier internally constructs the same
finite-projective model. Its original residue-field comparison gives
arbitrary original base change and the adjacent-degree freeness criterion.
Degree zero uses the actual model lower bound. Reducedness is not assumed;
surjectivity of the original geometric residue map remains an explicit
mathematical hypothesis. New target rings need not be flat or Noetherian.
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

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (M : X.Modules) (hM : affineLocallyFiniteType X M)
  (hflat : Scheme.Modules.relativeFlat f M)

include hM hflat

/-- Surjectivity of the original residue-field comparison for a coherent relatively flat
proper coefficient gives invertibility of its original comparison after every ring map. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_proper (q : ℕ)
    (hres : Epi (moduleCohomologyBaseChangeMap f
      (algebraMap R (IsLocalRing.ResidueField R)) M q))
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.moduleCohomologyBaseChangeMap_isIso_of_epi_residue
    hU hcover Equiv.ulift hflat q hres σ

/-- Under surjectivity in degree `q+1`, unchanged proper cohomology in that degree is
free exactly when the original degree-`q` residue-field comparison is surjective. -/
theorem moduleCohomology_free_succ_iff_epi_residue_of_proper (q : ℕ)
    (hres : Epi (moduleCohomologyBaseChangeMap f
      (algebraMap R (IsLocalRing.ResidueField R)) M (q + 1))) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M (q + 1)
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) ↔
      Epi (moduleCohomologyBaseChangeMap f
        (algebraMap R (IsLocalRing.ResidueField R)) M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.free_moduleCohomology_succ_iff_epi_residue hU hcover Equiv.ulift hflat q hres

/-- Surjectivity of the original degree-zero residue-field comparison makes unchanged
proper degree-zero cohomology free over the local ring. -/
theorem moduleCohomology_free_zero_of_epi_residue_of_proper
    (hres : Epi (moduleCohomologyBaseChangeMap f
      (algebraMap R (IsLocalRing.ResidueField R)) M 0)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.free_moduleCohomology_zero_of_epi_residue hU hcover Equiv.ulift hflat hres

end AlgebraicGeometry.Scheme.Cohomology

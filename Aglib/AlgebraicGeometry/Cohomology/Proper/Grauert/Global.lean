/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Grauert.Global

/-!
# Original proper Grauert criteria over a reduced affine base

The proved proper supplier internally constructs the same actual finite-cover
model. Local constancy of the original ordinary fibre dimension gives native
projectivity and arbitrary original geometric base change. Actual proper
finiteness supplies finite generation over the Noetherian original base.
Reducedness is retained; no local-ring hypothesis is imposed.
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

variable {R : Type u} [CommRing R] [_root_.IsReduced R] [IsNoetherianRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (M : X.Modules) (hM : affineLocallyFiniteType X M)
  (hflat : Scheme.Modules.relativeFlat f M)

include hM hflat

/-- Over a reduced Noetherian affine base, locally constant original ordinary fibre
cohomology dimension makes unchanged proper cohomology finite projective. -/
theorem moduleCohomology_finite_projective_of_isLocallyConstant_of_proper (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) ∧
      Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact ⟨moduleCohomology_finite_of_proper R f M hM q,
    D.projective_moduleCohomology_of_isLocallyConstant_fiberDimension
      hU hcover Equiv.ulift hflat q h⟩

/-- Over the whole reduced Noetherian affine base, the original proper cohomology
base-change map is invertible in any degree of locally constant original fibre dimension.
The new ring need be neither flat nor Noetherian. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant_of_proper (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q))
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant
    hU hcover Equiv.ulift hflat q h σ

end AlgebraicGeometry.Scheme.Cohomology

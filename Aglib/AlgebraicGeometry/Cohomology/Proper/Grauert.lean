/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Grauert.Global
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Grauert

/-!
# Original proper Grauert freeness over a reduced local base

The same internally constructed proper model gives freeness of unchanged
cohomology in every degree with locally constant original ordinary fibre
dimension. Both reducedness and the local-ring hypothesis are retained.
The explicit nonreduced residue-surjectivity criterion is separate.
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

/-- Coherent relatively flat proper coefficients over a reduced Noetherian local ring
have free unchanged cohomology in every degree of locally constant original fibre dimension. -/
theorem moduleCohomology_free_of_isLocallyConstant_of_proper
    {R : Type u} [CommRing R] [_root_.IsReduced R] [IsLocalRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M)
    (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.free_moduleCohomology_of_isLocallyConstant_fiberDimension
    hU hcover Equiv.ulift hflat q h

end AlgebraicGeometry.Scheme.Cohomology

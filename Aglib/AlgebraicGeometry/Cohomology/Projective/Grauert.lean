/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Grauert.Global
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Grauert

/-!
# Grauert criteria over reduced affine and local bases

The global leaf proves finite projectivity and arbitrary original base
change over a reduced Noetherian affine base. This leaf adds freeness over
a local base. Both use the original fibre-cohomology dimension and actual
constructed universal model. The retained reducedness hypothesis is
essential for these constant-dimension criteria. General local-surjectivity
and open-neighbourhood criteria are separate interfaces.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Module AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] [_root_.IsReduced R] [IsLocalRing R]
    {ι : Type u} {X : Scheme.{u}} {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- The reduced local constant-dimension criterion makes the unchanged original
cohomology module free for a displayed actual universal model. -/
theorem ProjectiveCohomologyModel.free_moduleCohomology_of_isLocallyConstant_fiberDimension
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.free_moduleCohomology_of_isLocallyConstant_fiberDimension D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat q h

/-- Coherent relatively flat coefficients on an actual projective embedding over a
reduced Noetherian local ring have free original cohomology in each degree whose
original fibre-cohomology dimension is locally constant. -/
theorem moduleCohomology_free_of_isLocallyConstant_of_projectiveEmbedding
    [IsNoetherianRing R] (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  exact D.free_moduleCohomology_of_isLocallyConstant_fiberDimension e hflat q h

end AlgebraicGeometry.Scheme.Cohomology

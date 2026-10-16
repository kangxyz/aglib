/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChangeCriterion
public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Fibers
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Grauert.Global

/-!
# Grauert's criterion over a reduced affine base

For coherent relatively flat coefficients on an actual projective embedding
over a reduced Noetherian ring, local constancy of an original fibre-cohomology
dimension gives finite projective original cohomology and arbitrary original
cohomology base change. The base need not be local. The model-level arguments
need only the displayed actual universal finite-projective model, so they do
not require Noetherianity once that data is given.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Module AlgebraicGeometry
open CategoryTheory.ShortComplex
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] [_root_.IsReduced R]
    {ι : Type u} {X : Scheme.{u}} {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- Locally constant original fibre dimension gives projective original cohomology
over the whole reduced base, for the same actual universal model. -/
theorem ProjectiveCohomologyModel.projective_moduleCohomology_of_isLocallyConstant_fiberDimension
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.projective_moduleCohomology_of_isLocallyConstant_fiberDimension D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat q h

/-- Over a reduced base, locally constant original fibre dimension gives arbitrary
base change for the original geometric map on the same actual model. The base need
not be local, and the ring map need not be flat. -/
theorem ProjectiveCohomologyModel.moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q))
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat q h σ

/-- Original cohomology is finite projective when its original fibre dimension is
locally constant for coherent relatively flat coefficients on an actual projective
embedding over a reduced Noetherian ring. No locality assumption is needed. -/
theorem moduleCohomology_finite_projective_of_isLocallyConstant_of_projectiveEmbedding
    [IsNoetherianRing R] (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) ∧
      Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  exact ⟨moduleCohomology_finite_of_projectiveEmbedding R ι i n e f hf M hM q,
    D.projective_moduleCohomology_of_isLocallyConstant_fiberDimension e hflat q h⟩

/-- Over the whole reduced Noetherian affine base, the original cohomology base-change
map is invertible in every degree of locally constant original fibre dimension. The
proved projective supplier constructs the model internally. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant_of_projectiveEmbedding
    [IsNoetherianRing R] (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q))
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  exact D.moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant e hflat q h σ

end AlgebraicGeometry.Scheme.Cohomology

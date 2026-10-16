/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.BaseChangeCriterion
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Fibers
public import Aglib.Algebra.Homology.ShortComplex.BaseChange.Grauert.Global

/-!
# Grauert's reduced-base criterion on the same actual finite-cover model

Local constancy of the unchanged ordinary fibre-cohomology dimension gives
projectivity of original cohomology and arbitrary original geometric base
change over a reduced ring. The actual supplied model needs no additional
Noetherianity. Geometric Noetherian suppliers separately give finiteness;
projectivity alone is not used to infer it over a noncoherent ring.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Module AlgebraicGeometry
open CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] [_root_.IsReduced R]
    {ι : Type u} {X : Scheme.{u}} [X.IsSeparated] {U : ι → X.Opens}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- Locally constant original fibre dimension gives projective original cohomology
over the whole reduced base, for the same actual universal model. -/
theorem FiniteCechCohomologyModel.projective_moduleCohomology_of_isLocallyConstant_fiberDimension
    (D : FiniteCechCohomologyModel R ι X f U M n) [M.IsQuasicoherent]
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let S : ShortComplex (ModuleCat.{u} R) := D.complex.sc (q : ℤ)
  let : Module.Finite R S.X₁ := by
    change Module.Finite R (D.complex.X ((ComplexShape.up ℤ).prev (q : ℤ)))
    infer_instance
  let : Module.FinitePresentation R S.X₂ := by
    change Module.FinitePresentation R (D.complex.X (q : ℤ))
    exact Module.finitePresentation_of_projective R _
  let : Module.Finite R S.X₃ := by
    change Module.Finite R (D.complex.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  let : Module.Projective R S.X₃ := by
    change Module.Projective R (D.complex.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  have he : moduleFiberCohomologyDimension f M q = fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj D.complex).homology (q : ℤ)) :=
    funext (D.fiberCohomologyDimension_eq_finrank hU hcover e hflat q)
  rw [he] at h
  let : Module.Projective R (D.complex.homology (q : ℤ)) :=
    ShortComplex.projective_homology_of_isLocallyConstant_residueField_finrank.{u, 0} S h
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M q
  exact Module.Projective.of_equiv' (D.cohomologyLinearEquiv hU hcover e q)

/-- Over a reduced base, locally constant original fibre dimension gives arbitrary
base change for the original geometric map on the same actual model. The base need
not be local, and the ring map need not be flat. -/
theorem FiniteCechCohomologyModel.moduleCohomologyBaseChangeMap_isIso_of_isLocallyConstant
    (D : FiniteCechCohomologyModel R ι X f U M n) [M.IsQuasicoherent]
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q))
    {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let S : ShortComplex (ModuleCat.{u} R) := D.complex.sc (q : ℤ)
  let : Module.Finite R S.X₁ := by
    change Module.Finite R (D.complex.X ((ComplexShape.up ℤ).prev (q : ℤ)))
    infer_instance
  let : Module.FinitePresentation R S.X₂ := by
    change Module.FinitePresentation R (D.complex.X (q : ℤ))
    exact Module.finitePresentation_of_projective R _
  let : Module.Finite R S.X₃ := by
    change Module.Finite R (D.complex.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  let : Module.Projective R S.X₃ := by
    change Module.Projective R (D.complex.X ((ComplexShape.up ℤ).next (q : ℤ)))
    infer_instance
  have he : moduleFiberCohomologyDimension f M q = fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj D.complex).homology (q : ℤ)) :=
    funext (D.fiberCohomologyDimension_eq_finrank hU hcover e hflat q)
  rw [he] at h
  apply (D.moduleCohomologyBaseChangeMap_isIso_iff hU hcover e hflat σ q).mpr
  exact homologyBaseChangeMap_isIso_of_isLocallyConstant_residueField_finrank_of_isReduced.{u,
    0, u} σ S h

end AlgebraicGeometry.Scheme.Cohomology

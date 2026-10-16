/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Grauert.Global
public import Aglib.Algebra.Homology.CochainComplex.Grauert

/-!
# Original Grauert freeness over a reduced local base on the same model

Local constancy of unchanged ordinary fibre-cohomology dimension gives
freeness of original cohomology for this same actual finite-cover model.
Both reducedness and the local-ring hypothesis are retained. No additional
Noetherianity is required once the model is supplied. The explicit
nonreduced residue-surjectivity criterion remains a separate interface.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Module AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] [_root_.IsReduced R] [IsLocalRing R]
    {ι : Type u} {X : Scheme.{u}} [X.IsSeparated] {U : ι → X.Opens}
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- The reduced local constant-dimension criterion makes the unchanged original
cohomology module free for a displayed actual universal model. -/
theorem FiniteCechCohomologyModel.free_moduleCohomology_of_isLocallyConstant_fiberDimension
    (D : FiniteCechCohomologyModel R ι X f U M n) [M.IsQuasicoherent]
    (hU : ∀ j, IsAffineOpen (U j)) (hcover : iSup U = ⊤)
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ)
    (h : IsLocallyConstant (moduleFiberCohomologyDimension f M q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let (j : ℤ) : Module.Finite R (D.complex.X j) := D.finite_X j
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  have he : moduleFiberCohomologyDimension f M q = fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (.up ℤ)).obj D.complex).homology (q : ℤ)) :=
    funext (D.fiberCohomologyDimension_eq_finrank hU hcover e hflat q)
  rw [he] at h
  let : Module.Free R (D.complex.homology (q : ℤ)) :=
    CochainComplex.free_homology_of_isLocallyConstant_residueField_finrank.{u, 0}
      D.complex (q : ℤ) h
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M q
  exact Module.Free.of_equiv (D.cohomologyLinearEquiv hU hcover e q)

end AlgebraicGeometry.Scheme.Cohomology

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.Fibers
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Fibers.EulerCharacteristic
public import Aglib.Algebra.Homology.EulerCharacteristic.Cohomology
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.EulerCharacteristic

/-!
# Locally constant projective fibre Euler characteristics

For a coherent relatively flat coefficient on an actual projective
embedding over a Noetherian ring, the alternating sum of the original
fibre-cohomology dimensions is locally constant. The actual universal
finite-projective model proves the vanishing bound and identifies this
intrinsic numerical invariant with the existing native homological
Euler characteristic of every residue-field scalar extension.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Module AlgebraicGeometry
open HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
    {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- The original fibre Euler characteristic is the native homological Euler
characteristic of the same actual scalar-extended model. The actual strict bounds
prove finite support, including in projective dimension zero. -/
theorem ProjectiveCohomologyModel.moduleFiberEulerChar_eq_homologyEulerChar
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (p : PrimeSpectrum R) :
    moduleFiberEulerChar f M p = HomologicalComplex.homologyEulerChar
      (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (.up ℤ)).obj D.complex) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.moduleFiberEulerChar_eq_homologyEulerChar D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat p

/-- The intrinsic original fibre Euler characteristic is locally constant for the
displayed actual universal model, without additional Noetherian hypotheses on its data. -/
theorem ProjectiveCohomologyModel.isLocallyConstant_moduleFiberEulerChar
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) :
    IsLocallyConstant (moduleFiberEulerChar f M) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.isLocallyConstant_moduleFiberEulerChar D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat

/-- Original fibre Euler characteristics of coherent relatively flat coefficients on
an actual projective embedding over a Noetherian ring are locally constant. The proved
geometric supplier constructs the universal finite-projective model internally. -/
theorem isLocallyConstant_moduleFiberEulerChar_of_projectiveEmbedding
    [IsNoetherianRing R] (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    IsLocallyConstant (moduleFiberEulerChar f M) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  exact D.isLocallyConstant_moduleFiberEulerChar e hflat

end AlgebraicGeometry.Scheme.Cohomology

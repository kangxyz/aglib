/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChange
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.BaseChangeCriterion

/-!
# Detecting original cohomology base change on the actual projective model

The proved linear square identifies invertibility and surjectivity of the
original geometric cohomology base-change map with the same properties of
the native homology mate of the constructed model. The original cohomology
carriers stay in universe `u+1`, and the actual model stays in universe `u`.
The comparisons use the existing scalar-extension linear equivalences;
no alternate cohomology object or new base-change map is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

universe u

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
    {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
    (D : ProjectiveCohomologyModel R ι i f M n) (e : ι ≃ Fin (n + 1))
    (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B] (σ : R →+* B)

include e hflat

/-- Invertibility of the original cohomology base-change map is detected by the native
homology mate on the same actual finite-projective model. -/
theorem moduleCohomologyBaseChangeMap_isIso_iff (q : ℕ) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) ↔
      IsIso (extendScalarsHomologyMap σ D.complex (q : ℤ)) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.moduleCohomologyBaseChangeMap_isIso_iff D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ q

/-- Surjectivity of the original cohomology base-change map is detected by the original
native model mate. This applies to arbitrary ring maps before a degreewise isomorphism
criterion is known. -/
theorem moduleCohomologyBaseChangeMap_epi_iff (q : ℕ) :
    Epi (moduleCohomologyBaseChangeMap f σ M q) ↔
      Epi (extendScalarsHomologyMap σ D.complex (q : ℤ)) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.moduleCohomologyBaseChangeMap_epi_iff D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ q

end AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

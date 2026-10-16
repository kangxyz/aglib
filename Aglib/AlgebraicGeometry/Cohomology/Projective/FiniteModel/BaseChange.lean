/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.BaseChange

/-!
# The original cohomology base-change map on a constructed projective model

The sole shared finite-cover model supplies the native homology-mate
comparison. These original coordinate-cover names delegate to it. The mate agrees
with the original geometric cohomology base-change map under the original
model comparisons. This normalization holds for every ring map, without
assuming that scalar extension preserves homology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open HomologicalComplex AlgebraicGeometry.ProjectiveSpace
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

variable {R : Type u} [CommRing R] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
  {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} [M.IsQuasicoherent] {n : ℕ}
  (D : ProjectiveCohomologyModel R ι i f M n) (e : ι ≃ Fin (n + 1))
  (hflat : Scheme.Modules.relativeFlat f M) {B : Type u} [CommRing B] (σ : R →+* B)

/-- The literal model homology mate has the original ordinary geometric
pullback as its unit pure-tensor value in every degree. -/
theorem baseChangeCohomologyLinearEquiv_one_tmul (q : ℕ)
    (x : D.complex.homology (q : ℤ)) :
    D.baseChangeCohomologyLinearEquiv e hflat σ q
        (extendScalarsHomologyMap σ D.complex (q : ℤ) ((1 : B) ⊗ₜ[R,σ] x)) =
      moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M q
        (D.cohomologyLinearEquiv e q x) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.baseChangeCohomologyLinearEquiv_one_tmul D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ q x

/-- Under the original model comparisons the native homology mate has the
same unit pure-tensor value as the original cohomology base-change map. -/
theorem baseChangeCohomologyLinearEquiv_homologyBaseChangeMap_one_tmul (q : ℕ)
    (x : D.complex.homology (q : ℤ)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M q
    D.baseChangeCohomologyLinearEquiv e hflat σ q
        (extendScalarsHomologyMap σ D.complex (q : ℤ) ((1 : B) ⊗ₜ[R,σ] x)) =
      moduleCohomologyBaseChangeMap f σ M q
        ((1 : B) ⊗ₜ[R,σ] (D.cohomologyLinearEquiv e q x)) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.baseChangeCohomologyLinearEquiv_homologyBaseChangeMap_one_tmul D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ q x

/-- The original cohomology base-change map is exactly the native model
homology mate under the original structural-ring linear comparisons.
The tensor of the source comparison keeps the distinct native carrier
universes on both sides. -/
theorem baseChangeCohomologyLinearEquiv_homologyBaseChangeMap (q : ℕ) :
    let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
    let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
    let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    let N := (Scheme.Modules.pullback p).obj M
    letI := σ.toAlgebra
    letI := moduleCohomologyModuleOfHom X α M q
    letI := moduleCohomologyModuleOfHom Y β N q
    (moduleCohomologyBaseChangeMap f σ M q).hom.comp
        ((D.cohomologyLinearEquiv e q).baseChange R B _ _).toLinearMap =
      (D.baseChangeCohomologyLinearEquiv e hflat σ q).toLinearMap.comp
        (extendScalarsHomologyMap σ D.complex (q : ℤ)).hom := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  exact FiniteCechCohomologyModel.baseChangeCohomologyLinearEquiv_homologyBaseChangeMap D
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) e hflat σ q

end AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

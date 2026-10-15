/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Geometric

/-!
# The original cohomology base-change map on a constructed projective model

The native homology mate of the constructed finite-projective model agrees
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
  have hn := ModuleCat.homologyBaseChangeMap_naturality σ
    ((shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) (q : ℤ)).map D.comparison)
  have hx := ConcreteCategory.congr_hom hn ((1 : B) ⊗ₜ[R,σ] x)
  simp only [ConcreteCategory.comp_apply] at hx
  change extendScalarsHomologyMap σ _ (q : ℤ)
      ((1 : B) ⊗ₜ[R,σ] (homologyMap D.comparison (q : ℤ) x)) =
    homologyMap
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.comparison)
      (q : ℤ)
      (extendScalarsHomologyMap σ D.complex (q : ℤ) ((1 : B) ⊗ₜ[R,σ] x)) at hx
  change moduleFiniteCechBaseChangeCohomologyLinearEquiv f M hflat
      (fun j => i ⁻¹ᵁ coordinateOpen R ι j) n e
      (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
      (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) σ q
      (homologyMap
        (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map D.comparison)
        (q : ℤ)
        (extendScalarsHomologyMap σ D.complex (q : ℤ) ((1 : B) ⊗ₜ[R,σ] x))) =
    moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M q
      (moduleFiniteCechCohomologyLinearEquiv X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
        (fun j => i ⁻¹ᵁ coordinateOpen R ι j) M n e
        (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
        (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) q
        (homologyMap D.comparison (q : ℤ) x))
  rw [← hx]
  exact moduleFiniteCechBaseChangeCohomologyLinearEquiv_one_tmul f M hflat
    (fun j => i ⁻¹ᵁ coordinateOpen R ι j) n e
    (fun j => (isAffineOpen_coordinateOpen R ι j).preimage i)
    (i.iSup_preimage_eq_top (iSup_coordinateOpen_eq_top R ι)) σ q
    (homologyMap D.comparison (q : ℤ) x)

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
  dsimp only
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M q
  rw [D.baseChangeCohomologyLinearEquiv_one_tmul e hflat σ q x]
  exact (moduleCohomologyBaseChangeMap_one_tmul f σ M q
    (D.cohomologyLinearEquiv e q x)).symm

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
  dsimp only
  let := σ.toAlgebra
  let := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) M q
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let r := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let N := (Scheme.Modules.pullback p).obj M
  let := moduleCohomologyModuleOfHom Y
    (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) N q
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul b x =>
    change moduleCohomologyBaseChangeMap f σ M q
        (b ⊗ₜ[R,σ] (D.cohomologyLinearEquiv e q x)) =
      D.baseChangeCohomologyLinearEquiv e hflat σ q
        (extendScalarsHomologyMap σ D.complex (q : ℤ) (b ⊗ₜ[R,σ] x))
    have hb : b ⊗ₜ[R,σ] x = b • ((1 : B) ⊗ₜ[R,σ] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hb' : b ⊗ₜ[R,σ] (D.cohomologyLinearEquiv e q x) =
        b • ((1 : B) ⊗ₜ[R,σ] (D.cohomologyLinearEquiv e q x)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hb, hb']
    simp only [map_smul]
    exact congrArg (fun z => b • z)
      (D.baseChangeCohomologyLinearEquiv_homologyBaseChangeMap_one_tmul e hflat σ q x).symm
  | add s t hs ht => simp only [map_add, hs, ht]

end AlgebraicGeometry.Scheme.Cohomology.ProjectiveCohomologyModel

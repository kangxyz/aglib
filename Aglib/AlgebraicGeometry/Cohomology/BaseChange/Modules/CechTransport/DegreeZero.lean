/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.CechComparison
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero.Geometric

/-!
# Degree-zero transport of the actual Cech tensor comparison

The original degree-zero linear Cech computation transports a genuine complex
isomorphism to a tensor equivalence on unchanged `Sheaf.H`. The actual
geometric unit square proves equality with the canonical cohomology tensor
mate. No quasicoherence or affine-intersection premise enters this transport;
those premises are used separately to construct the complex isomorphism.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  {X Y : Scheme.{u}} (p : X ⟶ Y) (σ : R →+* S)
  (α : R →+* Γ(Y, ⊤)) (β : S →+* Γ(X, ⊤))
  {M : Y.Modules} {N : X.Modules} {ι : Type u} (U : ι → Y.Opens)
  (hcover : iSup U = ⊤)
  (δ : ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℕ)).obj
      (moduleCechComplex Y α M U) ⟶
    moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i))
  [(ModuleCat.extendScalars.{u, u, u} σ).PreservesHomology] [IsIso δ]

/-- The actual zero-degree Cech tensor isomorphism transported to original cohomology. -/
def moduleCechTransportedTensorEquivZero :
    letI := moduleCohomologyModuleOfHom Y α M 0
    letI := moduleCohomologyModuleOfHom X β N 0
    (ModuleCat.extendScalars σ).obj
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf Y M) 0)) ≃ₗ[S]
      Sheaf.H.{u + 1} (moduleAddSheaf X N) 0 := by
  letI := σ.toAlgebra
  letI := moduleCohomologyModuleOfHom Y α M 0
  letI := moduleCohomologyModuleOfHom X β N 0
  letI := moduleCechTensorHomologyMap_isIso p σ α β U δ 0
  exact ((moduleCechCohomologyLinearEquivZero Y α M U hcover).symm.baseChange R S _ _).trans
    ((asIso (moduleCechTensorHomologyMap p σ α β U δ 0)).toLinearEquiv.trans
      (moduleCechCohomologyLinearEquivZero X β N (fun i => p ⁻¹ᵁ U i)
        (p.iSup_preimage_eq_top hcover)))

/-- The transported zero-degree equivalence retains the original tensor formula. -/
theorem moduleCechTransportedTensorEquivZero_tmul (s : S)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) 0) :
    let := moduleCohomologyModuleOfHom Y α M 0
    let := moduleCohomologyModuleOfHom X β N 0
    moduleCechTransportedTensorEquivZero p σ α β U hcover δ (s ⊗ₜ[R,σ] x) =
      moduleCechCohomologyLinearEquivZero X β N (fun i => p ⁻¹ᵁ U i)
        (p.iSup_preimage_eq_top hcover)
          (moduleCechTensorHomologyMap p σ α β U δ 0
            (s ⊗ₜ[R,σ] (moduleCechCohomologyLinearEquivZero Y α M U hcover).symm x)) := rfl

variable (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
  (hδ : (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsForgetUnit σ) (.up ℕ)).app
          (moduleCechComplex Y α M U) ≫
        ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).map δ ≫
        (moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).hom =
      (moduleCechForgetIso Y α M U).hom ≫
        additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
          (moduleCoefficientPullback p φ))

include hδ

/-- The transported zero-degree equivalence has the original geometric unit formula. -/
theorem moduleCechTransportedTensorEquivZero_one_tmul
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) 0) :
    let := moduleCohomologyModuleOfHom Y α M 0
    let := moduleCohomologyModuleOfHom X β N 0
    moduleCechTransportedTensorEquivZero p σ α β U hcover δ ((1 : S) ⊗ₜ[R,σ] x) =
      moduleCohomologyMapAlong p φ 0 x := by
  let := moduleCohomologyModuleOfHom Y α M 0
  let := moduleCohomologyModuleOfHom X β N 0
  let e := moduleCechCohomologyLinearEquivZero Y α M U hcover
  rw [moduleCechTransportedTensorEquivZero_tmul]
  have h := moduleCechCohomologyLinearEquivZero_geometric p U φ α β hcover (e.symm x)
    (moduleCechTensorHomologyMap p σ α β U δ 0 ((1 : S) ⊗ₜ[R,σ] e.symm x))
    (moduleCechTensorHomologyMap_one_tmul p σ α β U δ φ hδ 0 (e.symm x))
  change _ = moduleCohomologyMapAlong p φ 0 (e (e.symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

variable (hσ : p.appTop.hom.comp α = β.comp σ)

/-- The original zero-degree cohomology tensor map is the actual transported isomorphism. -/
theorem moduleCohomologyTensorMap_eq_cechTransport_zero :
    let := moduleCohomologyModuleOfHom Y α M 0
    let := moduleCohomologyModuleOfHom X β N 0
    moduleCohomologyTensorMap p σ α β hσ φ 0 =
      (moduleCechTransportedTensorEquivZero p σ α β U hcover δ).toModuleIso.hom := by
  let := moduleCohomologyModuleOfHom Y α M 0
  let := moduleCohomologyModuleOfHom X β N 0
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rw [moduleCohomologyTensorMap_one_tmul]
  exact (moduleCechTransportedTensorEquivZero_one_tmul p σ α β U hcover δ φ hδ x).symm

include hcover in
/-- An actual geometric Cech isomorphism proves invertibility of the original zero-degree mate. -/
theorem moduleCohomologyTensorMap_isIso_zero_of_cech :
    let := moduleCohomologyModuleOfHom Y α M 0
    let := moduleCohomologyModuleOfHom X β N 0
    IsIso (moduleCohomologyTensorMap p σ α β hσ φ 0) := by
  let := moduleCohomologyModuleOfHom Y α M 0
  let := moduleCohomologyModuleOfHom X β N 0
  rw [moduleCohomologyTensorMap_eq_cechTransport_zero p σ α β U hcover δ φ hδ hσ]
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology

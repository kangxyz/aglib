/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.CechComparison

/-!
# Transport of actual Cech tensor comparison to module cohomology

An invertible Cech scalar-extension map gives a linear equivalence on the
unchanged positive `Sheaf.H`. Its actual geometric unit square identifies the
forward map with the original scalar-adjunction mate on cohomology. Covers,
affine intersections and quasicoherence remain visible. No finiteness of
cohomology or field hypothesis is used.
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
  {M : Y.Modules} {N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  {ι : Type u} (U : ι → Y.Opens)
  (hcover : iSup U = ⊤)
  (haff : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))
  (haff' : ∀ (q : ℕ) (a : Fin (q + 1) → ι), IsAffineOpen (∏ᶜ fun k => p ⁻¹ᵁ U (a k)))
  (I : InjectiveResolution (moduleAddSheaf Y M))
  (J : InjectiveResolution (moduleAddSheaf X N))
  (δ : ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℕ)).obj
      (moduleCechComplex Y α M U) ⟶
    moduleCechComplex X β N (fun i => p ⁻¹ᵁ U i))
  [(ModuleCat.extendScalars.{u, u, u} σ).PreservesHomology] [IsIso δ]

/-- Transport of the actual Cech tensor isomorphism to the original positive cohomology. -/
def moduleCechTransportedTensorEquivSucc (n : ℕ) :
    letI := moduleCohomologyModuleOfHom Y α M (n + 1)
    letI := moduleCohomologyModuleOfHom X β N (n + 1)
    (ModuleCat.extendScalars σ).obj
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf Y M) (n + 1))) ≃ₗ[S]
      Sheaf.H.{u + 1} (moduleAddSheaf X N) (n + 1) := by
  letI := σ.toAlgebra
  letI := moduleCohomologyModuleOfHom Y α M (n + 1)
  letI := moduleCohomologyModuleOfHom X β N (n + 1)
  letI := moduleCechTensorHomologyMap_isIso p σ α β U δ (n + 1)
  exact ((moduleCechCohomologyLinearEquiv Y α M U hcover haff I n).symm.baseChange R S _ _).trans
    ((asIso (moduleCechTensorHomologyMap p σ α β U δ (n + 1))).toLinearEquiv.trans
      (moduleCechCohomologyLinearEquiv X β N (fun i => p ⁻¹ᵁ U i)
        (p.iSup_preimage_eq_top hcover) haff' J n))

/-- The transported equivalence retains the literal tensor of the original Cech comparison. -/
theorem moduleCechTransportedTensorEquivSucc_tmul (n : ℕ) (s : S)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) (n + 1)) :
    let := moduleCohomologyModuleOfHom Y α M (n + 1)
    let := moduleCohomologyModuleOfHom X β N (n + 1)
    moduleCechTransportedTensorEquivSucc p σ α β U hcover haff haff' I J δ n
        (s ⊗ₜ[R,σ] x) =
      moduleCechCohomologyLinearEquiv X β N (fun i => p ⁻¹ᵁ U i)
        (p.iSup_preimage_eq_top hcover) haff' J n
          (moduleCechTensorHomologyMap p σ α β U δ (n + 1)
            (s ⊗ₜ[R,σ] (moduleCechCohomologyLinearEquiv Y α M U hcover haff I n).symm x)) := rfl

variable (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
  (hδ : (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsForgetUnit σ) (.up ℕ)).app
          (moduleCechComplex Y α M U) ≫
        ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).map δ ≫
        (moduleCechForgetIso X β N (fun i => p ⁻¹ᵁ U i)).hom =
      (moduleCechForgetIso Y α M U).hom ≫
        additiveCechGeometricMap p U (moduleAddSheaf Y M) (moduleAddSheaf X N)
          (moduleCoefficientPullback p φ))

include hδ

/-- The transported positive cohomology equivalence has the original geometric unit formula. -/
theorem moduleCechTransportedTensorEquivSucc_one_tmul (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) (n + 1)) :
    let := moduleCohomologyModuleOfHom Y α M (n + 1)
    let := moduleCohomologyModuleOfHom X β N (n + 1)
    moduleCechTransportedTensorEquivSucc p σ α β U hcover haff haff' I J δ n
        ((1 : S) ⊗ₜ[R,σ] x) = moduleCohomologyMapAlong p φ (n + 1) x := by
  let := moduleCohomologyModuleOfHom Y α M (n + 1)
  let := moduleCohomologyModuleOfHom X β N (n + 1)
  let e := moduleCechCohomologyLinearEquiv Y α M U hcover haff I n
  rw [moduleCechTransportedTensorEquivSucc_tmul]
  change moduleCechCohomologyAddEquiv (fun i => p ⁻¹ᵁ U i) N J
      (p.iSup_preimage_eq_top hcover) haff' n
      ((moduleCechAdditiveHomologyIso X β N (fun i => p ⁻¹ᵁ U i) (n + 1)).hom
        (moduleCechTensorHomologyMap p σ α β U δ (n + 1)
          ((1 : S) ⊗ₜ[R,σ] e.symm x))) = _
  rw [moduleCechTensorHomologyMap_one_tmul p σ α β U δ φ hδ]
  erw [moduleCechCohomologyAddEquiv_geometric p U M N I J hcover
    (p.iSup_preimage_eq_top hcover) haff haff' (moduleCoefficientPullback p φ)]
  change moduleCohomologyMapAlong p φ (n + 1) (e (e.symm x)) = _
  rw [LinearEquiv.apply_symm_apply]

variable (hσ : p.appTop.hom.comp α = β.comp σ)

/-- The original cohomology tensor mate equals the actual transported Cech isomorphism. -/
theorem moduleCohomologyTensorMap_eq_cechTransport_succ (n : ℕ) :
    let := moduleCohomologyModuleOfHom Y α M (n + 1)
    let := moduleCohomologyModuleOfHom X β N (n + 1)
    moduleCohomologyTensorMap p σ α β hσ φ (n + 1) =
      (moduleCechTransportedTensorEquivSucc
        p σ α β U hcover haff haff' I J δ n).toModuleIso.hom := by
  let := moduleCohomologyModuleOfHom Y α M (n + 1)
  let := moduleCohomologyModuleOfHom X β N (n + 1)
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  rw [moduleCohomologyTensorMap_one_tmul]
  exact (moduleCechTransportedTensorEquivSucc_one_tmul
    p σ α β U hcover haff haff' I J δ φ hδ n x).symm

include hcover haff haff' I J in
/-- An actual geometric Cech isomorphism proves invertibility of the original positive mate. -/
theorem moduleCohomologyTensorMap_isIso_succ_of_cech (n : ℕ) :
    let := moduleCohomologyModuleOfHom Y α M (n + 1)
    let := moduleCohomologyModuleOfHom X β N (n + 1)
    IsIso (moduleCohomologyTensorMap p σ α β hσ φ (n + 1)) := by
  let := moduleCohomologyModuleOfHom Y α M (n + 1)
  let := moduleCohomologyModuleOfHom X β N (n + 1)
  rw [moduleCohomologyTensorMap_eq_cechTransport_succ
    p σ α β U hcover haff haff' I J δ φ hδ hσ]
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology

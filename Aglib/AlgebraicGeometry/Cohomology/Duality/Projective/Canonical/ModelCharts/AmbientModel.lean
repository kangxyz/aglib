/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenCounit
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.OpenComposition.Homology

/-!
# The original ambient map on the native chart model

Both original cochain isomorphisms use the same ordinary closed-adjoint
open comparison and the same extension comparison on the supplied
resolution. Their induced maps on ordinary homology therefore agree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomologicalComplex

universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {A A' B B' : CommRingCat.{u}}
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map ψ) (Spec.map τ) (Spec.map σ) (Spec.map φ))
  {L : (Spec A).Modules} (J : InjectiveResolution L)

/-- The original ambient and chart comparisons are the same original cochain isomorphism. -/
theorem canonicalAmbientModelOpenIso_eq_modelOpenIso :
    canonicalAmbientModelOpenIso φ σ τ ψ h J =
      closedImmersionModelOpenIso (Spec.map σ) J (Spec.map ψ) (Spec.map φ) (Spec.map τ) h := by
  apply Iso.ext
  ext n : 1
  simp only [canonicalAmbientModelOpenIso_hom_f, closedImmersionModelOpenIso_hom_f]

/-- Their original ordinary homology arrows agree in every integer degree. -/
theorem canonicalAmbientSheafHomologyMap_eq_step (n : ℤ) :
    canonicalAmbientSheafHomologyMap φ σ τ ψ h J n =
      closedImmersionChartModelStepHomologyMap (Spec.map σ) J
        (Spec.map ψ) (Spec.map φ) (Spec.map τ) h n := by
  simp only [canonicalAmbientSheafHomologyMap, closedImmersionChartModelStepHomologyMap,
    canonicalAmbientModelOpenIso_eq_modelOpenIso]

end AlgebraicGeometry.Scheme.Modules

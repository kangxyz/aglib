/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.LinearAlgebra.DefectIdealBound
public import Aglib.LinearAlgebra.DefectRestriction

/-! # Original affine pushforward restricts exceptional defect bounds

The comparison is the native global-section pushforward isomorphism and its
naturality square, rather than an arbitrary identification of the modules.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
  {M N : (Spec S).Modules} (q : M ⟶ N)

/-- An extended ideal bound on the original affine map gives the original
ideal bound on its actual geometric pushforward. -/
theorem affinePushforward_sections_defectBounds (J : Ideal R)
    (hk : Ideal.map φ.hom J • (moduleSpecΓFunctor.map q).hom.ker = ⊥)
    (hc : Ideal.map φ.hom J • (⊤ : Submodule S (moduleSpecΓFunctor.obj N)) ≤
      (moduleSpecΓFunctor.map q).hom.range) :
    J • (moduleSpecΓFunctor.map ((pushforward (Spec.map φ)).map q)).hom.ker = ⊥ ∧
      J • (⊤ : Submodule R (moduleSpecΓFunctor.obj
        ((pushforward (Spec.map φ)).obj N))) ≤
        (moduleSpecΓFunctor.map ((pushforward (Spec.map φ)).map q)).hom.range := by
  let : Algebra R S := φ.hom.toAlgebra
  let : Module R (moduleSpecΓFunctor.obj M) := Module.compHom _ φ.hom
  let : Module R (moduleSpecΓFunctor.obj N) := Module.compHom _ φ.hom
  let : IsScalarTower R S (moduleSpecΓFunctor.obj M) :=
    IsScalarTower.of_compHom R S _
  let : IsScalarTower R S (moduleSpecΓFunctor.obj N) :=
    IsScalarTower.of_compHom R S _
  have h := LinearMap.defectBounds_restrictScalars (moduleSpecΓFunctor.map q).hom J hk hc
  let e : moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj M) ≃ₗ[R]
      moduleSpecΓFunctor.obj M := ((pushforwardGlobalSectionsIso φ).app M).toLinearEquiv
  let d : moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj N) ≃ₗ[R]
      moduleSpecΓFunctor.obj N := ((pushforwardGlobalSectionsIso φ).app N).toLinearEquiv
  let f := (moduleSpecΓFunctor.map q).hom.restrictScalars R
  let g := (moduleSpecΓFunctor.map ((pushforward (Spec.map φ)).map q)).hom
  apply LinearMap.defectBounds_of_equiv f g e.symm d.symm _ J h.1 h.2
  intro x
  apply d.injective
  rw [LinearEquiv.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom ((pushforwardGlobalSectionsIso φ).hom.naturality q)
    (e.symm x)
  change d (g (e.symm x)) = f (e (e.symm x)) at hn
  simpa only [LinearEquiv.apply_symm_apply] using hn

end AlgebraicGeometry.Scheme.Modules.Coherent

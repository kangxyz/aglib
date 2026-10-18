/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineNaturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineSheafComposition

/-! # Composition of native affine sheaf maps

The comparison retains the original scheme pullback and scalar-extension
composition isomorphisms and the actual associated-sheaf counits.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology
open scoped TensorProduct ChangeOfRings

section Composition

variable {R S T : CommRingCat.{u}} {X Y Z : Scheme.{u}}
  (p : Y ⟶ X) (q : Z ⟶ Y) (f : X ⟶ Spec R) (b : Y ⟶ Spec S) (c : Z ⟶ Spec T)
  (σ : R ⟶ S) (τ : S ⟶ T)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
  [QuasiCompact c] [QuasiSeparated c]
  (hp : p ≫ f = b ≫ Spec.map σ) (hq : q ≫ b = c ≫ Spec.map τ)
  (hqp : (q ≫ p) ≫ f = c ≫ Spec.map (σ ≫ τ))
  {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] [P.IsQuasicoherent]
  (ψ : M ⟶ (pushforward p).obj N) (χ : N ⟶ (pushforward q).obj P) (n : ℕ)

set_option maxRecDepth 2000 in
-- The original section/cohomology comparison crosses the native and Ext module universes.
/-- Successive native small tensor comparisons compose with the actual geometric
coefficient arrow and the original scalar-extension comparison. -/
theorem higherDirectImageAffineSectionsTensorMap_comp :
    (ModuleCat.extendScalarsComp σ.hom τ.hom).hom.app
        (moduleSpecΓFunctor.obj (((pushforward f).rightDerived n).obj M)) ≫
      (ModuleCat.extendScalars τ.hom).map
        (higherDirectImageAffineSectionsTensorMap p b f σ hp ψ n) ≫
      higherDirectImageAffineSectionsTensorMap q c b τ hq χ n =
        higherDirectImageAffineSectionsTensorMap (q ≫ p) c f (σ ≫ τ) hqp
          (ψ ≫ (pushforward p).map χ ≫ (pushforwardComp q p).hom.app P) n := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  apply (moduleHigherDirectImageAffineSectionsLinearEquiv c P
    (injectiveResolution P) n).injective
  change moduleHigherDirectImageAffineSectionsLinearEquiv c P (injectiveResolution P) n
      (higherDirectImageAffineSectionsTensorMap q c b τ hq χ n
        ((ModuleCat.extendScalars τ.hom).map
          (higherDirectImageAffineSectionsTensorMap p b f σ hp ψ n)
          ((ModuleCat.extendScalarsComp σ.hom τ.hom).hom.app
            (moduleSpecΓFunctor.obj (((pushforward f).rightDerived n).obj M))
            ((1 : T) ⊗ₜ[R,(τ.hom.comp σ.hom)] x)))) =
    moduleHigherDirectImageAffineSectionsLinearEquiv c P (injectiveResolution P) n
      (higherDirectImageAffineSectionsTensorMap (q ≫ p) c f (σ ≫ τ) hqp
        (ψ ≫ (pushforward p).map χ ≫ (pushforwardComp q p).hom.app P) n
        ((1 : T) ⊗ₜ[R,(τ.hom.comp σ.hom)] x))
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul, ModuleCat.ExtendScalars.map_tmul,
    higherDirectImageAffineSectionsTensorMap_one_tmul,
    higherDirectImageAffineSectionsTensorMap_one_tmul,
    higherDirectImageAffineSectionsTensorMap_one_tmul]
  exact moduleCohomologyMapAlong_comp p q ψ χ n
    (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) n x)

/-- The actual nonflat affine higher-image maps compose through the installed scheme
pullback comparison and the original composite geometric coefficient arrow. -/
theorem higherDirectImageAffineMap_comp :
    (pullbackCongr (Spec.map_comp σ τ)).hom.app
        (((pushforward f).rightDerived n).obj M) ≫
      (pullbackComp (Spec.map τ) (Spec.map σ)).inv.app
        (((pushforward f).rightDerived n).obj M) ≫
      (pullback (Spec.map τ)).map (higherDirectImageAffineMap p b f σ hp ψ n) ≫
      higherDirectImageAffineMap q c b τ hq χ n =
        higherDirectImageAffineMap (q ≫ p) c f (σ ≫ τ) hqp
          (ψ ≫ (pushforward p).map χ ≫ (pushforwardComp q p).hom.app P) n := by
  let E := ((pushforward f).rightDerived n).obj M
  let F := ((pushforward b).rightDerived n).obj N
  let G := ((pushforward c).rightDerived n).obj P
  let := moduleHigherDirectImageAffine_isQuasicoherent f M n
  let := moduleHigherDirectImageAffine_isQuasicoherent b N n
  have H := Nonflat.affineMapFromTensor_comp σ τ E F G
    (higherDirectImageAffineSectionsTensorMap p b f σ hp ψ n)
    (higherDirectImageAffineSectionsTensorMap q c b τ hq χ n)
  rw [higherDirectImageAffineSectionsTensorMap_comp p q f b c σ τ hp hq hqp ψ χ n] at H
  exact H

end Composition

end AlgebraicGeometry.Scheme.Modules

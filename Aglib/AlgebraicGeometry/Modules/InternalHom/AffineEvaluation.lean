/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineSections

/-!
# Affine sections of the actual internal Hom

Evaluation identifies internal-Hom sections on an affine open with linear maps
of the original section modules. Only quasicoherence of the source is used.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.InternalHom

/-- Actual affine-chart morphisms associated with an original Hom section. -/
def affineSectionHomEquiv {X : Scheme.{u}} (U : X.affineOpens) (M N : X.Modules) :
    Γ(sheaf X M N, U) ≃
      (M.restrict U.property.fromSpec ⟶ N.restrict U.property.fromSpec) :=
  ((sheaf X M N).val.presheaf.mapIso
    (eqToIso U.property.opensRange_fromSpec).op).addCommGroupIsoToAddEquiv.toEquiv |>.trans
    (restrictionHomEquiv U.property.fromSpec M N).symm

/-- The affine-chart comparison evaluates by the original section component. -/
theorem affineSectionHomEquiv_evaluation {X : Scheme.{u}} (U : X.affineOpens)
    (M N : X.Modules) (s : Γ(sheaf X M N, U))
    (m : moduleSpecΓFunctor.obj (M.restrict U.property.fromSpec)) :
    sectionEvaluation X M N U s ((affineChartΓIso U M).hom m) =
      (affineChartΓIso U N).hom
        ((affineSectionHomEquiv U M N s).val.app (op ⊤) m) := by
  let V := U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)
  let h : U.val = V := by
    simp [V, Scheme.Hom.image_top_eq_opensRange, U.property.opensRange_fromSpec]
  let i : V ⟶ U.val := homOfLE ((U.property.fromSpec.image_le_opensRange ⊤).trans_eq
    U.property.opensRange_fromSpec)
  change s.val.app (op (Over.mk (𝟙 U.val))) (M.val.map (eqToHom h).op m) =
    N.val.map (eqToHom h).op (s.val.app (op (Over.mk i)) m)
  exact NatTrans.naturality_apply s.val
    (Over.homMk (eqToHom h) : Over.mk (𝟙 U.val) ⟶ Over.mk i).op m

/-- On affine opens, evaluation is bijective for a quasicoherent source. -/
theorem sectionEvaluation_bijective {X : Scheme.{u}} (U : X.affineOpens)
    (M N : X.Modules) [(M.restrict U.property.fromSpec).IsQuasicoherent] :
    Function.Bijective (sectionEvaluation X M N U) := by
  let e := (affineSectionHomEquiv U M N).trans
    ((affineGlobalHomEquiv Γ(X, U) (M.restrict U.property.fromSpec)
      (N.restrict U.property.fromSpec)).trans
        ((affineChartΓIso U M).toLinearEquiv.arrowCongr
          (affineChartΓIso U N).toLinearEquiv).toEquiv)
  have he : (sectionEvaluation X M N U : Γ(sheaf X M N, U) → _) = e := by
    funext s
    apply LinearMap.ext
    intro m
    obtain ⟨m, rfl⟩ := (affineChartΓIso U M).toLinearEquiv.surjective m
    change _ = (affineChartΓIso U N).hom
      (affineGlobalHomEquiv Γ(X, U) _ _ (affineSectionHomEquiv U M N s)
        ((affineChartΓIso U M).inv ((affineChartΓIso U M).hom m)))
    rw [Iso.hom_inv_id_apply, affineGlobalHomEquiv_apply]
    exact affineSectionHomEquiv_evaluation U M N s m
  rw [he]
  exact e.bijective

/-- Original sections of the actual Hom sheaf on an affine open are precisely
linear maps between the original section modules, with their actual scalar action. -/
def affineSectionsEquiv {X : Scheme.{u}} (U : X.affineOpens) (M N : X.Modules)
    [(M.restrict U.property.fromSpec).IsQuasicoherent] :
    Γ(sheaf X M N, U) ≃ₗ[Γ(X, U)] (Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U)) :=
  LinearEquiv.ofBijective (sectionEvaluation X M N U) (sectionEvaluation_bijective U M N)

/-- The affine linear equivalence retains the literal evaluation map. -/
theorem affineSectionsEquiv_apply {X : Scheme.{u}} (U : X.affineOpens) (M N : X.Modules)
    [(M.restrict U.property.fromSpec).IsQuasicoherent]
    (s : Γ(sheaf X M N, U)) (m : Γ(M, U)) :
    affineSectionsEquiv U M N s m = s.val.app (op (Over.mk (𝟙 U.val))) m := rfl

/-- The affine linear comparison preserves actual restriction, without requiring
that the smaller affine open be principal. -/
theorem affineSectionsEquiv_restrict {X : Scheme.{u}} (U V : X.affineOpens)
    (M N : X.Modules) [(M.restrict U.property.fromSpec).IsQuasicoherent]
    [(M.restrict V.property.fromSpec).IsQuasicoherent]
    (i : V.val ⟶ U.val) (s : Γ(sheaf X M N, U)) (m : Γ(M, U)) :
    affineSectionsEquiv V M N ((sheaf X M N).val.map i.op s) (M.val.map i.op m) =
      N.val.map i.op (affineSectionsEquiv U M N s m) :=
  sectionEvaluation_restrict X M N i s m

end AlgebraicGeometry.Scheme.Modules.InternalHom

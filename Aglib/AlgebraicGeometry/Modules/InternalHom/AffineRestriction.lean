/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineSections

/-!
# Global Hom sections on an actual affine restriction

The original internal-Hom sheaf is first restricted along the specified open
immersion. Its actual global sections identify linearly with maps of the
actual source and target section modules.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules.InternalHom

/-- Original sections on an affine chart are actual morphisms on that chart. -/
def affineRestrictionHomEquiv {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M N : X.Modules) :
    moduleSpecΓFunctor.obj ((show X.Modules from sheaf X M N).restrict j) ≃
      (M.restrict j ⟶ N.restrict j) :=
  ((sheaf X M N).val.presheaf.mapIso
    (eqToIso (j.image_top_eq_opensRange).symm).op).addCommGroupIsoToAddEquiv.toEquiv |>.trans
      (restrictionHomEquiv j M N).symm

/-- The affine-restriction Hom comparison is literal evaluation on its image open. -/
theorem affineRestrictionHomEquiv_apply {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
    (s : moduleSpecΓFunctor.obj ((show X.Modules from sheaf X M N).restrict j))
    (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    (affineRestrictionHomEquiv j M N s).val.app (op ⊤) m =
      s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) m := rfl

/-- Actual global sections of the restricted internal Hom identify linearly
with maps between the actual restricted global-section modules. -/
def affineRestrictionSectionsEquiv {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
    [(M.restrict j).IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((show X.Modules from sheaf X M N).restrict j) ≃ₗ[R]
      (moduleSpecΓFunctor.obj (M.restrict j) →ₗ[R] moduleSpecΓFunctor.obj (N.restrict j)) where
  toEquiv := (affineRestrictionHomEquiv j M N).trans
    (affineGlobalHomEquiv R (M.restrict j) (N.restrict j))
  map_add' s t := by
    apply LinearMap.ext
    intro m
    change affineGlobalHomEquiv R _ _ (affineRestrictionHomEquiv j M N (s + t)) m =
      affineGlobalHomEquiv R _ _ (affineRestrictionHomEquiv j M N s) m +
        affineGlobalHomEquiv R _ _ (affineRestrictionHomEquiv j M N t) m
    simp only [affineGlobalHomEquiv_apply]
    rfl
  map_smul' r s := by
    apply LinearMap.ext
    intro m
    change affineGlobalHomEquiv R _ _ (affineRestrictionHomEquiv j M N (r • s)) m =
      r • affineGlobalHomEquiv R _ _ (affineRestrictionHomEquiv j M N s) m
    simp only [affineGlobalHomEquiv_apply]
    change ((r • s).val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) m) =
      r • (show Γ(N.restrict j, ⊤) from s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) m)
    rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_Spec_def]
    change X.presheaf.map (𝟙 (j ''ᵁ ⊤)).op
      ((j.appIso ⊤).inv ((Spec R).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso R).inv r))) •
          (show Γ(N, j ''ᵁ ⊤) from s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) m) =
      ((j.appIso ⊤).inv ((Spec R).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso R).inv r))) •
          (show Γ(N, j ''ᵁ ⊤) from s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) m)
    simp

/-- The linear affine-restriction equivalence retains original section evaluation. -/
theorem affineRestrictionSectionsEquiv_apply {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
    [(M.restrict j).IsQuasicoherent]
    (s : moduleSpecΓFunctor.obj ((show X.Modules from sheaf X M N).restrict j))
    (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    affineRestrictionSectionsEquiv j M N s m =
      s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) m := by
  change affineGlobalHomEquiv R _ _ (affineRestrictionHomEquiv j M N s) m = _
  rw [affineGlobalHomEquiv_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules.InternalHom

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PrincipalSections

/-!
# Hom sections under iterated actual affine restriction

The native restriction-composition isomorphisms are retained, including their
original section maps. Their transports cancel by naturality of a Hom section.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite AlgebraicGeometry
open scoped ModuleCat.Algebra
universe u
namespace AlgebraicGeometry.Scheme.Modules.InternalHom

/-- Original Hom sections on an iterated affine restriction, with the native
composition comparisons on the source, target and internal Hom. -/
def iteratedAffineRestrictionSectionsEquiv {X : Scheme.{u}} {R S : CommRingCat.{u}}
    (j : Spec R ⟶ X) (k : Spec S ⟶ Spec R) [IsOpenImmersion j] [IsOpenImmersion k]
    (M N : X.Modules) [M.IsQuasicoherent] :
    moduleSpecΓFunctor.obj (((show X.Modules from sheaf X M N).restrict j).restrict k) ≃ₗ[S]
      (moduleSpecΓFunctor.obj ((M.restrict j).restrict k) →ₗ[S]
        moduleSpecΓFunctor.obj ((N.restrict j).restrict k)) :=
  (moduleSpecΓFunctor.mapIso ((Scheme.Modules.restrictFunctorComp k j).symm.app
    (sheaf X M N))).toLinearEquiv |>.trans
      ((affineRestrictionSectionsEquiv (k ≫ j) M N).trans
        ((moduleSpecΓFunctor.mapIso
          ((Scheme.Modules.restrictFunctorComp k j).app M)).toLinearEquiv.arrowCongr
            (moduleSpecΓFunctor.mapIso
              ((Scheme.Modules.restrictFunctorComp k j).app N)).toLinearEquiv))

/-- After the native composition transports, evaluation remains the original
component on the original image open. -/
theorem iteratedAffineRestrictionSectionsEquiv_apply {X : Scheme.{u}}
    {R S : CommRingCat.{u}} (j : Spec R ⟶ X) (k : Spec S ⟶ Spec R)
    [IsOpenImmersion j] [IsOpenImmersion k] (M N : X.Modules) [M.IsQuasicoherent]
    (s : moduleSpecΓFunctor.obj (((show X.Modules from sheaf X M N).restrict j).restrict k))
    (m : moduleSpecΓFunctor.obj ((M.restrict j).restrict k)) :
    iteratedAffineRestrictionSectionsEquiv j k M N s m =
      s.val.app (op (Over.mk (𝟙 (j ''ᵁ (k ''ᵁ ⊤))))) m := by
  let V := j ''ᵁ (k ''ᵁ ⊤)
  let W := (k ≫ j) ''ᵁ ⊤
  let h : W = V := Scheme.Hom.comp_image k j ⊤
  change (moduleSpecΓFunctor.mapIso ((Scheme.Modules.restrictFunctorComp k j).app N)).hom
    (affineRestrictionSectionsEquiv (k ≫ j) M N
      ((moduleSpecΓFunctor.mapIso ((Scheme.Modules.restrictFunctorComp k j).symm.app
        (sheaf X M N))).hom s)
      ((moduleSpecΓFunctor.mapIso ((Scheme.Modules.restrictFunctorComp k j).app M)).inv m)) = _
  rw [affineRestrictionSectionsEquiv_apply]
  change N.val.map (eqToHom h.symm).op
    (s.val.app (op (Over.mk (eqToHom h))) (M.val.map (eqToHom h).op m)) =
      s.val.app (op (Over.mk (𝟙 V))) m
  have hn := NatTrans.naturality_apply s.val
    (Over.homMk (eqToHom h) : Over.mk (eqToHom h) ⟶ Over.mk (𝟙 V)).op m
  change s.val.app (op (Over.mk (eqToHom h))) (M.val.map (eqToHom h).op m) =
    N.val.map (eqToHom h).op (s.val.app (op (Over.mk (𝟙 V))) m) at hn
  rw [hn]
  exact Iso.hom_inv_id_apply (N.presheaf.mapIso (eqToIso h).op) _

/-- Principal restriction of the original Hom section commutes with evaluation
on the original principal-restriction map of source sections. -/
theorem affineRestrictionSectionsEquiv_principal {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (r : R)
    (M N : X.Modules) [M.IsQuasicoherent]
    (s : moduleSpecΓFunctor.obj ((show X.Modules from sheaf X M N).restrict j))
    (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    iteratedAffineRestrictionSectionsEquiv j (QuasiCoherent.principalOpen R r) M N
      (QuasiCoherent.toPrincipalGlobalSections R r ((show X.Modules from sheaf X M N).restrict j) s)
      (QuasiCoherent.toPrincipalGlobalSections R r (M.restrict j) m) =
    QuasiCoherent.toPrincipalGlobalSections R r (N.restrict j)
      (affineRestrictionSectionsEquiv j M N s m) := by
  rw [iteratedAffineRestrictionSectionsEquiv_apply, affineRestrictionSectionsEquiv_apply]
  let V := j ''ᵁ (QuasiCoherent.principalOpen R r ''ᵁ ⊤)
  let U := j ''ᵁ (⊤ : (Spec R).Opens)
  let i : V ⟶ U := homOfLE (j.image_mono le_top)
  change s.val.app (op (Over.mk i)) (M.val.map i.op m) =
    N.val.map i.op (s.val.app (op (Over.mk (𝟙 U))) m)
  exact NatTrans.naturality_apply s.val
    (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op m

end AlgebraicGeometry.Scheme.Modules.InternalHom

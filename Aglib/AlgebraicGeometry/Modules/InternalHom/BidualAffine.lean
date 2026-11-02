/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.AffineRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Bidual
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.AffineSections

/-! # Original affine sections of the canonical bidual

The original section comparisons identify sheaf evaluation with module evaluation.
Only quasicoherence of the two original affine restrictions is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open _root_.Module

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} {R : CommRingCat.{u}}
  (j : Spec R ⟶ X) [IsOpenImmersion j]

/-- Original scalar sections on an affine restriction, through the original
restriction-unit isomorphism and the original affine structure sections. -/
def affineRestrictionUnitSectionsEquiv :
    moduleSpecΓFunctor.obj
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).restrict j) ≃ₗ[R] R :=
  ((moduleSpecΓFunctor.mapIso (Scheme.Modules.restrictUnitIso j)) ≪≫
    (globalSectionsUnitIso (R := R))).toLinearEquiv

variable (M : X.Modules) [(M.restrict j).IsQuasicoherent]

/-- Sections of the original dual sheaf are the actual linear dual of sections. -/
def affineDualSectionsEquiv :
    moduleSpecΓFunctor.obj ((show X.Modules from dualSheaf X M).restrict j) ≃ₗ[R]
      Module.Dual R (moduleSpecΓFunctor.obj (M.restrict j)) :=
  (InternalHom.affineRestrictionSectionsEquiv j M
    (SheafOfModules.unit X.ringCatSheaf)).trans
      ((LinearEquiv.refl R (moduleSpecΓFunctor.obj (M.restrict j))).arrowCongr
        (affineRestrictionUnitSectionsEquiv j))

/-- The affine dual comparison evaluates on the original image open. -/
theorem affineDualSectionsEquiv_apply
    (s : moduleSpecΓFunctor.obj ((show X.Modules from dualSheaf X M).restrict j))
    (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    affineDualSectionsEquiv j M s m = affineRestrictionUnitSectionsEquiv j
      (s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) m) := by
  change affineRestrictionUnitSectionsEquiv j
    (InternalHom.affineRestrictionSectionsEquiv j M
      (SheafOfModules.unit X.ringCatSheaf) s m) = _
  exact congrArg (affineRestrictionUnitSectionsEquiv j)
    (InternalHom.affineRestrictionSectionsEquiv_apply j M
      (SheafOfModules.unit X.ringCatSheaf) s m)

variable [((show X.Modules from dualSheaf X M).restrict j).IsQuasicoherent]

/-- Apply the actual affine Hom comparison twice, retaining the same scalar map. -/
def affineBidualSectionsEquiv :
    moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j) ≃ₗ[R]
      Module.Dual R (Module.Dual R (moduleSpecΓFunctor.obj (M.restrict j))) :=
  (affineDualSectionsEquiv j (dualSheaf X M)).trans
    ((affineDualSectionsEquiv j M).arrowCongr (LinearEquiv.refl R R))

/-- The second comparison is evaluation on the actual inverse dual section. -/
theorem affineBidualSectionsEquiv_apply
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j))
    (l : Module.Dual R (moduleSpecΓFunctor.obj (M.restrict j))) :
    affineBidualSectionsEquiv j M s l = affineRestrictionUnitSectionsEquiv j
      (s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) ((affineDualSectionsEquiv j M).symm l)) := by
  change affineDualSectionsEquiv j (dualSheaf X M) s
    ((affineDualSectionsEquiv j M).symm l) = _
  exact affineDualSectionsEquiv_apply j (dualSheaf X M) s _

/-- The original sheaf bidual evaluation becomes the original module evaluation. -/
theorem affineBidualSectionsEquiv_evaluation
    (m : moduleSpecΓFunctor.obj (M.restrict j)) :
    affineBidualSectionsEquiv j M
        ((moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor j).map
          (bidualMap X M))).hom m) =
      Module.Dual.eval R (moduleSpecΓFunctor.obj (M.restrict j)) m := by
  apply LinearMap.ext
  intro l
  let ell := (affineDualSectionsEquiv j M).symm l
  have hfirst := affineBidualSectionsEquiv_apply j M
    ((moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor j).map
      (bidualMap X M))).hom m) l
  have heval := congrArg (affineRestrictionUnitSectionsEquiv j)
    (bidualMap_evaluate X M (j ''ᵁ ⊤) m ell)
  have hdual := (affineDualSectionsEquiv_apply j M ell m).symm
  have hinverse := congrArg
    (fun a : Module.Dual R (moduleSpecΓFunctor.obj (M.restrict j)) => a m)
    ((affineDualSectionsEquiv j M).apply_symm_apply l)
  exact hfirst.trans (heval.trans (hdual.trans hinverse))

end AlgebraicGeometry.Scheme.Modules.Invertible

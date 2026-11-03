/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.AffineGlobalSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.SectionsMap


/-!
# Original affine open restriction of the actual bidual

The existing affine Hom comparisons supply the map from the restriction of
the original bidual to the bidual of the restricted sheaf. The original
bidual evaluation square is retained. No arbitrary-pullback comparison or
new affine equivalence is used.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u


open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} {R : CommRingCat.{u}}
  (j : Spec R ⟶ X) [IsOpenImmersion j] (M : X.Modules)
  [(M.restrict j).IsQuasicoherent]
  [((show X.Modules from dualSheaf X M).restrict j).IsQuasicoherent]
  [((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j).IsQuasicoherent]
  [(dualSheaf (Spec R) (M.restrict j)).IsQuasicoherent]
  [(dualSheaf (Spec R) (dualSheaf (Spec R) (M.restrict j))).IsQuasicoherent]

/-- The original affine comparisons define the open restriction arrow. -/
def affineBidualOpenRestriction :
    (show X.Modules from dualSheaf X (dualSheaf X M)).restrict j ⟶
      dualSheaf (Spec R) (dualSheaf (Spec R) (M.restrict j)) :=
  affineSectionsMap (ModuleCat.ofHom
    (X := moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j))
    (Y := moduleSpecΓFunctor.obj
      (dualSheaf (Spec R) (dualSheaf (Spec R) (M.restrict j))))
    (((affineBidualSectionsEquiv j M).trans
      (affineBidualGlobalSectionsEquiv (M.restrict j)).symm).toLinearMap))

/-- Its actual sections are the two original bidual comparisons. -/
theorem affineBidualOpenRestriction_sections :
    moduleSpecΓFunctor.map (affineBidualOpenRestriction j M) =
      ModuleCat.ofHom
        (X := moduleSpecΓFunctor.obj
          ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j))
        (Y := moduleSpecΓFunctor.obj
          (dualSheaf (Spec R) (dualSheaf (Spec R) (M.restrict j))))
        (((affineBidualSectionsEquiv j M).trans
        (affineBidualGlobalSectionsEquiv (M.restrict j)).symm).toLinearMap) :=
  affineSectionsMap_sections _

/-- Restriction of the original evaluation is the original local evaluation. -/
theorem affineBidualOpenRestriction_evaluation :
    (restrictFunctor j).map (bidualMap X M) ≫ affineBidualOpenRestriction j M =
      bidualMap (Spec R) (M.restrict j) := by
  apply hom_eq_of_globalSections_eq
  refine (moduleSpecΓFunctor.map_comp _ _).trans ?_
  refine (congrArg (fun t =>
    moduleSpecΓFunctor.map ((restrictFunctor j).map (bidualMap X M)) ≫ t)
      (affineBidualOpenRestriction_sections j M)).trans ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply (affineBidualGlobalSectionsEquiv (M.restrict j)).injective
  change affineBidualGlobalSectionsEquiv (M.restrict j)
    ((affineBidualGlobalSectionsEquiv (M.restrict j)).symm
      (affineBidualSectionsEquiv j M
        ((moduleSpecΓFunctor.map ((restrictFunctor j).map (bidualMap X M))).hom m))) = _
  exact ((affineBidualGlobalSectionsEquiv (M.restrict j)).apply_symm_apply _).trans
    ((affineBidualSectionsEquiv_evaluation j M m).trans
      (affineBidualGlobalSectionsEquiv_evaluation (M.restrict j) m).symm)

end AlgebraicGeometry.Scheme.Modules.Invertible

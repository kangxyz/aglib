/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.AffineGlobalNaturality
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.AffineGlobalSections
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.AffineNaturality
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.OpenRestriction


/-!
# Naturality of the original affine bidual restriction arrow

The same affine restriction map commutes with original double-dual maps.
The proof uses the original global sections and their faithful affine
comparison, without canceling the raw bidual evaluation arrow.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} {R : CommRingCat.{u}}
  (j : Spec R ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
  [(M.restrict j).IsQuasicoherent]
  [((show X.Modules from dualSheaf X M).restrict j).IsQuasicoherent]
  [((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j).IsQuasicoherent]
  [(dualSheaf (Spec R) (M.restrict j)).IsQuasicoherent]
  [(dualSheaf (Spec R) (dualSheaf (Spec R) (M.restrict j))).IsQuasicoherent]
  [(N.restrict j).IsQuasicoherent]
  [((show X.Modules from dualSheaf X N).restrict j).IsQuasicoherent]
  [((show X.Modules from dualSheaf X (dualSheaf X N)).restrict j).IsQuasicoherent]
  [(dualSheaf (Spec R) (N.restrict j)).IsQuasicoherent]
  [(dualSheaf (Spec R) (dualSheaf (Spec R) (N.restrict j))).IsQuasicoherent]

/-- Original affine coordinates of the actual open-restriction map. -/
theorem affineBidualOpenRestriction_value
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j)) :
    affineBidualGlobalSectionsEquiv (M.restrict j)
      ((moduleSpecΓFunctor.map (affineBidualOpenRestriction j M)).hom s) =
        affineBidualSectionsEquiv j M s := by
  have h := congrArg (fun t => t.hom s) (affineBidualOpenRestriction_sections j M)
  exact (congrArg (affineBidualGlobalSectionsEquiv (M.restrict j)) h).trans
    ((affineBidualGlobalSectionsEquiv (M.restrict j)).apply_symm_apply _)

/-- The actual bidual restriction arrow is natural for the original sheaf map. -/
theorem affineBidualOpenRestriction_naturality (h : M ⟶ N) :
    affineBidualOpenRestriction j M ≫
      doubleDualMap (Spec R) ((restrictFunctor j).map h) =
    (restrictFunctor j).map (doubleDualMap X h) ≫ affineBidualOpenRestriction j N := by
  apply hom_eq_of_globalSections_eq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply (affineBidualGlobalSectionsEquiv (N.restrict j)).injective
  have hl := affineBidualGlobalSectionsEquiv_naturality (M.restrict j) (N.restrict j)
    ((restrictFunctor j).map h)
    ((moduleSpecΓFunctor.map (affineBidualOpenRestriction j M)).hom s)
  have hm := affineBidualOpenRestriction_value j M s
  have hn := affineBidualSectionsEquiv_naturality j M N h s
  have hr := affineBidualOpenRestriction_value j N
    ((moduleSpecΓFunctor.map ((restrictFunctor j).map (doubleDualMap X h))).hom s)
  exact hl.trans ((congrArg
    (moduleSpecΓFunctor.map ((restrictFunctor j).map h)).hom.dualMap.dualMap hm).trans
      (hn.symm.trans hr.symm))

end AlgebraicGeometry.Scheme.Modules.Invertible

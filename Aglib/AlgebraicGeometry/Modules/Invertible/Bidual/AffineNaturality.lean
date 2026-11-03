/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Map


/-!
# Original affine dual comparisons retain the actual Hom arrows

The existing affine dual and bidual section equivalences commute with the
original internal-Hom precomposition maps. This is proved by their actual
section evaluations, not by cancellation of raw bidual evaluation as an epi.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} {R : CommRingCat.{u}}
  (j : Spec R ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
  [(M.restrict j).IsQuasicoherent] [(N.restrict j).IsQuasicoherent]
  (h : M ⟶ N)

/-- The actual affine dual comparison commutes with original precomposition. -/
theorem affineDualSectionsEquiv_naturality
    (s : moduleSpecΓFunctor.obj ((show X.Modules from dualSheaf X N).restrict j)) :
    affineDualSectionsEquiv j M
      ((moduleSpecΓFunctor.map ((restrictFunctor j).map
        (InternalHom.map X h (𝟙 (SheafOfModules.unit X.ringCatSheaf))))).hom s) =
    (moduleSpecΓFunctor.map ((restrictFunctor j).map h)).hom.dualMap
      (affineDualSectionsEquiv j N s) := by
  apply LinearMap.ext
  intro m
  have hl := affineDualSectionsEquiv_apply j M
    ((moduleSpecΓFunctor.map ((restrictFunctor j).map
      (InternalHom.map X h (𝟙 (SheafOfModules.unit X.ringCatSheaf))))).hom s) m
  have hr := affineDualSectionsEquiv_apply j N s
    ((moduleSpecΓFunctor.map ((restrictFunctor j).map h)).hom m)
  exact hl.trans hr.symm

variable [((show X.Modules from dualSheaf X M).restrict j).IsQuasicoherent]
  [((show X.Modules from dualSheaf X N).restrict j).IsQuasicoherent]

/-- The actual affine bidual comparison commutes with the original double-dual map. -/
theorem affineBidualSectionsEquiv_naturality
    (s : moduleSpecΓFunctor.obj
      ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j)) :
    affineBidualSectionsEquiv j N
      ((moduleSpecΓFunctor.map ((restrictFunctor j).map (doubleDualMap X h))).hom s) =
    (moduleSpecΓFunctor.map ((restrictFunctor j).map h)).hom.dualMap.dualMap
      (affineBidualSectionsEquiv j M s) := by
  apply LinearMap.ext
  intro ell
  let d := (moduleSpecΓFunctor.map ((restrictFunctor j).map h)).hom
  let t := (affineDualSectionsEquiv j N).symm ell
  have ht := affineDualSectionsEquiv_naturality j M N h t
  have he : (affineDualSectionsEquiv j N) t = ell :=
    (affineDualSectionsEquiv j N).apply_symm_apply ell
  have hd : (moduleSpecΓFunctor.map ((restrictFunctor j).map
      (InternalHom.map X h (𝟙 (SheafOfModules.unit X.ringCatSheaf))))).hom t =
      (affineDualSectionsEquiv j M).symm (d.dualMap ell) := by
    apply (affineDualSectionsEquiv j M).injective
    exact ht.trans ((congrArg d.dualMap he).trans
      ((affineDualSectionsEquiv j M).apply_symm_apply _).symm)
  have hl := affineBidualSectionsEquiv_apply j N
    ((moduleSpecΓFunctor.map ((restrictFunctor j).map (doubleDualMap X h))).hom s) ell
  have hr := affineBidualSectionsEquiv_apply j M s (d.dualMap ell)
  exact hl.trans ((congrArg (fun q => affineRestrictionUnitSectionsEquiv j
    (s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤)))) q)) hd).trans hr.symm)

end AlgebraicGeometry.Scheme.Modules.Invertible

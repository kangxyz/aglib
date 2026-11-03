/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Affine


/-!
# Original affine bidual sections without an identity restriction

The comparison is the existing affine bidual comparison, transported only
through the original identity-restriction isomorphism. Its evaluation is
still the original module bidual evaluation. This is preparatory to open
restriction of the same raw bidual, not arbitrary pullback of a determinant.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)
  [M.IsQuasicoherent] [(dualSheaf (Spec R) M).IsQuasicoherent]

/-- Remove the original identity restriction from the native bidual comparison. -/
def affineBidualGlobalSectionsEquiv :
    moduleSpecΓFunctor.obj (dualSheaf (Spec R) (dualSheaf (Spec R) M)) ≃ₗ[R]
      Module.Dual R (Module.Dual R (moduleSpecΓFunctor.obj M)) :=
  ((moduleSpecΓFunctor.mapIso (restrictFunctorId.app
      (dualSheaf (Spec R) (dualSheaf (Spec R) M)))).symm.toLinearEquiv).trans
    ((affineBidualSectionsEquiv (𝟙 (Spec R)) M).trans
      (moduleSpecΓFunctor.mapIso (restrictFunctorId.app M)).toLinearEquiv.dualMap.dualMap)

/-- The comparison retains the actual evaluation map, not just the objects. -/
theorem affineBidualGlobalSectionsEquiv_evaluation
    (m : moduleSpecΓFunctor.obj M) :
    affineBidualGlobalSectionsEquiv M
      ((moduleSpecΓFunctor.map (bidualMap (Spec R) M)).hom m) =
        Module.Dual.eval R (moduleSpecΓFunctor.obj M) m := by
  let e := (moduleSpecΓFunctor.mapIso (restrictFunctorId.app M)).toLinearEquiv
  have hnat := congrArg (fun t => (moduleSpecΓFunctor.map t).hom m)
    (restrictFunctorId.inv.naturality (bidualMap (Spec R) M))
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply] at hnat
  have heval := affineBidualSectionsEquiv_evaluation (𝟙 (Spec R)) M (e.symm m)
  apply LinearMap.ext
  intro ell
  change affineBidualSectionsEquiv (𝟙 (Spec R)) M
    ((moduleSpecΓFunctor.map (restrictFunctorId.inv.app
      (dualSheaf (Spec R) (dualSheaf (Spec R) M)))).hom
      ((moduleSpecΓFunctor.map (bidualMap (Spec R) M)).hom m))
        (e.dualMap ell) = ell m
  exact (congrArg (fun q =>
    affineBidualSectionsEquiv (𝟙 (Spec R)) M q (e.dualMap ell)) hnat).trans
      ((congrArg (fun q => q (e.dualMap ell)) heval).trans
        (congrArg ell (e.apply_symm_apply m)))

end AlgebraicGeometry.Scheme.Modules.Invertible

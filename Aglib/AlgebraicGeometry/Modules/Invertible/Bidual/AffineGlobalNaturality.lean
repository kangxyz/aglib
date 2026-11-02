/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.AffineGlobalSections
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.AffineNaturality


/-!
# Naturality after removing the original identity restriction

The original identity-restriction naturality squares transport the actual
bidual Hom-arrow comparison. The original global-section arrow and both
original identity-restriction isomorphisms are retained.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {R : CommRingCat.{u}} (M N : (Spec R).Modules)
  [M.IsQuasicoherent] [N.IsQuasicoherent]
  [(dualSheaf (Spec R) M).IsQuasicoherent] [(dualSheaf (Spec R) N).IsQuasicoherent]
  (h : M ⟶ N)

/-- The original global affine bidual comparison retains the original double-dual arrow. -/
theorem affineBidualGlobalSectionsEquiv_naturality
    (s : moduleSpecΓFunctor.obj (dualSheaf (Spec R) (dualSheaf (Spec R) M))) :
    affineBidualGlobalSectionsEquiv N
      ((moduleSpecΓFunctor.map (doubleDualMap (Spec R) h)).hom s) =
    (moduleSpecΓFunctor.map h).hom.dualMap.dualMap
      (affineBidualGlobalSectionsEquiv M s) := by
  let eM := (moduleSpecΓFunctor.mapIso (restrictFunctorId.app M)).toLinearEquiv
  let eN := (moduleSpecΓFunctor.mapIso (restrictFunctorId.app N)).toLinearEquiv
  let v := (moduleSpecΓFunctor.map (restrictFunctorId.inv.app
    (dualSheaf (Spec R) (dualSheaf (Spec R) M)))).hom s
  let d := (moduleSpecΓFunctor.map h).hom
  let dr := (moduleSpecΓFunctor.map ((restrictFunctor (𝟙 (Spec R))).map h)).hom
  have hd := congrArg (fun q => (moduleSpecΓFunctor.map q).hom s)
    (restrictFunctorId.inv.naturality (doubleDualMap (Spec R) h))
  have hb := congrArg (fun q => (moduleSpecΓFunctor.map q).hom)
    (restrictFunctorId.hom.naturality h)
  apply LinearMap.ext
  intro ell
  have he : dr.dualMap (eN.dualMap ell) = eM.dualMap (d.dualMap ell) := by
    apply LinearMap.ext
    intro m
    exact congrArg ell (congrArg (fun q => q m) hb)
  have hn := affineBidualSectionsEquiv_naturality (𝟙 (Spec R)) M N h v
  change affineBidualSectionsEquiv (𝟙 (Spec R)) N
    ((moduleSpecΓFunctor.map (restrictFunctorId.inv.app
      (dualSheaf (Spec R) (dualSheaf (Spec R) N)))).hom
      ((moduleSpecΓFunctor.map (doubleDualMap (Spec R) h)).hom s))
        (eN.dualMap ell) =
    affineBidualSectionsEquiv (𝟙 (Spec R)) M v (eM.dualMap (d.dualMap ell))
  exact (congrArg (fun q => affineBidualSectionsEquiv (𝟙 (Spec R)) N q
    (eN.dualMap ell)) hd).trans
      ((congrArg (fun q => q (eN.dualMap ell)) hn).trans
        (congrArg (affineBidualSectionsEquiv (𝟙 (Spec R)) M v) he))

end AlgebraicGeometry.Scheme.Modules.Invertible

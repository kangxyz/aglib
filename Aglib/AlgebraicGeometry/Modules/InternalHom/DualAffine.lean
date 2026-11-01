/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.DualFunctor
public import Aglib.AlgebraicGeometry.Modules.InternalHom.BidualAffine

/-! # Original affine comparison for dual maps

The unchanged affine dual-section equivalence intertwines the original
internal-Hom map with precomposition on the original section modules.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u

/-- The entire original affine dual map is precomposition by the original section map. -/
theorem affineDualSectionsEquiv_map {X : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] {M N : X.Modules}
    [(M.restrict j).IsQuasicoherent] [(N.restrict j).IsQuasicoherent]
    (a : M ⟶ N)
    (s : moduleSpecΓFunctor.obj ((show X.Modules from dualSheaf X N).restrict j)) :
    affineDualSectionsEquiv j M
        ((moduleSpecΓFunctor.map ((restrictFunctor j).map ((dualFunctor X).map a.op))) s) =
      (affineDualSectionsEquiv j N s).comp
        (moduleSpecΓFunctor.map ((restrictFunctor j).map a)).hom := by
  apply LinearMap.ext
  intro m
  rw [affineDualSectionsEquiv_apply]
  change affineRestrictionUnitSectionsEquiv j
      (s.val.app (op (Over.mk (𝟙 (j ''ᵁ ⊤))))
        ((moduleSpecΓFunctor.map ((restrictFunctor j).map a)).hom m)) = _
  exact (affineDualSectionsEquiv_apply j N s _).symm

end AlgebraicGeometry.Scheme.Modules.InternalHom

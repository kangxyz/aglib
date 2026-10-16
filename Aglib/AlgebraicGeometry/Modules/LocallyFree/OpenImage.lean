/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover

/-!
# Free presentations on the image of an open immersion

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/Degree/FiniteFlatLocallyFree.lean`, SHA-256
  `d3dc4d7ca161eb1493165b50730ef4e573da5882fd475b4d4d520c066d42a7fb`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}} {I : Type u}

/-- The given actual free presentation transported to the image of an open immersion. -/
def freeIsoOnImage (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (V : X.Opens)
    (e : SheafOfModules.free (R := V.toScheme.ringCatSheaf) I ≅
      (M.restrict f).restrict V.ι) :
    SheafOfModules.free (R := (f ''ᵁ V).toScheme.ringCatSheaf) I ≅
      M.restrict (f ''ᵁ V).ι := by
  apply freeIsoOfRestrictIso (f.isoImage V) (M.restrict (f ''ᵁ V).ι)
  exact e ≪≫ ((Scheme.Modules.restrictFunctorComp V.ι f).symm.app M) ≪≫
    ((Scheme.Modules.restrictFunctorCongr (f.isoImage_hom_ι V).symm).app M) ≪≫
    ((Scheme.Modules.restrictFunctorComp (f.isoImage V).hom (f ''ᵁ V).ι).app M)

end AlgebraicGeometry.Scheme.Modules
end

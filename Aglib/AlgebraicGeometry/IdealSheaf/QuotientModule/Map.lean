/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Monomorphism
public import Aglib.AlgebraicGeometry.IdealSheaf.QuotientModule

/-!
# The structure module of the image of a closed subscheme

Let `j : X ⟶ Y` be a morphism of schemes and `V ⊆ X` a closed subscheme (`V : X.IdealSheafData`)
that is closed in `Y`: `V ⟶ X ⟶ Y` is a closed immersion. Its image `V.map j ⊆ Y` (Mathlib's
`IdealSheafData.map`, the kernel of `V ⟶ Y`) is isomorphic to `V` over `Y`
(`Scheme.IdealSheafData.mapSubschemeIso`, `IdealSheaf/Monomorphism`), so its structure module is
the pushforward of the structure module of `V`:

* `Scheme.IdealSheafData.quotientModulePushforwardIso`: `j_* 𝒪_V ≅ 𝒪_{V.map j}`, through the
  pushforward presentations `𝒪_V ≅ (V ⟶ X)_* 𝒪_V` and `𝒪_{V.map j} ≅ (V.map j ⟶ Y)_* 𝒪`
  (`quotientModuleIsoPushforward`) and the isomorphism `V ≅ V.map j` over `Y`.

The only hypothesis is the closedness of `V` in `Y`; for a closed immersion `j` it holds for every
`V`. This is the pushforward counterpart of the pullback comparison `quotientModulePullbackIso`
(`IdealSheaf/BaseChange/QuotientModule`). It identifies the structure module of the image of a
closed subscheme of a projective fibre with a pushforward, as in the Hilbert polynomial of a
divisor of a projective family (`HilbertScheme/Immersed/Fiber`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- **The structure module of the image of a closed subscheme**: for `j : X ⟶ Y` and a closed
subscheme `V ⊆ X` that is closed in `Y`, `j_* 𝒪_V ≅ 𝒪_{V.map j}`. -/
def quotientModulePushforwardIso (V : X.IdealSheafData) (j : X ⟶ Y)
    [IsClosedImmersion (V.subschemeι ≫ j)] :
    (Scheme.Modules.pushforward j).obj V.quotientModule ≅ (V.map j).quotientModule :=
  (Scheme.Modules.pushforward j).mapIso V.quotientModuleIsoPushforward ≪≫
    (Scheme.Modules.pushforwardComp V.subschemeι j).app _ ≪≫
    (Scheme.Modules.pushforwardCongr (V.mapSubschemeIso_hom_subschemeι j)).symm.app _ ≪≫
    ((Scheme.Modules.pushforwardComp (V.mapSubschemeIso j).hom (V.map j).subschemeι).app
      _).symm ≪≫
    (Scheme.Modules.pushforward (V.map j).subschemeι).mapIso
      (asIso (Scheme.Hom.structureModuleMap (V.mapSubschemeIso j).hom)).symm ≪≫
    (V.map j).quotientModuleIsoPushforward.symm

end AlgebraicGeometry.Scheme.IdealSheafData

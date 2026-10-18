/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction

/-!
# Relative flatness of tensor products with locally trivial sheaves

Let `f : X ⟶ Y` and let `L` be an `𝒪_X`-module that is locally isomorphic to `𝒪_X`, for instance a
twisting sheaf `𝒪(d)` on projective space. If `M` is relatively flat over `Y`
(`Scheme.Modules.relativeFlat f M`), so is `L ⊗ M`: on an open `U` where `L|_U ≅ 𝒪_U`, the
restriction `(L ⊗ M)|_U` is isomorphic to `M|_U`, and relative flatness is pointwise and transported
along open restriction and isomorphisms.

This supplies the relative flatness of the twists `F(m) = 𝒪(m) ⊗ F` of a flat family, used with
cohomology and base change in Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, proof of Theorem 4.3, p. 21.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- **Tensoring with a locally trivial sheaf preserves relative flatness.** If every point of `X`
has an open neighbourhood `U` with `L|_U ≅ 𝒪_U`, and `M` is relatively flat over `Y`, then so is
`L ⊗ M`. -/
theorem relativeFlat_tensor_of_locallyTrivial {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : X.Modules)
    (hL : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hM : relativeFlat f M) : relativeFlat f ((moduleTensorLeftFunctor X L).obj M) := by
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hL x
  have hMU : relativeFlat (U.ι ≫ f) (M.restrict U.ι) := relativeFlat_restrict U.ι f hM
  let e' : ((moduleTensorLeftFunctor X L).obj M).restrict U.ι ≅ M.restrict U.ι :=
    (tensorRestrictionIso U.ι L M).symm ≪≫
      ((SheafOfModulesOfCommRing.tensorFunctor U.toScheme.sheaf).mapIso e).app
        (M.restrict U.ι) ≪≫
      (SheafOfModulesOfCommRing.tensorLeftUnitIso U.toScheme.sheaf).app (M.restrict U.ι)
  exact flat_stalk_of_flat_stalk_restrict U.ι f _ ⟨x, hxU⟩
    (relativeFlat_of_iso (U.ι ≫ f) e' hMU ⟨x, hxU⟩)

end AlgebraicGeometry.Scheme.Modules

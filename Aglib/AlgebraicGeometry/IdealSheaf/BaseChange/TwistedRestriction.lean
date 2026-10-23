/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.QuotientModule
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.RightUnit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism

/-!
# Restriction of a twisted module to a closed subscheme, under pullback

For a module `L` on a scheme `X` and a closed subscheme `W ⊆ X`, the restriction
`W.twistedRestriction L : L ⟶ L ⊗ 𝒪_W` is the inverse right unitor followed by
`L ◁ (𝒪_X ⟶ 𝒪_W)`. For `p : Y ⟶ X` and an isomorphism `c : p^* L ≅ L'`,
`W.pullbackTensorQuotientIso p c : p^*(L ⊗ 𝒪_W) ≅ L' ⊗ 𝒪_{W.comap p}` is the canonical tensor
comparison (invertible for every `p`, `Pullback.Tensor.pullbackTensorMap_isIso`) followed by
`c` and `quotientModulePullbackIso` (no flatness). The restriction is natural:
`p^*(W.twistedRestriction L)` followed by this isomorphism is `c` followed by
`(W.comap p).twistedRestriction L'` (`pullback_map_twistedRestriction`).

The twisted module, the restriction and the ideal inclusion agree with the objects and maps of
the twisted sequence `W.shortComplex.map (moduleTensorLeftFunctor X L)`, definitionally
(`tensor_quotientModule_eq_shortComplex_map_X₃`, `twistedRestriction_eq_shortComplex_map_g`,
`whiskerLeft_idealInclusion_eq_shortComplex_map_f`); these are stated once, at variable data.

This is the restriction `E(r) ⟶ F(r)` of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §5, p. 25, diagram (**), for `E = 𝒪` and `F = 𝒪_W`, and its compatibility
with base change.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The restriction `L ⟶ L ⊗ 𝒪_W` of a module `L` to a closed subscheme `W`. -/
def twistedRestriction (W : X.IdealSheafData) (L : X.Modules) : L ⟶ L ⊗ W.quotientModule :=
  (ρ_ L).inv ≫ (L ◁ W.toQuotientModule)

theorem twistedRestriction_def (W : X.IdealSheafData) (L : X.Modules) :
    W.twistedRestriction L = (ρ_ L).inv ≫ (L ◁ W.toQuotientModule) :=
  rfl

/-- **The pullback of a twisted structure module**: for `p : Y ⟶ X` and `c : p^* L ≅ L'`,
`p^*(L ⊗ 𝒪_W) ≅ L' ⊗ 𝒪_{W.comap p}`. No flatness is needed. -/
def pullbackTensorQuotientIso (W : X.IdealSheafData) (p : Y ⟶ X) {L : X.Modules}
    {L' : Y.Modules} (c : (Scheme.Modules.pullback p).obj L ≅ L') :
    (Scheme.Modules.pullback p).obj (L ⊗ W.quotientModule) ≅ L' ⊗ (W.comap p).quotientModule :=
  haveI := Pullback.Tensor.pullbackTensorMap_isIso p L W.quotientModule
  asIso (pullbackTensorMap p L W.quotientModule) ≪≫ (c ⊗ᵢ W.quotientModulePullbackIso p)

theorem pullbackTensorQuotientIso_hom (W : X.IdealSheafData) (p : Y ⟶ X) {L : X.Modules}
    {L' : Y.Modules} (c : (Scheme.Modules.pullback p).obj L ≅ L') :
    (W.pullbackTensorQuotientIso p c).hom =
      pullbackTensorMap p L W.quotientModule ≫ (c.hom ⊗ₘ (W.quotientModulePullbackIso p).hom) :=
  rfl

/-- The naturality of `pullbackTensorMap` in the second factor, for the projection to `𝒪_W`. -/
theorem pullback_map_whiskerLeft_toQuotientModule (W : X.IdealSheafData) (p : Y ⟶ X)
    (L : X.Modules) :
    (Scheme.Modules.pullback p).map (L ◁ W.toQuotientModule) ≫
        pullbackTensorMap p L W.quotientModule =
      pullbackTensorMap p L (𝟙_ X.Modules) ≫
        ((Scheme.Modules.pullback p).obj L ◁
          (Scheme.Modules.pullback p).map W.toQuotientModule) := by
  have h := pullbackTensorMap_naturality p (𝟙 L) W.toQuotientModule
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-- **The restriction to a closed subscheme commutes with pullback**: for `p : Y ⟶ X` and
`c : p^* L ≅ L'`, `p^*(L ⟶ L ⊗ 𝒪_W)` followed by `pullbackTensorQuotientIso` is `c` followed by
the restriction `L' ⟶ L' ⊗ 𝒪_{W.comap p}`. -/
theorem pullback_map_twistedRestriction (W : X.IdealSheafData) (p : Y ⟶ X) {L : X.Modules}
    {L' : Y.Modules} (c : (Scheme.Modules.pullback p).obj L ≅ L') :
    (Scheme.Modules.pullback p).map (W.twistedRestriction L) ≫
        (W.pullbackTensorQuotientIso p c).hom =
      c.hom ≫ (W.comap p).twistedRestriction L' := by
  have h1 := W.pullback_map_whiskerLeft_toQuotientModule p L
  have h2 := pullbackTensorMap_rightUnit p L
  have h3 := W.pullback_map_toQuotientModule_quotientModulePullbackIso_hom p
  rw [twistedRestriction_def, twistedRestriction_def, pullbackTensorQuotientIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% h1, tensorHom_def,
    whisker_exchange_assoc, ← whiskerLeft_comp, h3, whiskerLeft_comp,
    ← whisker_exchange_assoc, reassoc_of% h2]
  exact (rightUnitor_inv_naturality_assoc c.hom _).symm

/-- **The twisted structure module in the two presentations**: `L ⊗ 𝒪_W` is the third object of
the twisted sequence `L ⊗ (I_W ⟶ 𝒪 ⟶ 𝒪_W)`. Checked once, at variable data. -/
theorem tensor_quotientModule_eq_shortComplex_map_X₃ (W : X.IdealSheafData) (L : X.Modules) :
    L ⊗ W.quotientModule = (W.shortComplex.map (moduleTensorLeftFunctor X L)).X₃ :=
  rfl

/-- **The restriction to `W` in the two presentations**: `W.twistedRestriction L` is the inverse
right unitor followed by the second map of the twisted sequence. Checked once, at variable
data. -/
theorem twistedRestriction_eq_shortComplex_map_g (W : X.IdealSheafData) (L : X.Modules) :
    W.twistedRestriction L =
      (ρ_ L).inv ≫ (W.shortComplex.map (moduleTensorLeftFunctor X L)).g :=
  rfl

/-- **The inclusion of `L ⊗ I_W` in the two presentations**: the inclusion `L ⊗ I_W ⟶ L`, through
the right unitor, is the first map of the twisted sequence followed by the right unitor. -/
theorem whiskerLeft_idealInclusion_eq_shortComplex_map_f (W : X.IdealSheafData) (L : X.Modules) :
    (L ◁ Scheme.Hom.idealInclusion W.subschemeι) ≫ (ρ_ L).hom =
      (W.shortComplex.map (moduleTensorLeftFunctor X L)).f ≫ (ρ_ L).hom :=
  rfl

end AlgebraicGeometry.Scheme.IdealSheafData

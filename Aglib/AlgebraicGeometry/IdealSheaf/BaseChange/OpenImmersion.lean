/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Isomorphism

/-!
# Canonical ideal maps along open immersions

For a cartesian square of a closed subscheme along an open immersion `b : Y ⟶ X`, the canonical
ideal comparison `Scheme.Hom.idealPullbackMap` is an isomorphism
(`idealPullbackMap_isIso_of_isOpenImmersion`). No flatness or closed-immersion hypothesis is
used: the square restricts to the open image of `b`, where both horizontal maps are
isomorphisms, and `idealPullbackMap_isIso_of_local` glues.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

variable {D X : Scheme.{u}}

/-- Along every cartesian square whose base-change morphism is an open immersion, the canonical
ideal comparison is an isomorphism. -/
theorem idealPullbackMap_isIso_of_isOpenImmersion {D' Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D) (h : a ≫ i = i' ≫ b)
    (H' : IsPullback a i' i b) [IsOpenImmersion b] :
    IsIso (idealPullbackMap i i' b a h) := by
  apply idealPullbackMap_isIso_of_local i i' b a h
  intro y
  have hWV : (⊤ : Y.Opens) ≤ b ⁻¹ᵁ b.opensRange := by
    rw [Scheme.Hom.preimage_opensRange]
  refine ⟨b.opensRange, ⊤, hWV, trivial, ?_⟩
  have hres : b.resLE b.opensRange ⊤ hWV = (⊤ : Y.Opens).ι ≫ b.isoOpensRange.hom := by
    apply (cancel_mono b.opensRange.ι).mp
    rw [Scheme.Hom.resLE_comp_ι, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have : IsIso ((⊤ : Y.Opens).ι) := inferInstanceAs (IsIso Y.topIso.hom)
  have : IsIso (b.resLE b.opensRange ⊤ hWV) := by
    rw [hres]
    infer_instance
  have : IsIso (restrictedSquareSourceMap i i' b a h b.opensRange ⊤ hWV) :=
    (restrictedSquareSourceMap_isPullback i i' b a h H' b.opensRange ⊤ hWV).isIso_fst_of_isIso
  exact idealPullbackMap_isIso_of_iso_square _ _ _ _ _

end AlgebraicGeometry.Scheme.Hom

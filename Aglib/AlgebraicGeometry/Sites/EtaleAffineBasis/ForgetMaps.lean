/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! # Original affine-test objects and arrows in the over-category -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

variable {S : Scheme.{u}}

/-- Forgetting the original affine test gives its literal structural arrow. -/
theorem forget_spec_obj (U : S.AffineEtale) :
    (Scheme.Etale.forget S).obj ((Scheme.AffineEtale.Spec S).obj U) =
      Over.mk ((Scheme.AffineEtale.Spec S).obj U).hom := rfl

/-- Forgetting the original affine-test transition gives the original spectrum
map and its native structural equation, before any coefficient is applied. -/
theorem forget_spec_map {U V : S.AffineEtale} (g : V ⟶ U) :
    (Scheme.Etale.forget S).map ((Scheme.AffineEtale.Spec S).map g) =
      Over.homMk (U := Over.mk ((Scheme.AffineEtale.Spec S).obj V).hom)
        (V := Over.mk ((Scheme.AffineEtale.Spec S).obj U).hom) (Spec.map g.left.unop)
        (MorphismProperty.Over.w ((Scheme.AffineEtale.Spec S).map g)) := rfl

end AlgebraicGeometry.Scheme.EtaleAffineBasis

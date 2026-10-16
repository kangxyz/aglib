/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Fixed-endpoint short exact extensions

An extension of `X` by `Y` records an actual short exact sequence with these
endpoints. Its class is Mathlib's derived `Ext X Y 1`, and its isomorphisms fix
both endpoints.
-/
@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.Abelian.Ext1
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A short exact extension of `X` by `Y`, with both endpoints fixed. -/
structure Extension (X Y : C) where
  /-- The middle object of the extension. -/
  middle : C
  /-- The inclusion of the fixed left endpoint. -/
  i : Y ⟶ middle
  /-- The projection to the fixed right endpoint. -/
  p : middle ⟶ X
  /-- The two consecutive maps compose to zero. -/
  zero : i ≫ p = 0
  /-- The recorded short complex is short exact. -/
  shortExact : (ShortComplex.mk i p zero).ShortExact

/-- The actual short complex of a fixed-endpoint extension. -/
def Extension.toShortComplex {X Y : C} (E : Extension X Y) : ShortComplex C :=
  ShortComplex.mk E.i E.p E.zero

/-- The canonical degree-one derived Ext class of the extension. -/
def Extension.extClass [HasExt.{w} C] {X Y : C} (E : Extension X Y) :
    Ext.{w} X Y 1 := E.shortExact.extClass

/-- An isomorphism of extensions inducing the identity on both endpoints. -/
structure Extension.Iso {X Y : C} (E E' : Extension X Y) where
  /-- The isomorphism between the middle objects. -/
  middleIso : E.middle ≅ E'.middle
  /-- The middle isomorphism preserves the inclusion of the left endpoint. -/
  comm_i : E.i ≫ middleIso.hom = E'.i
  /-- The middle isomorphism preserves the projection to the right endpoint. -/
  comm_p : middleIso.hom ≫ E'.p = E.p

end CategoryTheory.Abelian.Ext1

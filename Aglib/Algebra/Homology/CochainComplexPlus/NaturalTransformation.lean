/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.CochainComplexPlus.Functoriality
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans

/-! # Original coefficient transformations on bounded-below complexes

Arbitrary coefficient transformations, not just isomorphisms, act termwise on
the original complexes. This includes noninvertible noncentral scalar actions
on an underlying additive coefficient functor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
namespace CategoryTheory
universe u v u' v'
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type u'} [Category.{v'} B] [Preadditive B]
  {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]

/-- Isomorphism mapping uses the same actual forward transformation. -/
theorem NatTrans.mapCochainComplexPlus_iso_hom (e : F ≅ G) :
    NatTrans.mapCochainComplexPlus e.hom = (NatIso.mapCochainComplexPlus e).hom := rfl

end CategoryTheory

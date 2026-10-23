/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition

/-! # Functoriality of the original bounded-below derived isomorphism comparison -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w u' v' w'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive]

/-- The installed derived isomorphism comparison respects composition of original
functor isomorphisms. -/
theorem rightDerivedFunctorPlusIso_trans {G H : A ⥤ B} [G.Additive] [H.Additive]
    (e : F ≅ G) (e' : G ≅ H) :
    F.rightDerivedFunctorPlusIso (e ≪≫ e') =
      F.rightDerivedFunctorPlusIso e ≪≫ G.rightDerivedFunctorPlusIso e' := by
  apply Iso.ext
  apply F.rightDerivedFunctorPlus.rightDerived_ext F.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom]
  rw [rightDerivedFunctorPlusIso_hom_app, ← Category.assoc,
    rightDerivedFunctorPlusIso_hom_app, Category.assoc,
    rightDerivedFunctorPlusIso_hom_app, ← Category.assoc, ← map_comp]
  rfl

/-- The comparison for an identity is the identity of the installed derived functor. -/
@[simp]
theorem rightDerivedFunctorPlusIso_refl :
    F.rightDerivedFunctorPlusIso (Iso.refl F) = Iso.refl F.rightDerivedFunctorPlus := by
  apply Iso.ext
  apply F.rightDerivedFunctorPlus.rightDerived_ext F.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, Iso.refl_hom, NatTrans.id_app]
  rw [rightDerivedFunctorPlusIso_hom_app]
  change (DerivedCategory.Plus.Q (C := B)).map (𝟙 _) ≫ _ = _
  rw [map_id, Category.id_comp]
  exact (Category.comp_id (F.rightDerivedFunctorPlusUnit.app K)).symm

end CategoryTheory.Functor

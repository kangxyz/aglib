/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Whole identity normalizations for right-unit source faces -/

@[expose] public section
namespace CategoryTheory
variable {U A : Type*} [Category* U] [Category* A]
  {J T : U ⥤ A} {I : A ⥤ A}

/-- An original identity compositor gives the inverse identity component after transport. -/
theorem rightIdentityExpansion_app (e : T ≅ J) (c : T ≅ J ⋙ I) (l : I ≅ 𝟭 A)
    (h : c ≪≫ Functor.isoWhiskerLeft J l ≪≫ Functor.rightUnitor J = e) (K : U) :
    (e.symm ≪≫ c).hom.app K = l.inv.app (J.obj K) := by
  have hh := congrArg (fun z => z.hom.app K) h
  change c.hom.app K ≫ l.hom.app (J.obj K) ≫ 𝟙 _ = e.hom.app K at hh
  rw [Category.comp_id] at hh
  apply (cancel_mono (l.hom.app (J.obj K))).mp
  change (e.inv.app K ≫ c.hom.app K) ≫ l.hom.app (J.obj K) = _
  rw [Category.assoc, hh, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
  rfl

/-- A whole original refinement identity determines its original component. -/
theorem identityRefinement_inv_app (δ : J ⟶ J ⋙ I) (d : I ≅ 𝟭 A)
    (h : δ ≫ Functor.whiskerLeft J d.hom ≫ (Functor.rightUnitor J).hom = 𝟙 J) (K : U) :
    δ.app K = d.inv.app (J.obj K) := by
  have hh := congrArg (fun z => z.app K) h
  change δ.app K ≫ d.hom.app (J.obj K) ≫ 𝟙 _ = 𝟙 _ at hh
  rw [Category.comp_id] at hh
  apply (cancel_mono (d.hom.app (J.obj K))).mp
  rw [hh, Iso.inv_hom_id_app]
  rfl

end CategoryTheory

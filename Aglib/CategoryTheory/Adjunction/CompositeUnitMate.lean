/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-!
# The identity-base mate of a composite adjunction

The original mate of a specified composition comparison is the original unit
of the second adjunction followed by the conjugate right comparison. This is
the identity-base contraction needed for actual refinement comparisons.
-/

@[expose] public section

namespace CategoryTheory

variable {S A B : Type*} [Category* S] [Category* A] [Category* B]
  {L : S ⥤ A} {R : A ⥤ S} {H : A ⥤ B} {Q : B ⥤ A}
  {T : S ⥤ B} {U : B ⥤ S}

/-- The original mate of the identity square for a composite left adjoint is
exactly the original second-adjunction unit pushed through the first right adjoint. -/
theorem mateEquiv_composite_leftUnitor
    (a : L ⊣ R) (h : H ⊣ Q) (K : A) :
    (mateEquiv a (a.comp h)
      (TwoSquare.mk (𝟭 S) L (L ⋙ H) H (Functor.leftUnitor (L ⋙ H)).hom)).app K =
      R.map (h.unit.app K) := by
  rw [mateEquiv_app_eq]
  simp only [TwoSquare.mk, Functor.leftUnitor_hom_app, Functor.id_obj,
    Functor.map_id, Adjunction.comp_unit_app, Functor.comp_map]
  simp only [Category.assoc]
  change a.unit.app (R.obj K) ≫ R.map (h.unit.app (L.obj (R.obj K))) ≫
    (𝟙 (R.obj (Q.obj (H.obj (L.obj (R.obj K)))))) ≫
      R.map (Q.map (H.map (a.counit.app K))) = R.map (h.unit.app K)
  calc
    _ = a.unit.app (R.obj K) ≫ R.map (h.unit.app (L.obj (R.obj K))) ≫
        R.map (Q.map (H.map (a.counit.app K))) :=
      congrArg (fun z => a.unit.app (R.obj K) ≫
        R.map (h.unit.app (L.obj (R.obj K))) ≫ z)
        (Category.id_comp (R.map (Q.map (H.map (a.counit.app K)))))
    _ = a.unit.app (R.obj K) ≫ R.map
        (h.unit.app (L.obj (R.obj K)) ≫ Q.map (H.map (a.counit.app K))) :=
      congrArg (fun z => a.unit.app (R.obj K) ≫ z) (R.map_comp _ _).symm
    _ = a.unit.app (R.obj K) ≫ R.map (a.counit.app K ≫ h.unit.app K) :=
      congrArg (fun z => a.unit.app (R.obj K) ≫ R.map z)
        (h.unit.naturality (a.counit.app K)).symm
    _ = (a.unit.app (R.obj K) ≫ R.map (a.counit.app K)) ≫
        R.map (h.unit.app K) := by rw [R.map_comp, Category.assoc]
    _ = R.map (h.unit.app K) :=
      (congrArg (fun z => z ≫ R.map (h.unit.app K)) (a.right_triangle_components K)).trans
        (Category.id_comp (R.map (h.unit.app K)))

/-- Conjugate composition comparisons retain the original unit in the
identity-base mate. -/
theorem mateEquiv_composition_unit
    (a : L ⊣ R) (h : H ⊣ Q) (t : T ⊣ U)
    (c : T ≅ L ⋙ H) (d : U ≅ Q ⋙ R)
    (hc : conjugateEquiv (a.comp h) t c.hom = d.inv) (K : A) :
    (mateEquiv a t
      (TwoSquare.mk (𝟭 S) L T H ((Functor.leftUnitor T).hom ≫ c.hom))).app K ≫
        d.hom.app (H.obj K) = R.map (h.unit.app K) := by
  let α := TwoSquare.mk (𝟭 S) L (L ⋙ H) H (Functor.leftUnitor (L ⋙ H)).hom
  let β := TwoSquare.mk (𝟭 S) L T H ((Functor.leftUnitor T).hom ≫ c.hom)
  have hs : α.whiskerRight c.hom = β.whiskerLeft (Iso.refl L).hom := by
    ext X
    simp [α, β]
  have hm := mateEquiv_conjugate_comparisons a a (a.comp h) t
    (Iso.refl L) c (Iso.refl R) d (by simp) hc α β hs K
  change (𝟙 (R.obj K)) ≫ (mateEquiv a (a.comp h) α).app K =
    (mateEquiv a t β).app K ≫ d.hom.app (H.obj K) at hm
  rw [Category.id_comp] at hm
  exact hm.symm.trans (mateEquiv_composite_leftUnitor a h K)

end CategoryTheory

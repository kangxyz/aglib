/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.CompositeUnitMate
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Normalization

/-! # The original identity-base exchange as an actual unit comparison -/

@[expose] public section
namespace CategoryTheory

variable {S A B : Type*} [Category* S] [Category* A] [Category* B]
  {L : S ⥤ A} {R : A ⥤ S} {H : A ⥤ B} {Q : B ⥤ A}
  {T : S ⥤ B} {U : B ⥤ S} {I : S ⥤ S}

/-- Whole normalization equation retaining the actual exchange and right compositor. -/
def CompositeIdentityBaseMateEquation (h : H ⊣ Q) (d : U ≅ Q ⋙ R)
    (i : I ≅ 𝟭 S) (β : R ⋙ I ⟶ H ⋙ U) : Prop :=
  ∀ K, β.app K ≫ d.hom.app (H.obj K) =
    i.hom.app (R.obj K) ≫ R.map (h.unit.app K)

/-- An original normalized composition square gives the original unit contraction.
The square and the exchange must be identified with the actual comparisons. -/
theorem compositeIdentityBaseMateEquation
    (a : L ⊣ R) (h : H ⊣ Q) (t : T ⊣ U)
    (c : T ≅ L ⋙ H) (d : U ≅ Q ⋙ R) (i : I ≅ 𝟭 S)
    (hc : conjugateEquiv (a.comp h) t c.hom = d.inv)
    (e : I ⋙ T ≅ L ⋙ H)
    (he : e = Functor.isoWhiskerRight i T ≪≫ Functor.leftUnitor T ≪≫ c)
    (β : R ⋙ I ⟶ H ⋙ U)
    (hβ : β = (mateEquiv a t (TwoSquare.mk I L T H e.hom)).natTrans) :
    CompositeIdentityBaseMateEquation h d i β := by
  subst β
  subst e
  intro K
  let α := TwoSquare.mk I L T H
    (Functor.isoWhiskerRight i T ≪≫ Functor.leftUnitor T ≪≫ c).hom
  let α₀ := TwoSquare.mk (𝟭 S) L T H ((Functor.leftUnitor T).hom ≫ c.hom)
  have hs : ∀ X, T.map (i.hom.app X) ≫ α₀.app X =
      α.app X ≫ (𝟙 H : H ⟶ H).app (L.obj X) := by
    intro X
    simp [α, α₀]
  have hm := mateEquiv_top_bottom_naturality a t α α₀ i.hom (𝟙 H) hs K
  simp only [NatTrans.id_app, Functor.map_id] at hm
  have hm' : i.hom.app (R.obj K) ≫ (mateEquiv a t α₀).app K =
      (mateEquiv a t α).app K :=
    hm.trans (Category.comp_id ((mateEquiv a t α).app K))
  change (mateEquiv a t α).app K ≫ d.hom.app (H.obj K) = _
  exact (congrArg (fun z => z ≫ d.hom.app (H.obj K)) hm'.symm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun z => i.hom.app (R.obj K) ≫ z)
        (mateEquiv_composition_unit a h t c d hc K)))

end CategoryTheory

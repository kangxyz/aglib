/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MateHomEquiv

/-!
# Coherence of unit maps for specified adjunction comparisons

The identity and composition equations retain the original adjunction units and
the prescribed comparison isomorphisms. The left and right comparison maps are
required to be actual conjugates. The component statements apply without
adjunctions on the source functors, including the refinement maps for derived
exceptional direct images.
-/

@[expose] public noncomputable section

namespace CategoryTheory

section ConjugateTransport

variable {C D : Type*} [Category* C] [Category* D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- Transporting the original unit map along specified conjugate isomorphisms
agrees with the original unit map for the other adjunction. -/
theorem Adjunction.unit_map_conjugateIso
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₂ ≅ L₁) (d : R₂ ≅ R₁)
    (hc : conjugateEquiv a b c.hom = d.inv)
    {X : C} {Y : D} (f : L₁.obj X ⟶ Y) :
    (b.unit.app X ≫ R₂.map (c.hom.app X ≫ f)) ≫ d.hom.app Y =
      a.unit.app X ≫ R₁.map f := by
  have h := homEquiv_conjugate a b c.hom f
  rw [hc] at h
  simp only [Adjunction.homEquiv_apply] at h
  rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end ConjugateTransport

section CompositeUnit

variable {B C D : Type*} [Category* B] [Category* C] [Category* D]
  {Lf : B ⥤ C} {Rf : C ⥤ B} {Lk : C ⥤ D} {Rk : D ⥤ C}

/-- The composite adjunction unit transposes a composite of two original arrows
as the composite of their unit transposes. -/
theorem Adjunction.unit_map_composite
    (af : Lf ⊣ Rf) (ak : Lk ⊣ Rk)
    {X : B} {Y : C} {Z : D} (f : Lf.obj X ⟶ Y) (g : Lk.obj Y ⟶ Z) :
    (af.comp ak).unit.app X ≫ (Rk ⋙ Rf).map (Lk.map f ≫ g) =
      (af.unit.app X ≫ Rf.map f) ≫ Rf.map (ak.unit.app Y ≫ Rk.map g) := by
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rw [← Rf.map_comp_assoc, ak.unit_naturality, Rf.map_comp]
  simp only [Category.assoc]

end CompositeUnit

section Composition

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {Ll : A ⥤ B} {Lj : A ⥤ C} {Li : A ⥤ D}
  {Lf : B ⥤ C} {Rf : C ⥤ B} {Lk : C ⥤ D} {Rk : D ⥤ C}
  {Lt : B ⥤ D} {Rt : D ⥤ B}

/-- The original unit maps respect a specified composite comparison when the
total-adjunction comparison and its right comparison are actual conjugates. -/
theorem adjunctionUnitComparison_comp
    (af : Lf ⊣ Rf) (ak : Lk ⊣ Rk) (atotal : Lt ⊣ Rt)
    (σf : Ll ⋙ Lf ≅ Lj) (σk : Lj ⋙ Lk ≅ Li) (σt : Ll ⋙ Lt ≅ Li)
    (c : Lt ≅ Lf ⋙ Lk) (d : Rt ≅ Rk ⋙ Rf)
    (hc : conjugateEquiv (af.comp ak) atotal c.hom = d.inv)
    (hσ : σt = Functor.isoWhiskerLeft Ll c ≪≫
      (Functor.associator Ll Lf Lk).symm ≪≫
      Functor.isoWhiskerRight σf Lk ≪≫ σk) (K : A) :
    (atotal.unit.app (Ll.obj K) ≫ Rt.map (σt.hom.app K)) ≫
        d.hom.app (Li.obj K) =
      (af.unit.app (Ll.obj K) ≫ Rf.map (σf.hom.app K)) ≫
        Rf.map (ak.unit.app (Lj.obj K) ≫ Rk.map (σk.hom.app K)) := by
  have hσK : σt.hom.app K = c.hom.app (Ll.obj K) ≫
      Lk.map (σf.hom.app K) ≫ σk.hom.app K := by
    rw [hσ]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp]
  rw [hσK, Adjunction.unit_map_conjugateIso (af.comp ak) atotal c d hc]
  exact Adjunction.unit_map_composite af ak (σf.hom.app K) (σk.hom.app K)

end Composition

section Identity

variable {A B : Type*} [Category* A] [Category* B]
  {L : A ⥤ B} {I J : B ⥤ B}

/-- Removing a specified identity adjunction from the original unit comparison
gives the identity arrow, using the actual conjugate identity comparisons. -/
theorem adjunctionUnitComparison_id
    (a : I ⊣ J) (σ : L ⋙ I ≅ L) (dI : I ≅ 𝟭 B) (dJ : J ≅ 𝟭 B)
    (hd : conjugateEquiv Adjunction.id a dI.hom = dJ.inv)
    (hσ : σ = Functor.isoWhiskerLeft L dI ≪≫ Functor.rightUnitor L) (K : A) :
    (a.unit.app (L.obj K) ≫ J.map (σ.hom.app K)) ≫ dJ.hom.app (L.obj K) =
      𝟙 (L.obj K) := by
  have hσK : σ.hom.app K = dI.hom.app (L.obj K) := by
    rw [hσ]
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    exact Category.comp_id (dI.hom.app (L.obj K))
  have hu := homEquiv_to_identity a dI.hom (L.obj K)
  rw [hd, Adjunction.homEquiv_apply] at hu
  rw [hσK, hu]
  exact Iso.inv_hom_id_app dJ (L.obj K)

end Identity

end CategoryTheory

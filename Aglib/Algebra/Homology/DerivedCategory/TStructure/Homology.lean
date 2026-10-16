/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# The original homology of a concentrated derived object

For objects whose homology is concentrated in one degree, the native
homology functor detects equality of morphisms. Such an object has a
normalized isomorphism to the native single of its original homology.
The defining normalization makes the homology map the identity after the
original single/homology comparison. This is shared by Postnikov layers
and geometric purity calculations and requires no enough-injectives
hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Original homology detects equality between maps of objects concentrated in one degree. -/
theorem homology_map_injective_of_isGE_of_isLE (K L : DerivedCategory C) (n : ℤ)
    [K.IsGE n] [K.IsLE n] [L.IsGE n] [L.IsLE n] :
    Function.Injective (fun f : K ⟶ L => (homologyFunctor C n).map f) := by
  intro f g h
  obtain ⟨X, ⟨eK⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  obtain ⟨Y, ⟨eL⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE L n
  let S := singleFunctor C n
  let H := homologyFunctor C n
  change H.map f = H.map g at h
  let f₀ := eK.inv ≫ f ≫ eL.hom
  let g₀ := eK.inv ≫ g ≫ eL.hom
  obtain ⟨f', hf'⟩ := S.map_surjective f₀
  obtain ⟨g', hg'⟩ := S.map_surjective g₀
  have hh : H.map (S.map f') = H.map (S.map g') := by
    rw [hf', hg']
    simp only [f₀, g₀, Functor.map_comp, h]
  have hfg : f' = g' := by
    have h₁ := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C n) f'
    have h₂ := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C n) g'
    dsimp at h₁ h₂
    rw [← h₁, ← h₂, hh]
  have h₀ : f₀ = g₀ := by rw [← hf', ← hg', hfg]
  apply (cancel_epi eK.inv).mp
  apply (cancel_mono eL.hom).mp
  simpa only [Category.assoc] using h₀

/-- A concentrated object is canonically its original homology placed in that degree.
The following homology equation removes the auxiliary presentation choice. -/
def isoSingleHomology (K : DerivedCategory C) (n : ℤ) [K.IsGE n] [K.IsLE n] :
    K ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj K) :=
  let h := exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  let p : Σ Y : C, K ≅ (singleFunctor C n).obj Y := ⟨h.choose, h.choose_spec.some⟩
  p.2 ≪≫ (singleFunctor C n).mapIso
    (((homologyFunctor C n).mapIso p.2 ≪≫
      (singleFunctorCompHomologyFunctorIso C n).app p.1).symm)

/-- The normalized single comparison induces the identity on the original homology. -/
@[reassoc]
theorem isoSingleHomology_homology (K : DerivedCategory C) (n : ℤ)
    [K.IsGE n] [K.IsLE n] :
    (homologyFunctor C n).map (isoSingleHomology K n).hom ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj K) =
      𝟙 _ := by
  let hp := exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  let p : Σ Y : C, K ≅ (singleFunctor C n).obj Y := ⟨hp.choose, hp.choose_spec.some⟩
  let H := homologyFunctor C n
  let S := singleFunctor C n
  let E := singleFunctorCompHomologyFunctorIso C n
  let h : H.obj K ≅ p.1 := H.mapIso p.2 ≪≫ E.app p.1
  have hn := E.hom.naturality h.inv
  change H.map (S.map h.inv) ≫ E.hom.app (H.obj K) = E.hom.app p.1 ≫ h.inv at hn
  change H.map (p.2.hom ≫ S.map h.inv) ≫ E.hom.app (H.obj K) = 𝟙 _
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc]
  exact h.hom_inv_id

/-- The original homology normalization uniquely specifies the single comparison. -/
theorem isoSingleHomology_hom_eq (K : DerivedCategory C) (n : ℤ)
    [K.IsGE n] [K.IsLE n]
    (f : K ⟶ (singleFunctor C n).obj ((homologyFunctor C n).obj K))
    (hf : (homologyFunctor C n).map f ≫
      (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj K) = 𝟙 _) :
    f = (isoSingleHomology K n).hom := by
  apply homology_map_injective_of_isGE_of_isLE K _ n
  apply (cancel_mono
    ((singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj K))).mp
  exact hf.trans (isoSingleHomology_homology K n).symm

/-- The homology-normalized single comparison is natural in every concentrated object. -/
@[reassoc]
theorem isoSingleHomology_naturality {K L : DerivedCategory C} (n : ℤ)
    [K.IsGE n] [K.IsLE n] [L.IsGE n] [L.IsLE n] (f : K ⟶ L) :
    f ≫ (isoSingleHomology L n).hom =
      (isoSingleHomology K n).hom ≫ (singleFunctor C n).map ((homologyFunctor C n).map f) := by
  apply homology_map_injective_of_isGE_of_isLE K _ n
  apply (cancel_mono
    ((singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj L))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [isoSingleHomology_homology]
  have h := (singleFunctorCompHomologyFunctorIso C n).hom.naturality
    ((homologyFunctor C n).map f)
  change (homologyFunctor C n).map
      ((singleFunctor C n).map ((homologyFunctor C n).map f)) ≫
        (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj L) =
      (singleFunctorCompHomologyFunctorIso C n).hom.app ((homologyFunctor C n).obj K) ≫
        (homologyFunctor C n).map f at h
  rw [h, ← Category.assoc, isoSingleHomology_homology, Category.id_comp, Category.comp_id]

end DerivedCategory

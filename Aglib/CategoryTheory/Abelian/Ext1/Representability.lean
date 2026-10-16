/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Abelian.Ext1.Extension
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Realizing degree-one Ext classes by extensions

Every degree-one derived Ext class has an actual short exact representative
with the given endpoints. Distinguished triangles on objects of the abelian
category recover short exact sequences and their canonical connecting maps.
-/
@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Abelian DerivedCategory

namespace CategoryTheory.Abelian.Ext1

universe w w' v u
variable {C : Type u} [Category.{v} C] [Abelian C]

section Derived

variable [HasDerivedCategory.{w'} C]

/-- Degree-zero homology recovers a short exact sequence from a distinguished
triangle whose three terms come from the abelian category. -/
lemma shortExact_of_singleTriangle_distinguished (S : ShortComplex C)
    (δ : (singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g) δ ∈
      distTriang (DerivedCategory C)) : S.ShortExact := by
  let T := Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g) δ
  have hm : Mono ((homologyFunctor C 0).map T.mor₁) := by
    apply (HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0 (by decide)).2
    exact (isZero_of_isGE ((singleFunctor C 0).obj S.X₃) 0 (-1) (by decide)).eq_of_src _ _
  have he : Epi ((homologyFunctor C 0).map T.mor₂) := by
    apply (HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1 (by decide)).2
    exact (isZero_of_isLE ((singleFunctor C 0).obj S.X₁) 0 1 (by decide)).eq_of_tgt _ _
  have hs : (S.map (singleFunctor C 0 ⋙ homologyFunctor C 0)).ShortExact :=
    { exact := HomologySequence.exact₂ T hT 0
      mono_f := hm
      epi_g := he }
  let e := singleFunctorCompHomologyFunctorIso C 0
  apply ShortComplex.shortExact_of_iso (S₁ := S.map (singleFunctor C 0 ⋙ homologyFunctor C 0))
    (ShortComplex.isoMk (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) ?_ ?_) hs
  · exact (e.hom.naturality S.f).symm
  · exact (e.hom.naturality S.g).symm

/-- The third map of a distinguished triangle on a fixed short exact sequence
is its canonical connecting morphism. -/
lemma singleδ_eq_of_distinguished (S : ShortComplex C) (hS : S.ShortExact)
    (δ : (singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g) δ ∈
      distTriang (DerivedCategory C)) : hS.singleδ = δ := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
    hS.singleTriangle
    (Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g) δ)
    hS.singleTriangle_distinguished hT (𝟙 _) (𝟙 _) (by simp)
  obtain ⟨c', rfl⟩ := (singleFunctor C 0).map_surjective c
  have := hS.epi_g
  have hc' : c' = 𝟙 S.X₃ := by
    apply (cancel_epi S.g).1
    apply (singleFunctor C 0).map_injective
    simpa only [Functor.map_comp, Functor.map_id, comp_id, id_comp,
      ShortComplex.ShortExact.singleTriangle_mor₂, Triangle.mk_mor₂] using hc₂
  simpa [hc'] using hc₃

end Derived

/-- Every actual degree-one Ext class has a short-exact representative with
the given endpoints and exactly the prescribed canonical extension class. -/
theorem exists_extension [HasExt.{w} C] {X Y : C} (xi : Ext.{w} X Y 1) :
    ∃ E : Extension X Y, E.extClass = xi := by
  let := HasDerivedCategory.standard C
  obtain ⟨M, i, p, hT⟩ := distinguished_cocone_triangle₂ xi.hom
  let T := Triangle.mk i p xi.hom
  have : M.IsLE 0 := DerivedCategory.TStructure.t.isLE₂ T hT 0
    (by dsimp [T]; infer_instance) (by dsimp [T]; infer_instance)
  have : M.IsGE 0 := DerivedCategory.TStructure.t.isGE₂ T hT 0
    (by dsimp [T]; infer_instance) (by dsimp [T]; infer_instance)
  obtain ⟨B, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M 0
  obtain ⟨i', hi'⟩ := (singleFunctor C 0).map_surjective (i ≫ e.hom)
  obtain ⟨p', hp'⟩ := (singleFunctor C 0).map_surjective (e.inv ≫ p)
  have hzero : i' ≫ p' = 0 := by
    apply (singleFunctor C 0).map_injective
    rw [Functor.map_comp, hi', hp', Functor.map_zero]
    simpa [T] using comp_distTriang_mor_zero₁₂ T hT
  let S := ShortComplex.mk i' p' hzero
  have hT' : Triangle.mk ((singleFunctor C 0).map i') ((singleFunctor C 0).map p')
      xi.hom ∈ distTriang (DerivedCategory C) := by
    apply isomorphic_distinguished T hT _
    exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
      (by simp [hi', T]) (by simp [hp', T]) (by simp [T])
  have hS : S.ShortExact := shortExact_of_singleTriangle_distinguished S xi.hom hT'
  refine ⟨⟨B, i', p', hzero, hS⟩, ?_⟩
  apply Ext.ext
  rw [Extension.extClass, ShortComplex.ShortExact.extClass_hom]
  exact singleδ_eq_of_distinguished S hS xi.hom hT'

end CategoryTheory.Abelian.Ext1

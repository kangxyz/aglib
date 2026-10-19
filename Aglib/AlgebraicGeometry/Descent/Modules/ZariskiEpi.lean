/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.Modules.Zariski
public import Aglib.AlgebraicGeometry.Modules.Pullback.FreeComp

/-!
# Zariski gluing of morphisms under an epimorphism

Let `f i : X i ⟶ S` be a jointly surjective family of open immersions and `π : F ⟶ Q` an
epimorphism of module sheaves on `S`. Morphisms `e i : (f i)^* Q ⟶ (f i)^* Q'` with
`(f i)^* π ≫ e i = (f i)^* π'` glue to a morphism `g : Q ⟶ Q'` with `π ≫ g = π'`
(`exists_comp_eq_of_openImmersion`): the local morphisms form a morphism of descent data, because
its compatibility condition can be checked after the pulled-back epimorphism, and morphisms glue
along such families (`fullyFaithfulToDescentDataOfOpenImmersion`). For two epimorphisms with
compatible local isomorphisms the glued morphism is an isomorphism (`exists_iso_of_openImmersion`).

`toDescentData_obj_free_hom` compares the descent datum of a free sheaf with the pullback
isomorphisms `pullbackFreeIso`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- **Gluing compatible morphisms under an epimorphism**: if `π : F ⟶ Q` is an epimorphism,
`π' : F ⟶ Q'` is any morphism and, on a jointly surjective family of open immersions `f i`, there
are morphisms `e i : (f i)^* Q ⟶ (f i)^* Q'` with `(f i)^* π ≫ e i = (f i)^* π'`, then there is a
morphism `g : Q ⟶ Q'` with `π ≫ g = π'`. -/
theorem exists_comp_eq_of_openImmersion {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : S, ∃ (i : ι) (y : X i), f i y = x)
    {F Q Q' : S.Modules} (π : F ⟶ Q) (π' : F ⟶ Q') [Epi π]
    (e : ∀ i, (pullback (f i)).obj Q ⟶ (pullback (f i)).obj Q')
    (he : ∀ i, (pullback (f i)).map π ≫ e i = (pullback (f i)).map π') :
    ∃ g : Q ⟶ Q', π ≫ g = π' := by
  let hff := fullyFaithfulToDescentDataOfOpenImmersion f hf
  let Φ : (pullbackPseudofunctor.toDescentData f).obj Q ⟶
      (pullbackPseudofunctor.toDescentData f).obj Q' :=
    { hom := fun i ↦ e i
      comm := fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        have c := ((pullbackPseudofunctor.toDescentData f).map π).comm q f₁ f₂ hf₁ hf₂
        have c' := ((pullbackPseudofunctor.toDescentData f).map π').comm q f₁ f₂ hf₁ hf₂
        have : Epi ((pullback f₁).map ((pullback (f i₁)).map π)) := inferInstance
        change (pullback f₁).map (e i₁) ≫ _ = _ ≫ (pullback f₂).map (e i₂)
        change (pullback f₁).map ((pullback (f i₁)).map π) ≫ _ =
          _ ≫ (pullback f₂).map ((pullback (f i₂)).map π) at c
        change (pullback f₁).map ((pullback (f i₁)).map π') ≫ _ =
          _ ≫ (pullback f₂).map ((pullback (f i₂)).map π') at c'
        rw [← cancel_epi ((pullback f₁).map ((pullback (f i₁)).map π)),
          ← CategoryTheory.Functor.map_comp_assoc, he, c', reassoc_of% c,
          ← CategoryTheory.Functor.map_comp, he] }
  refine ⟨hff.preimage Φ, hff.map_injective ?_⟩
  ext i
  rw [CategoryTheory.Functor.map_comp, Pseudofunctor.DescentData.comp_hom, hff.map_preimage]
  exact he i

/-- **Epimorphisms that are locally isomorphic are isomorphic**: the version of
`exists_comp_eq_of_openImmersion` with local isomorphisms. -/
theorem exists_iso_of_openImmersion {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : S, ∃ (i : ι) (y : X i), f i y = x)
    {F Q Q' : S.Modules} (π : F ⟶ Q) (π' : F ⟶ Q') [Epi π] [Epi π']
    (e : ∀ i, (pullback (f i)).obj Q ≅ (pullback (f i)).obj Q')
    (he : ∀ i, (pullback (f i)).map π ≫ (e i).hom = (pullback (f i)).map π') :
    ∃ g : Q ≅ Q', π ≫ g.hom = π' := by
  obtain ⟨g, hg⟩ := exists_comp_eq_of_openImmersion f hf π π' (fun i ↦ (e i).hom) he
  obtain ⟨g', hg'⟩ := exists_comp_eq_of_openImmersion f hf π' π (fun i ↦ (e i).inv) fun i ↦ by
    rw [← he i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨⟨g, g', ?_, ?_⟩, hg⟩
  · rw [← cancel_epi π, reassoc_of% hg, hg', Category.comp_id]
  · rw [← cancel_epi π', reassoc_of% hg', hg, Category.comp_id]

/-- The descent datum of a free sheaf is compatible with the pullback isomorphisms of free
sheaves. -/
theorem toDescentData_obj_free_hom {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (I : Type u) {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((pullbackPseudofunctor.toDescentData f).obj (SheafOfModules.free I)).hom q f₁ f₂ hf₁ hf₂ ≫
        (pullback f₂).map (pullbackFreeIso (f i₂) I).hom ≫ (pullbackFreeIso f₂ I).hom =
      (pullback f₁).map (pullbackFreeIso (f i₁) I).hom ≫ (pullbackFreeIso f₁ I).hom := by
  rw [pullbackPseudofunctor_toDescentData_obj_hom, Category.assoc, Category.assoc,
    Category.assoc, ← pullbackFreeIso_comp, Iso.inv_hom_id_app_assoc, pullbackFreeIso_congr,
    pullbackFreeIso_congr, pullbackFreeIso_comp]

end AlgebraicGeometry.Scheme.Modules

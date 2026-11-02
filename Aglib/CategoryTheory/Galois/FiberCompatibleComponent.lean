/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Galois.FiberCompatible
public import Aglib.CategoryTheory.Galois.RegularActionComponent

/-! # The original connected subobject after fibre-compatible transport

Restrict the transported regular deck action to a supplied actual connected
subobject. No replacement component or connectedness of the whole image is
assumed. The original inclusion equation and deck-group bound are retained.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe c h d j v

variable {C : Type c} [Category.{h} C] [GaloisCategory C]
  {D : Type d} [Category.{j} D] [GaloisCategory D]
  (F : C ⥤ FintypeCat.{v}) [FiberFunctor F]
  (G : D ⥤ FintypeCat.{v}) [FiberFunctor G]
  (T : C ⥤ D) (e : F ≅ T ⋙ G)
  (Y : C) [IsGalois Y] {Z : D} [IsConnected Z]
  (i : Z ⟶ T.obj Y) [Mono i]

include F G e in
/-- The same connected subobject is Galois, with deck transformations given
by unique original source translations preserving its actual inclusion. -/
theorem component_galois_and_aut_embedding_of_fiberCompatible :
    IsGalois Z ∧ ∃ δ : Aut Z →* Aut Y, Function.Injective δ ∧
      (∀ σ, σ.hom ≫ i = i ≫ (Functor.mapAut Y T (δ σ)).hom) ∧
      Nat.card (Aut Z) ∣ Nat.card (Aut Y) := by
  obtain ⟨z⟩ := nonempty_fiber_of_isConnected G Z
  let y := G.map i z
  have hρ := mappedOrbit_bijective_of_fiberCompatible F G T e Y y
  exact ⟨isGalois_of_regularAction_component G (Functor.mapAut Y T) y hρ i z rfl,
    componentTranslationHom G (Functor.mapAut Y T) y hρ i z rfl,
    componentTranslationHom_injective G (Functor.mapAut Y T) y hρ i z rfl,
    componentTranslation_over G (Functor.mapAut Y T) y hρ i z rfl,
    component_aut_card_dvd G (Functor.mapAut Y T) y hρ i z rfl⟩

end CategoryTheory.PreGaloisCategory

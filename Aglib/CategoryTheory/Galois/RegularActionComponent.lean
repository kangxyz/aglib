/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.GroupTheory.Schreier

/-! # Connected components of an object with a regular global action

The component is Mathlib's native connected subobject. Its deck transformations
are the unique original translations preserving that subobject; no arbitrary
Galois refinement or fundamental-group realization is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe c h v a

variable {C : Type c} [Category.{h} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{v}) [FiberFunctor F]
  {A : Type a} [Group A] {Y : C} (ρ : A →* Aut Y)
  (y : F.obj Y) (hρ : Function.Bijective (fun a => F.map (ρ a).hom y))
  {Z : C} [IsConnected Z] (i : Z ⟶ Y) [Mono i]
  (z : F.obj Z) (hz : F.map i z = y)

/-- The coefficient of a deck transformation is its unique original translation,
read at the specified point of the unchanged component. -/
def componentTranslation (σ : Aut Z) : A :=
  (Equiv.ofBijective _ hρ).symm (F.map i (F.map σ.hom z))

omit [Mono i] in
include hz in
/-- The selected translation agrees with the deck transformation as an original
map, not merely on the chosen fibre point. -/
theorem componentTranslation_over (σ : Aut Z) :
    σ.hom ≫ i = i ≫ (ρ (componentTranslation F ρ y hρ i z σ)).hom := by
  apply evaluation_injective_of_isConnected F Z Y z
  simp only [Functor.map_comp, FintypeCat.comp_apply, hz]
  exact ((Equiv.ofBijective _ hρ).apply_symm_apply _).symm

omit [GaloisCategory C] [FiberFunctor F] [IsConnected Z] [Mono i] in
include hz in
/-- The original inclusion equation uniquely determines the translation. -/
theorem componentTranslation_unique (σ : Aut Z) (a : A)
    (ha : σ.hom ≫ i = i ≫ (ρ a).hom) :
    componentTranslation F ρ y hρ i z σ = a := by
  apply hρ.injective
  have he := congrArg (fun f : Z ⟶ Y => F.map f z) ha
  simp only [Functor.map_comp, FintypeCat.comp_apply, hz] at he
  exact ((Equiv.ofBijective _ hρ).apply_symm_apply _).trans he

/-- The original component deck group embeds in the acting group, with the
native automorphism multiplication orientation. -/
def componentTranslationHom : Aut Z →* A where
  toFun := componentTranslation F ρ y hρ i z
  map_one' := componentTranslation_unique F ρ y hρ i z hz 1 1 (by
    rw [map_one]
    change (𝟙 Z) ≫ i = i ≫ (𝟙 Y)
    simp only [Category.id_comp, Category.comp_id])
  map_mul' σ τ := componentTranslation_unique F ρ y hρ i z hz (σ * τ) _ (by
    rw [map_mul]
    change (τ.hom ≫ σ.hom) ≫ i =
      i ≫ ((ρ (componentTranslation F ρ y hρ i z τ)).hom ≫
        (ρ (componentTranslation F ρ y hρ i z σ)).hom)
    rw [Category.assoc, componentTranslation_over F ρ y hρ i z hz σ,
      ← Category.assoc, componentTranslation_over F ρ y hρ i z hz τ]
    simp only [Category.assoc])

/-- Faithfulness of the unchanged component inclusion gives injectivity. -/
theorem componentTranslationHom_injective :
    Function.Injective (componentTranslationHom F ρ y hρ i z hz) := by
  intro σ τ hστ
  apply Iso.ext
  apply (cancel_mono i).mp
  rw [componentTranslation_over F ρ y hρ i z hz σ,
    componentTranslation_over F ρ y hρ i z hz τ]
  exact congrArg (fun a => i ≫ (ρ a).hom) hστ

include hρ hz in
/-- Translations move the selected point to every point of its component.
Uniqueness of the native connected component then makes that component Galois. -/
theorem isGalois_of_regularAction_component : IsGalois Z := by
  have htrans : ∀ w : F.obj Z, ∃ σ : Aut Z, F.map σ.hom z = w := by
    intro w
    obtain ⟨a, ha⟩ := hρ.surjective (F.map i w)
    let : IsIso (ρ a).hom := (ρ a : Y ≅ Y).isIso_hom
    apply connected_component_unique F z w (i ≫ (ρ a).hom) i
    simpa only [Functor.map_comp, FintypeCat.comp_apply, hz] using ha
  apply (isGalois_iff_pretransitive F Z).mpr
  constructor
  intro u w
  obtain ⟨σ, hσ⟩ := htrans u
  obtain ⟨τ, hτ⟩ := htrans w
  refine ⟨τ * σ⁻¹, ?_⟩
  change F.map (σ.inv ≫ τ.hom) u = w
  rw [← hσ, Functor.map_comp, FintypeCat.comp_apply]
  have hinv : F.map σ.inv (F.map σ.hom z) = z := by
    change (F.map σ.hom ≫ F.map σ.inv) z = z
    rw [← Functor.map_comp, (σ : Z ≅ Z).hom_inv_id, Functor.map_id]
    rfl
  rw [hinv]
  exact hτ

include hρ hz in
/-- The actual component deck-group order divides the original acting-group order. -/
theorem component_aut_card_dvd : Nat.card (Aut Z) ∣ Nat.card A :=
  Subgroup.card_dvd_of_injective (componentTranslationHom F ρ y hρ i z hz)
    (componentTranslationHom_injective F ρ y hρ i z hz)

include hρ in
/-- A chosen fibre point lies in an actual Galois connected subobject whose
original deck transformations inject into the original regular acting group. -/
theorem exists_galois_component_of_regularAction :
    ∃ (Z : C) (i : Z ⟶ Y) (z : F.obj Z),
      F.map i z = y ∧ Mono i ∧ IsGalois Z ∧
      ∃ δ : Aut Z →* A, Function.Injective δ ∧
        (∀ σ, σ.hom ≫ i = i ≫ (ρ (δ σ)).hom) ∧
        Nat.card (Aut Z) ∣ Nat.card A := by
  obtain ⟨Z, i, z, hz, hZ, hi⟩ := fiber_in_connected_component F Y y
  let := hZ
  let := hi
  refine ⟨Z, i, z, hz, hi, isGalois_of_regularAction_component F ρ y hρ i z hz,
    componentTranslationHom F ρ y hρ i z hz,
    componentTranslationHom_injective F ρ y hρ i z hz, ?_,
    component_aut_card_dvd F ρ y hρ i z hz⟩
  exact componentTranslation_over F ρ y hρ i z hz

/-- For a finitely generated abelian regular acting group annihilated by `n`,
the original component deck order divides a power of that same `n`. -/
theorem component_aut_card_dvd_pow {B : Type a} [CommGroup B] [Group.FG B]
    (ρ : B →* Aut Y) (y : F.obj Y)
    (hρ : Function.Bijective (fun b => F.map (ρ b).hom y))
    (i : Z ⟶ Y) [Mono i] (z : F.obj Z) (hz : F.map i z = y)
    {n : ℕ} (hn : ∀ b : B, b ^ n = 1) :
    Nat.card (Aut Z) ∣ n ^ Group.rank B :=
  (component_aut_card_dvd F ρ y hρ i z hz).trans
    (card_dvd_exponent_pow_rank' B hn)

end CategoryTheory.PreGaloisCategory

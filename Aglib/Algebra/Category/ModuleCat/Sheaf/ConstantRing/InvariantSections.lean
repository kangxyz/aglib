/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.PresheafAutomorphismAction
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RepresentationTheory.Invariants

/-! # Original linear section descent from a covering graph family

The actual overlap projections and their native pullback property are retained.
A covering family of the actual action graphs turns invariance into overlap
compatibility. Native sheaf amalgamation constructs the descended linear map;
separatedness and its restriction law prove the invariant-section isomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf.ConstantRing

universe u v r w g

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Type r} [CommRing R] (F : CategoryTheory.Sheaf J (ModuleCat.{w} R))
  {T U V : C} {G : Type g} [Group G] (action : G →* Aut U)

/-- The original restriction has invariant image when the actual action preserves the cover. -/
theorem sectionRestriction_invariant (q : U ⟶ T)
    (hq : ∀ σ : G, (action σ).hom ≫ q = q) (s : F.obj.obj (op T)) :
    F.obj.map q.op s ∈ (Presheaf.restrictionRepresentation F.obj action).invariants := by
  intro σ
  change F.obj.map (action σ).inv.op (F.obj.map q.op s) = _
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp]
  have h : (action σ).inv ≫ q = q := by
    have h := hq σ⁻¹
    rw [map_inv] at h
    exact h
  rw [h]

/-- Literal restriction, with codomain the native invariant submodule. -/
def invariantRestriction (q : U ⟶ T)
    (hq : ∀ σ : G, (action σ).hom ≫ q = q) :
    F.obj.obj (op T) ⟶
      ModuleCat.of R (Presheaf.restrictionRepresentation F.obj action).invariants :=
  ModuleCat.ofHom (LinearMap.codRestrict _ (F.obj.map q.op).hom
    (sectionRestriction_invariant F action q hq))

@[reassoc (attr := simp)]
theorem invariantRestriction_subtype (q : U ⟶ T)
    (hq : ∀ σ : G, (action σ).hom ≫ q = q) :
    invariantRestriction F action q hq ≫
      ModuleCat.ofHom (Presheaf.restrictionRepresentation F.obj action).invariants.subtype =
        F.obj.map q.op := rfl

/-- Sheaf separatedness on the actual graph cover turns invariance into overlap equality. -/
theorem invariantSection_overlap (p₁ p₂ : V ⟶ U) (graph : G → (U ⟶ V))
    (hgraph : Sieve.ofArrows (fun _ : G => U) graph ∈ J V)
    (hfst : ∀ σ, graph σ ≫ p₁ = 𝟙 U)
    (hsnd : ∀ σ, graph σ ≫ p₂ = (action σ).hom)
    {E : ModuleCat.{w} R} (a : E ⟶ F.obj.obj (op U))
    (ha : ∀ σ : G, a ≫ F.obj.map (action σ).hom.op = a) :
    a ≫ F.obj.map p₁.op = a ≫ F.obj.map p₂.op := by
  apply F.property.hom_ext_ofArrows graph hgraph
  intro σ
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, hfst, hsnd]
  rw [op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact (ha σ).symm

section Descent

variable (q : U ⟶ T)
  (hq : Sieve.ofArrows (fun _ : Unit => U) (fun _ => q) ∈ J T)
  (p₁ p₂ : V ⟶ U) (hp : IsPullback p₁ p₂ q q)
  (overlap : ∀ {E : ModuleCat.{w} R} (a : E ⟶ F.obj.obj (op U)),
    (∀ σ : G, a ≫ F.obj.map (action σ).hom.op = a) →
      a ≫ F.obj.map p₁.op = a ≫ F.obj.map p₂.op)

include hp overlap in
/-- The native pullback of the actual overlap gives compatibility on every test object. -/
theorem invariantSection_compatible {E : ModuleCat.{w} R}
    (a : E ⟶ F.obj.obj (op U))
    (ha : ∀ σ : G, a ≫ F.obj.map (action σ).hom.op = a)
    {W : C} (b c : W ⟶ U) (hbc : b ≫ q = c ≫ q) :
    a ≫ F.obj.map b.op = a ≫ F.obj.map c.op := by
  let k := hp.lift b c hbc
  have hk₁ : k ≫ p₁ = b := hp.lift_fst b c hbc
  have hk₂ : k ≫ p₂ = c := hp.lift_snd b c hbc
  rw [← hk₁, ← hk₂, op_comp, op_comp, Functor.map_comp, Functor.map_comp,
    ← Category.assoc, ← Category.assoc, overlap a ha]

/-- The descended linear map is native categorical amalgamation on the original cover. -/
def invariantSectionDescend {E : ModuleCat.{w} R}
    (a : E ⟶ F.obj.obj (op U))
    (ha : ∀ σ : G, a ≫ F.obj.map (action σ).hom.op = a) : E ⟶ F.obj.obj (op T) :=
  F.property.amalgamateOfArrows (fun _ : Unit => q) hq (fun _ => a)
    (fun _ _ _ b c hbc => invariantSection_compatible F action q p₁ p₂ hp overlap a ha b c hbc)

/-- The actual descended map restricts to precisely the supplied original linear map. -/
@[reassoc (attr := simp)]
theorem invariantSectionDescend_restriction {E : ModuleCat.{w} R}
    (a : E ⟶ F.obj.obj (op U))
    (ha : ∀ σ : G, a ≫ F.obj.map (action σ).hom.op = a) :
    invariantSectionDescend F action q hq p₁ p₂ hp overlap a ha ≫ F.obj.map q.op = a :=
  F.property.amalgamateOfArrows_map (fun _ : Unit => q) hq (fun _ => a)
    (fun _ _ _ b c hbc => invariantSection_compatible F action q p₁ p₂ hp overlap a ha b c hbc) ()

/-- The original invariant inclusion is fixed under the original forward restrictions. -/
theorem invariantSections_subtype_fixed (σ : G) :
    ModuleCat.ofHom (Presheaf.restrictionRepresentation F.obj action).invariants.subtype ≫
      F.obj.map (action σ).hom.op =
        ModuleCat.ofHom (Presheaf.restrictionRepresentation F.obj action).invariants.subtype := by
  ext s
  change F.obj.map (action σ).hom.op s.val = s.val
  have h := s.property σ⁻¹
  rw [Presheaf.restrictionRepresentation_apply, map_inv] at h
  exact h

/-- Original restriction and native amalgamation are inverse on the actual invariant module. -/
def invariantSectionsIso (haction : ∀ σ : G, (action σ).hom ≫ q = q) :
    F.obj.obj (op T) ≅
      ModuleCat.of R (Presheaf.restrictionRepresentation F.obj action).invariants where
  hom := invariantRestriction F action q haction
  inv := invariantSectionDescend F action q hq p₁ p₂ hp overlap
    (ModuleCat.ofHom (Presheaf.restrictionRepresentation F.obj action).invariants.subtype)
    (invariantSections_subtype_fixed F action)
  hom_inv_id := by
    apply F.property.hom_ext_ofArrows (fun _ : Unit => q) hq
    intro i
    change (invariantRestriction F action q haction ≫
      invariantSectionDescend F action q hq p₁ p₂ hp overlap _ _) ≫ F.obj.map q.op =
        𝟙 _ ≫ F.obj.map q.op
    rw [Category.assoc, invariantSectionDescend_restriction,
      invariantRestriction_subtype, Category.id_comp]
  inv_hom_id := by
    ext s
    exact ConcreteCategory.congr_hom
      (invariantSectionDescend_restriction F action q hq p₁ p₂ hp overlap
        (ModuleCat.ofHom (Presheaf.restrictionRepresentation F.obj action).invariants.subtype)
        (invariantSections_subtype_fixed F action)) s

end Descent

end ModuleCat.Sheaf.ConstantRing

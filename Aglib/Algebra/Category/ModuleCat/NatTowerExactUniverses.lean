/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.NatTower

/-!
# Compatible-section surjectivity across independent module universes

A stagewise surjective morphism of natural-number towers is surjective on
native compatible sections if the adjacent maps on its kernels are surjective.
The proof corrects a lift by a kernel element, then applies dependent choice
to the actual fibre functor. It does not assert levelwise exactness of adic
reduction, nor does it require finite modules or a Noetherian ring.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v v' w w'

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- A compatible family of linear maps acts on native sections, even when
the source and target module universes differ. -/
def sectionsMapOfLinearMaps {J : Type w} [Category.{w'} J]
    {F : J ⥤ ModuleCat.{v} R} {G : J ⥤ ModuleCat.{v'} R}
    (φ : ∀ j, F.obj j →ₗ[R] G.obj j)
    (hφn : ∀ {j k} (f : j ⟶ k) (x : F.obj j),
      φ k (F.map f x) = G.map f (φ j x)) :
    sectionsSubmodule F →ₗ[R] sectionsSubmodule G where
  toFun s := ⟨fun j => φ j (s.val j), by
    intro j k f
    have h := hφn f (s.val j)
    change φ k (F.map f (s.val j)) = G.map f (φ j (s.val j)) at h
    have hs : F.map f (s.val j) = s.val k := s.property f
    rw [hs] at h
    exact h.symm⟩
  map_add' s t := by
    apply Subtype.ext
    funext j
    exact (φ j).map_add (s.val j) (t.val j)
  map_smul' r s := by
    apply Subtype.ext
    funext j
    exact (φ j).map_smul r (s.val j)

@[simp]
theorem sectionsMapOfLinearMaps_apply {J : Type w} [Category.{w'} J]
    {F : J ⥤ ModuleCat.{v} R} {G : J ⥤ ModuleCat.{v'} R}
    (φ : ∀ j, F.obj j →ₗ[R] G.obj j)
    (hφn : ∀ {j k} (f : j ⟶ k) (x : F.obj j),
      φ k (F.map f x) = G.map f (φ j x))
    (s : sectionsSubmodule F) (j : J) :
    (sectionsMapOfLinearMaps φ hφn s).val j = φ j (s.val j) := rfl

variable {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} {G : ℕᵒᵖ ⥤ ModuleCat.{v'} R}
  (φ : ∀ j, F.obj j →ₗ[R] G.obj j)
  (hφn : ∀ {j k} (f : j ⟶ k) (x : F.obj j),
    φ k (F.map f x) = G.map f (φ j x))

/-- The original fibre over a compatible target section, as a type-valued tower. -/
def sectionFiberOfLinearMaps (y : sectionsSubmodule G) : ℕᵒᵖ ⥤ Type v where
  obj j := {x : F.obj j // φ j x = y.val j}
  map f := ↾(fun x => ⟨F.map f x.val, by
    have h := hφn f x.val
    change φ _ (F.map f x.val) = G.map f (φ _ x.val) at h
    rw [h, x.property]
    exact y.property f⟩)
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (F.map_id j) x.val
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (F.map_comp f g) x.val

/-- Kernel corrections make the adjacent maps of every original fibre
surjective. The kernel premise refers to actual elements and actual maps. -/
theorem sectionFiberOfLinearMaps_map_surjective
    (hφ : ∀ n, Function.Surjective (φ (op n)))
    (hK : ∀ n (x : F.obj (op n)), φ (op n) x = 0 →
      ∃ z : F.obj (op (n + 1)), φ (op (n + 1)) z = 0 ∧
        F.map (homOfLE (Nat.le_succ n)).op z = x)
    (y : sectionsSubmodule G) (n : ℕ) :
    Function.Surjective ((sectionFiberOfLinearMaps φ hφn y).map (homOfLE (Nat.le_succ n)).op) := by
  intro x
  obtain ⟨z, hz⟩ := hφ (n + 1) (y.val (op (n + 1)))
  let t := F.map (homOfLE (Nat.le_succ n)).op
  have ht : φ (op n) (t z) = y.val (op n) := by
    have h := hφn (homOfLE (Nat.le_succ n)).op z
    change φ (op n) (t z) =
      G.map (homOfLE (Nat.le_succ n)).op (φ (op (n + 1)) z) at h
    rw [h, hz]
    exact y.property _
  have hk : φ (op n) (t z - x.val) = 0 := by
    rw [map_sub, ht, x.property, sub_self]
  obtain ⟨k, hk, htk⟩ := hK n (t z - x.val) hk
  refine ⟨⟨z - k, ?_⟩, ?_⟩
  · rw [map_sub, hz, hk, sub_zero]
  · apply Subtype.ext
    change t (z - k) = x.val
    rw [map_sub, htk, sub_sub_cancel]

/-- Surjective finite-level maps and surjective kernel transitions imply
surjectivity on the original compatible-section submodules. -/
theorem sectionsMapOfLinearMaps_surjective
    (hφ : ∀ n, Function.Surjective (φ (op n)))
    (hK : ∀ n (x : F.obj (op n)), φ (op n) x = 0 →
      ∃ z : F.obj (op (n + 1)), φ (op (n + 1)) z = 0 ∧
        F.map (homOfLE (Nat.le_succ n)).op z = x) :
    Function.Surjective (sectionsMapOfLinearMaps φ hφn) := by
  intro y
  obtain ⟨x, hx⟩ := hφ 0 (y.val (op 0))
  obtain ⟨s, _⟩ := (sectionFiberOfLinearMaps φ hφn y).sections_eval_surjective_of_surjective_succ
    (sectionFiberOfLinearMaps_map_surjective φ hφn hφ hK y) 0 ⟨x, hx⟩
  let z : sectionsSubmodule F := ⟨fun j => (s.val j).val, by
    intro j k f
    exact congrArg Subtype.val (s.property f)⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  funext j
  exact (s.val j).property

end ModuleCat

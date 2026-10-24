/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.EpiLifting

/-!
# Small representatives of objects with bounded subobject cardinality

The separator gives an epimorphism from a fixed coproduct to every object
with the prescribed subobject bound. Quotients of that fixed object are
parameterized by its subobjects in the opposite abelian category. Thus the
representative index actually lies in the Grothendieck universe.

This is the object-size step of Stacks 079E, not an assumed small family.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits Opposite

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

include hG

/-- A single coproduct covers every object whose subobject cardinal is bounded
by the cardinal of its index. -/
lemma exists_epi_from_cardinal_coproduct (κ : Cardinal.{w}) (N : C)
    (hN : Cardinal.mk (Shrink.{w} (Subobject N)) ≤ κ) :
    ∃ p : (∐ fun _ : κ.out ↦ G) ⟶ N, Epi p := by
  classical
  obtain ⟨a, ha⟩ := exists_epi_comp_from_subobject_coproduct hG (𝟙 N)
  have ha' : Epi a := by simpa using ha
  have hN' : Cardinal.mk (Shrink.{w} (Subobject N)) ≤ Cardinal.mk κ.out := by
    simpa using hN
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hN'
  let : Nonempty (Shrink.{w} (Subobject N)) :=
    ⟨equivShrink.{w} (Subobject N) ⊤⟩
  obtain ⟨r, hr⟩ := j.injective.hasLeftInverse
  let p : (∐ fun _ : κ.out ↦ G) ⟶ N :=
    Sigma.desc (fun k ↦ Sigma.ι (fun _ : Shrink.{w} (Subobject N) ↦ G) (r k) ≫ a)
  let b : (∐ fun _ : Shrink.{w} (Subobject N) ↦ G) ⟶ (∐ fun _ : κ.out ↦ G) :=
    Sigma.desc (fun k ↦ Sigma.ι (fun _ : κ.out ↦ G) (j k))
  have hbp : b ≫ p = a := by
    apply Sigma.hom_ext
    intro k
    simp [b, p, hr k]
  refine ⟨p, ?_⟩
  have : Epi (b ≫ p) := by rw [hbp]; exact ha'
  exact epi_of_epi b p

/-- An explicit small family represents all objects with bounded subobject
cardinality. Its parameters are quotients of one fixed separator coproduct. -/
lemma exists_small_object_representatives (κ : Cardinal.{w}) :
    ∃ (I : Type w) (Q : I → C), ∀ N : C,
      Cardinal.mk (Shrink.{w} (Subobject N)) ≤ κ →
        ∃ i : I, Nonempty (N ≅ Q i) := by
  let P : C := ∐ fun _ : κ.out ↦ G
  let e := equivShrink.{w} (Subobject (op P))
  refine ⟨Shrink.{w} (Subobject (op P)),
    fun i ↦ unop ((e.symm i : Subobject (op P)) : Cᵒᵖ), ?_⟩
  intro N hN
  obtain ⟨p, hp⟩ := exists_epi_from_cardinal_coproduct hG κ N hN
  have := hp
  refine ⟨e (Subobject.mk p.op), ?_⟩
  simpa only [Equiv.symm_apply_apply] using
    (show Nonempty (N ≅ unop ((Subobject.mk p.op : Subobject (op P)) : Cᵒᵖ)) from
      ⟨(Subobject.underlyingIso p.op).unop⟩)

end CategoryTheory.IsGrothendieckAbelian

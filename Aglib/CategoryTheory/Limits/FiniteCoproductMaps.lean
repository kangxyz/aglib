/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.Data.Fintype.Option

/-!
# Maps out of and between finite coproducts

* `CategoryTheory.Limits.Sigma.desc_induction`: in a category with finite coproducts, let `P` be a
  property of morphisms into a fixed object `X` that is stable under precomposition with
  isomorphisms, holds for morphisms out of initial objects and is stable under binary
  `coprod.desc`. Then `P (Sigma.desc f)` for every finite family `f j : Y j ⟶ X` with all `P (f j)`.
  The proof is the induction `Finite.induction_empty_option` on the index type, through the
  decomposition `CategoryTheory.Limits.sigmaOptionIso : Y none ⨿ ∐ (Y ∘ some) ≅ ∐ Y`.
* `CategoryTheory.FinitaryExtensive.isPullback_sigmaι_sigmaMap`: in a finitary extensive category,
  for a finite family `f j : X j ⟶ Y j` the square of `Sigma.ι X j`, `f j`, `Sigma.map f` and
  `Sigma.ι Y j` is a pullback, by the van Kampen property of finite coproducts
  (`FinitaryExtensive.isVanKampen_finiteCoproducts`).

For schemes, Mathlib's `isPullback_inl_inl_coprodMap` is the binary form of
`isPullback_sigmaι_sigmaMap`, and `Sigma.desc_induction` extends Mathlib's binary
`IsFinite (coprod.desc f g)` to finite families; compare Mathlib's object-level
`ObjectProperty.IsClosedUnderFiniteCoproducts.mk'`. Consumer: the finite disjoint unions of
H-quasi-projective schemes (`Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.Coproduct`,
Picard plan task HQ4), through `Sigma.desc_induction`.
-/

@[expose] public section

noncomputable section

universe w

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasFiniteCoproducts C]

/-- The coproduct over `Option α` is the binary coproduct of the `none` summand with the coproduct
over `α`. -/
def sigmaOptionIso {α : Type w} [Finite α] (Y : Option α → C) :
    Y none ⨿ ∐ (fun a => Y (some a)) ≅ ∐ Y where
  hom := coprod.desc (Sigma.ι Y none) (Sigma.desc fun a => Sigma.ι Y (some a))
  inv := Sigma.desc fun o => Option.rec (motive := fun o => Y o ⟶ Y none ⨿ ∐ (fun a => Y (some a)))
    coprod.inl (fun a => Sigma.ι (fun a => Y (some a)) a ≫ coprod.inr) o
  hom_inv_id := by
    apply coprod.hom_ext
    · simp
    · apply Sigma.hom_ext
      intro a
      simp
  inv_hom_id := by
    apply Sigma.hom_ext
    intro o
    cases o <;> simp

/-- Under `sigmaOptionIso`, `Sigma.desc f` is the binary `coprod.desc` of the `none` component and
the `Sigma.desc` of the remaining components. -/
theorem sigmaOptionIso_hom_desc {α : Type w} [Finite α] {Y : Option α → C} {X : C}
    (f : ∀ o, Y o ⟶ X) :
    (sigmaOptionIso Y).hom ≫ Sigma.desc f =
      coprod.desc (f none) (Sigma.desc fun a => f (some a)) := by
  apply coprod.hom_ext
  · simp [sigmaOptionIso]
  · apply Sigma.hom_ext
    intro a
    simp [sigmaOptionIso]

variable {X : C}

/-- **Induction for maps out of finite coproducts.** A property `P` of morphisms into `X` that is
stable under precomposition with isomorphisms, holds for morphisms out of initial objects and is
stable under binary `coprod.desc` holds for `Sigma.desc f` whenever it holds for every `f j`, for
every finite index type. -/
theorem Sigma.desc_induction (P : ∀ ⦃Y : C⦄, (Y ⟶ X) → Prop)
    (iso : ∀ ⦃Y Y' : C⦄ (e : Y ≅ Y') (f : Y' ⟶ X), P f → P (e.hom ≫ f))
    (initial : ∀ ⦃Y : C⦄ (f : Y ⟶ X), IsInitial Y → P f)
    (coprod : ∀ ⦃Y₁ Y₂ : C⦄ (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X), P f₁ → P f₂ → P (coprod.desc f₁ f₂))
    {J : Type w} [Finite J] {Y : J → C} (f : ∀ j, Y j ⟶ X) (hf : ∀ j, P (f j)) :
    P (Sigma.desc f) := by
  revert Y
  refine Finite.induction_empty_option (P := fun J => ∀ [Finite J] {Y : J → C}
    (f : ∀ j, Y j ⟶ X), (∀ j, P (f j)) → P (Sigma.desc f)) ?_ ?_ ?_ J
  · intro α β e ih _ Y f hf
    have : Finite α := Finite.of_equiv β e.symm
    have h := ih (Y := Y ∘ e) (fun a => f (e a)) (fun a => hf (e a))
    have he : Sigma.desc (f := Y ∘ e) (fun a => f (e a)) =
        (Sigma.reindex e Y).hom ≫ Sigma.desc f := by
      apply Sigma.hom_ext
      intro a
      simp
    rw [he] at h
    simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using iso (Sigma.reindex e Y).symm _ h
  · intro _ Y f _
    exact initial _ (IsInitial.ofUniqueHom (fun Z => Sigma.desc fun j => PEmpty.elim j)
      (fun Z m => Sigma.hom_ext _ _ fun j => PEmpty.elim j))
  · intro α _ ih _ Y f hf
    have h := coprod _ _ (hf none) (ih (Y := fun a => Y (some a)) (fun a => f (some a))
      (fun a => hf (some a)))
    rw [← sigmaOptionIso_hom_desc] at h
    simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using iso (sigmaOptionIso Y).symm _ h

end CategoryTheory.Limits

namespace CategoryTheory.FinitaryExtensive

open Limits

variable {C : Type*} [Category* C] [FinitaryExtensive C]

/-- **Coproduct maps are cartesian over the summands**: in a finitary extensive category, for a
finite family `f j : X j ⟶ Y j`, the inclusion of the `j`-th summand of `∐ X` is the pullback of the
inclusion of the `j`-th summand of `∐ Y` along `Sigma.map f`. -/
theorem isPullback_sigmaι_sigmaMap {J : Type w} [Finite J] {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    (j : J) : IsPullback (Sigma.ι X j) (f j) (Limits.Sigma.map f) (Sigma.ι Y j) :=
  (isVanKampen_finiteCoproducts (coproductIsCoproduct Y) (Cofan.mk (∐ X) (Sigma.ι X))
    (Discrete.natTrans fun j => f j.as) (Limits.Sigma.map f) (by ext; simp)
    (NatTrans.Equifibered.of_discrete _)).mp ⟨coproductIsCoproduct X⟩ ⟨j⟩

end CategoryTheory.FinitaryExtensive

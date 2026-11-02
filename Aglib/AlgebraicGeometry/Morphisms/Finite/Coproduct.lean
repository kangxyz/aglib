/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Finiteness of the actual finite coproduct morphism

The native finite coproduct cofan decomposes into the native binary cofan.
Induction and canonical reindexing prove finiteness of the original
`Sigma.desc`, including the empty family. No source-locality of finiteness
or replacement of the displayed coproduct morphism is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

private theorem isFinite_fin_sigmaDesc (n : ℕ) {S : Scheme.{u}}
    (X : Fin n → Scheme.{u}) (f : ∀ i, X i ⟶ S) [∀ i, IsFinite (f i)] :
    IsFinite (Sigma.desc f) := by
  induction n with
  | zero =>
    let : IsEmpty (∐ X : Scheme.{u}) := ⟨fun x => Fin.elim0 ((sigmaOpenCover X).idx x)⟩
    infer_instance
  | succ n ih =>
    let : IsFinite (Sigma.desc fun i : Fin n => f i.succ) :=
      ih (fun i => X i.succ) (fun i => f i.succ)
    let hC := extendCofanIsColimit X
      (colimit.isColimit (Discrete.functor fun i : Fin n => X i.succ))
      (colimit.isColimit (pair (X 0) (∐ fun i : Fin n => X i.succ)))
    let e := (colimit.isColimit (Discrete.functor X)).coconePointUniqueUpToIso hC
    let : IsFinite (hC.desc (Cofan.mk S f)) := by
      change IsFinite (coprod.desc (f 0) (Sigma.desc fun i : Fin n => f i.succ))
      infer_instance
    rw [show Sigma.desc f = e.hom ≫ hC.desc (Cofan.mk S f) from
      (IsColimit.coconePointUniqueUpToIso_hom_desc
        (colimit.isColimit (Discrete.functor X)) hC).symm]
    infer_instance

/-- A finite family of finite maps has finite native coproduct descent.
The index universe is independent of the scheme universe. -/
theorem isFinite_sigmaDesc {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ S) [∀ i, IsFinite (f i)] :
    IsFinite (Sigma.desc f) := by
  let : Fintype ι := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  let g := fun i => f (e i)
  let E : (∐ (X ∘ e) : Scheme.{u}) ≅ (∐ X : Scheme.{u}) := Sigma.reindex e X
  have hg : IsFinite (Sigma.desc g) := isFinite_fin_sigmaDesc _ (X ∘ e) g
  have hE : IsFinite E.inv := inferInstance
  have h : Sigma.desc f = E.inv ≫ Sigma.desc g := by
    apply (cancel_epi E.hom).mp
    apply Sigma.hom_ext
    intro i
    simp [E, g]
  rw [h]
  exact MorphismProperty.comp_mem (@IsFinite : MorphismProperty Scheme.{u}) _ _ hE hg

end AlgebraicGeometry

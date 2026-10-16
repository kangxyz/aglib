/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Finite iterated native products of schemes over a base

The empty product is the actual identity of the base. Each successor is the
native binary product in `Over S`, compared with the native scheme pullback.
The structure maps preserve properness and surjectivity, and the original
componentwise product map preserves closed immersions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The native over-category binary product has the displayed pullback structure map. -/
theorem overProd_hom_eq (X Y : Over S) :
    (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫
      pullback.fst X.hom Y.hom ≫ X.hom := by
  rw [Over.prodLeftIsoPullback_hom_fst_assoc]
  exact (Over.w (prod.fst : X ⨯ Y ⟶ X)).symm

/-- The structure map of a native binary product of proper schemes over `S` is proper. -/
theorem isProper_overProd (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⨯ Y).hom := by
  rw [overProd_hom_eq]
  infer_instance

/-- The structure map of a native binary product of surjective schemes over `S` is surjective. -/
theorem surjective_overProd (X Y : Over S) [Surjective X.hom] [Surjective Y.hom] :
    Surjective (X ⨯ Y).hom := by
  rw [overProd_hom_eq]
  infer_instance

/-- The original componentwise map of two native over-products is a closed immersion
when both original component maps are closed immersions. -/
theorem isClosedImmersion_overProd_map {X₁ X₂ Y₁ Y₂ : Over S}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [IsClosedImmersion f.left] [IsClosedImmersion g.left] :
    IsClosedImmersion (prod.map f g).left := by
  let t := pullback.map X₁.hom Y₁.hom X₂.hom Y₂.hom f.left g.left (𝟙 S)
    ((Category.comp_id _).trans f.w.symm) ((Category.comp_id _).trans g.w.symm)
  have ht : IsClosedImmersion t :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u}) inferInstance inferInstance
      f.w.symm g.w.symm
  have he : (prod.map f g).left =
      (Over.prodLeftIsoPullback X₁ Y₁).hom ≫ t ≫ (Over.prodLeftIsoPullback X₂ Y₂).inv := by
    apply (cancel_mono (Over.prodLeftIsoPullback X₂ Y₂).hom).mp
    apply pullback.hom_ext <;>
      simp [t, pullback.map, ← Over.comp_left]
  rw [he]
  infer_instance

/-- A finite iteration of native products in `Over S`, starting from the actual identity. -/
def finiteProductOver : {n : ℕ} → (Fin n → Over S) → Over S
  | 0, _ => Over.mk (𝟙 S)
  | n + 1, X => X 0 ⨯ finiteProductOver (fun i : Fin n => X i.succ)

@[simp]
theorem finiteProductOver_zero (X : Fin 0 → Over S) :
    finiteProductOver X = Over.mk (𝟙 S) := rfl

@[simp]
theorem finiteProductOver_succ {n : ℕ} (X : Fin (n + 1) → Over S) :
    finiteProductOver X = (X 0 ⨯ finiteProductOver (fun i : Fin n => X i.succ)) := rfl

/-- The original projection of a finite native over-product. -/
def finiteProductOverπ : {n : ℕ} → (X : Fin n → Over S) →
    (i : Fin n) → (finiteProductOver X ⟶ X i)
  | 0, _, i => i.elim0
  | n + 1, X, i => Fin.cases prod.fst
      (fun j => prod.snd ≫ finiteProductOverπ (fun k : Fin n => X k.succ) j) i

@[simp]
theorem finiteProductOverπ_zero {n : ℕ} (X : Fin (n + 1) → Over S) :
    finiteProductOverπ X 0 = prod.fst := by
  simp only [finiteProductOverπ, Fin.cases_zero]

@[simp]
theorem finiteProductOverπ_succ {n : ℕ} (X : Fin (n + 1) → Over S) (i : Fin n) :
    finiteProductOverπ X i.succ =
      prod.snd ≫ finiteProductOverπ (fun j : Fin n => X j.succ) i := by
  simp only [finiteProductOverπ, Fin.cases_succ]

@[reassoc (attr := simp)]
theorem finiteProductOverπ_hom {n : ℕ} (X : Fin n → Over S) (i : Fin n) :
    (finiteProductOverπ X i).left ≫ (X i).hom = (finiteProductOver X).hom :=
  (finiteProductOverπ X i).w

/-- The lift into a finite native over-product, assembled from the original binary lifts. -/
def finiteProductOverLift {T : Over S} : {n : ℕ} → (X : Fin n → Over S) →
    (∀ i, T ⟶ X i) → (T ⟶ finiteProductOver X)
  | 0, _, _ => Over.mkIdTerminal.from T
  | n + 1, X, f => prod.lift (f 0)
      (finiteProductOverLift (fun i : Fin n => X i.succ) (fun i => f i.succ))

@[reassoc (attr := simp)]
theorem finiteProductOverLift_π {T : Over S} {n : ℕ} (X : Fin n → Over S)
    (f : ∀ i, T ⟶ X i) (i : Fin n) :
    finiteProductOverLift X f ≫ finiteProductOverπ X i = f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp only [finiteProductOverLift, finiteProductOverπ_zero, prod.lift_fst]
    | succ i =>
      simp only [finiteProductOverLift, finiteProductOverπ_succ, prod.lift_snd_assoc, ih]

/-- Morphisms into a finite native over-product are determined by its original projections. -/
@[ext]
theorem finiteProductOver_hom_ext {T : Over S} {n : ℕ} (X : Fin n → Over S)
    {f g : T ⟶ finiteProductOver X}
    (h : ∀ i, f ≫ finiteProductOverπ X i = g ≫ finiteProductOverπ X i) : f = g := by
  induction n with
  | zero => exact Over.mkIdTerminal.hom_ext f g
  | succ n ih =>
    apply prod.hom_ext
    · simpa only [finiteProductOverπ_zero] using h 0
    · apply ih
      intro i
      simpa only [finiteProductOverπ_succ, Category.assoc] using h i.succ

/-- The original componentwise map between finite native over-products. -/
def finiteProductOverMap : {n : ℕ} → {X Y : Fin n → Over S} →
    (∀ i, X i ⟶ Y i) → (finiteProductOver X ⟶ finiteProductOver Y)
  | 0, _, _, _ => 𝟙 _
  | n + 1, _, _, f => prod.map (f 0) (finiteProductOverMap (fun i : Fin n => f i.succ))

@[reassoc (attr := simp)]
theorem finiteProductOverMap_π {n : ℕ} {X Y : Fin n → Over S}
    (f : ∀ i, X i ⟶ Y i) (i : Fin n) :
    finiteProductOverMap f ≫ finiteProductOverπ Y i = finiteProductOverπ X i ≫ f i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp only [finiteProductOverMap, finiteProductOverπ, Fin.cases_zero, prod.map_fst]
    | succ i =>
      simp only [finiteProductOverMap, finiteProductOverπ, Fin.cases_succ, Category.assoc,
        prod.map_snd_assoc, ih]

/-- Finite native products of proper schemes have proper original structure map. -/
theorem isProper_finiteProductOver {n : ℕ} (X : Fin n → Over S)
    [∀ i, IsProper (X i).hom] : IsProper (finiteProductOver X).hom := by
  induction n with
  | zero => change IsProper (𝟙 S); infer_instance
  | succ n ih =>
    have : IsProper (finiteProductOver (fun i : Fin n => X i.succ)).hom := ih _
    exact isProper_overProd _ _

/-- Finite native products of surjective schemes have surjective original structure map. -/
theorem surjective_finiteProductOver {n : ℕ} (X : Fin n → Over S)
    [∀ i, Surjective (X i).hom] : Surjective (finiteProductOver X).hom := by
  induction n with
  | zero => change Surjective (𝟙 S); infer_instance
  | succ n ih =>
    have : Surjective (finiteProductOver (fun i : Fin n => X i.succ)).hom := ih _
    exact surjective_overProd _ _

/-- A finite native product of isomorphisms to the base has isomorphic structure map. -/
theorem isIso_finiteProductOver {n : ℕ} (X : Fin n → Over S)
    [∀ i, IsIso (X i).hom] : IsIso (finiteProductOver X).hom := by
  induction n with
  | zero => change IsIso (𝟙 S); infer_instance
  | succ n ih =>
    have : IsIso (finiteProductOver (fun i : Fin n => X i.succ)).hom := ih _
    rw [finiteProductOver_succ, overProd_hom_eq]
    infer_instance

/-- The native finite product map of closed immersions is a closed immersion. -/
theorem isClosedImmersion_finiteProductOverMap {n : ℕ} {X Y : Fin n → Over S}
    (f : ∀ i, X i ⟶ Y i) [∀ i, IsClosedImmersion (f i).left] :
    IsClosedImmersion (finiteProductOverMap f).left := by
  induction n with
  | zero => change IsClosedImmersion (𝟙 S); infer_instance
  | succ n ih =>
    have : IsClosedImmersion (finiteProductOverMap (fun i : Fin n => f i.succ)).left := ih _
    exact isClosedImmersion_overProd_map _ _

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.RestrictionData.OfMaps

/-! # Complete scalar linearization of original additive restriction data

The five specified scalar actions, original additive maps and original additive
comparison equivalences produce all module objects, linear maps and scalar
adjunction mates together. Uniqueness on unit tensors identifies each mate
with any original specified map with its original unit formula.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u w

namespace ModuleCat.TensorRestrictionData

/-- Linearize an original additive equivalence using the specified actions. -/
def linearIso {R : Type u} [CommRing R] (A B : AddCommGrpCat.{max u w})
    (sA : Module R A) (sB : Module R B) (e : A ≃+ B)
    (he : letI := sA; letI := sB; ∀ (a : R) (x : A), e (a • x) = a • e x) :
    letI := sA; letI := sB; ModuleCat.of R A ≅ ModuleCat.of R B := by
  letI := sA
  letI := sB
  exact (show A ≃ₗ[R] B from { __ := e, map_smul' := he }).toModuleIso

/-- The linear comparison retains the original forward additive map. -/
theorem linearIso_hom_apply {R : Type u} [CommRing R] (A B : AddCommGrpCat.{max u w})
    (sA : Module R A) (sB : Module R B) (e : A ≃+ B)
    (he : letI := sA; letI := sB; ∀ (a : R) (x : A), e (a • x) = a • e x) (x : A) :
    (linearIso A B sA sB e he).hom x = e x := rfl

/-- The linear comparison retains the original inverse additive map. -/
theorem linearIso_inv_apply {R : Type u} [CommRing R] (A B : AddCommGrpCat.{max u w})
    (sA : Module R A) (sB : Module R B) (e : A ≃+ B)
    (he : letI := sA; letI := sB; ∀ (a : R) (x : A), e (a • x) = a • e x) (x : B) :
    (linearIso A B sA sB e he).inv x = e.symm x := rfl

/-- Build the original complete scalar comparison before native specialization. -/
def ofAdditive {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    (A A' B B' D : AddCommGrpCat.{max u w})
    (sA : Module R A) (sA' : Module R A')
    (sB : Module S B) (sB' : Module S B') (sD : Module S D)
    (g : A →+ B) (r : A' →+ D)
    (eX : A ≃+ A') (eY : B ≃+ B') (eε : B' ≃+ D)
    (hg : letI := sA; letI := sB; ∀ (a : R) (x : A), g (a • x) = σ a • g x)
    (hr : letI := sA'; letI := sD; ∀ (a : R) (x : A'), r (a • x) = σ a • r x)
    (hX : letI := sA; letI := sA'; ∀ (a : R) (x : A), eX (a • x) = a • eX x)
    (hY : letI := sB; letI := sB'; ∀ (a : S) (x : B), eY (a • x) = a • eY x)
    (hε : letI := sB'; letI := sD; ∀ (a : S) (x : B'), eε (a • x) = a • eε x) :
    TensorRestrictionData.{u, w} σ := by
  letI := sA
  letI := sA'
  letI := sB
  letI := sB'
  letI := sD
  let gp : ModuleCat.of R A ⟶ (restrictScalars σ).obj (ModuleCat.of S B) :=
    ModuleCat.ofHom (X := ModuleCat.of R A)
      (Y := (restrictScalars σ).obj (ModuleCat.of S B)) { __ := g, map_smul' := hg }
  let rp : ModuleCat.of R A' ⟶ (restrictScalars σ).obj (ModuleCat.of S D) :=
    ModuleCat.ofHom (X := ModuleCat.of R A')
      (Y := (restrictScalars σ).obj (ModuleCat.of S D)) { __ := r, map_smul' := hr }
  let adj := extendRestrictScalarsAdj.{max u w, u, u} σ
  let q := (adj.homEquiv _ _).symm gp
  let δ := (adj.homEquiv _ _).symm rp
  have hq : ∀ x, q ((1 : S) ⊗ₜ[R,σ] x) = g x := by
    intro x
    exact congrArg (fun f => f x) ((adj.homEquiv _ _).apply_symm_apply gp)
  have hδ : ∀ x, δ ((1 : S) ⊗ₜ[R,σ] x) = r x := by
    intro x
    exact congrArg (fun f => f x) ((adj.homEquiv _ _).apply_symm_apply rp)
  exact ofMaps.{u, w} σ (ModuleCat.of R A) (ModuleCat.of R A')
    (ModuleCat.of S B) (ModuleCat.of S B') (ModuleCat.of S D) q δ
    (linearIso A A' sA sA' eX hX) (linearIso B B' sB sB' eY hY)
    (linearIso B' D sB' sD eε hε) g r hq hδ

/-- Unit tensors uniquely identify the original upper mate. -/
theorem q_eq_of_unit {R S : Type u} [CommRing R] [CommRing S] {σ : R →+* S}
    (d : TensorRestrictionData.{u, w} σ)
    (q : (extendScalars σ).obj d.A ⟶ d.B)
    (h : ∀ x, q ((1 : S) ⊗ₜ[R,σ] x) = d.g x) : d.q = q := by
  apply ExtendScalars.hom_ext
  intro x
  exact (d.hq x).trans (h x).symm

/-- Unit tensors uniquely identify the original lower mate. -/
theorem δ_eq_of_unit {R S : Type u} [CommRing R] [CommRing S] {σ : R →+* S}
    (d : TensorRestrictionData.{u, w} σ)
    (δ : (extendScalars σ).obj d.A' ⟶ d.D)
    (h : ∀ x, δ ((1 : S) ⊗ₜ[R,σ] x) = d.r x) : d.δ = δ := by
  apply ExtendScalars.hom_ext
  intro x
  exact (d.hδ x).trans (h x).symm

/-- Retain the literal original mates after proving their equalities to the
constructed mates. The objects, actions and all three comparisons are unchanged. -/
def withMates {R S : Type u} [CommRing R] [CommRing S] {σ : R →+* S}
    (d : TensorRestrictionData.{u, w} σ)
    (q : (extendScalars σ).obj d.A ⟶ d.B)
    (δ : (extendScalars σ).obj d.A' ⟶ d.D)
    (hq : d.q = q) (hδ : d.δ = δ) : TensorRestrictionData.{u, w} σ :=
  { d with
    q := q
    δ := δ
    hq := by rw [← hq]; exact d.hq
    hδ := by rw [← hδ]; exact d.hδ }

end ModuleCat.TensorRestrictionData

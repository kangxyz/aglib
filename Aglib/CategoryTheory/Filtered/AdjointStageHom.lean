/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.Presentable.Limits

/-! # Actual adjoint stage Hom descent

The original adjunction units turn equality after the apex left adjoint into
literal equality after a later stage left adjoint. The only continuity input is
eventual equality in the supplied source Hom cocone. For that same cocone,
finite-limit/filtered-colimit interchange extends the Hom universal property
from generators to their finite-colimit closure.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.AdjointStageHom

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Transport a supplied factorization through the original target isomorphisms. -/
theorem factorization_target_iso {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) {A K B : C} {S M N : D}
    (s : S ⟶ L.obj A) (β : A ⟶ K) (e : K ≅ B)
    (T : N ≅ L.obj B) (E : M ≅ N) (ι : L.obj K ⟶ M)
    (γ : S ⟶ N) (δ : L.obj K ⟶ N)
    (hi : ι ≫ E.hom = δ) (ht : L.map e.hom ≫ T.inv = δ)
    (hβ : (s ≫ L.map β) ≫ ι = γ ≫ E.inv) :
    s ≫ L.map (β ≫ e.hom) = γ ≫ T.hom := by
  apply (cancel_mono T.inv).mp
  calc
    _ = s ≫ L.map β ≫ (L.map e.hom ≫ T.inv) := by
      rw [L.map_comp]
      simp only [Category.assoc]
    _ = s ≫ L.map β ≫ δ := congrArg (fun k => s ≫ L.map β ≫ k) ht
    _ = ((s ≫ L.map β) ≫ ι) ≫ E.hom := by
      rw [← hi]
      simp only [Category.assoc]
    _ = (γ ≫ E.inv) ≫ E.hom := congrArg (fun k => k ≫ E.hom) hβ
    _ = γ := by rw [Category.assoc, E.inv_hom_id, Category.comp_id]
    _ = (γ ≫ T.hom) ≫ T.inv := by
      rw [Category.assoc, T.hom_inv_id, Category.comp_id]

/-- Original unit comparisons turn source-Hom eventual equality into equality of
the actual stage images of the original two maps. -/
theorem eventually_equal_of_units
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    {Stages : J → Type*} [∀ j, Category* (Stages j)]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (Ls : ∀ j, C ⥤ Stages j) (Rs : ∀ j, Stages j ⥤ C)
    (adjs : ∀ j, Ls j ⊣ Rs j) (T : J ⥤ C) (c : Cocone T) {A B : C}
    (s : ∀ j, B ⟶ T.obj j)
    (hs : ∀ {j k : J} (t : j ⟶ k), s j ≫ T.map t = s k)
    (E : c.pt ≅ R.obj (L.obj B))
    (hE : ∀ j, s j ≫ c.ι.app j ≫ E.hom = adj.unit.app B)
    (v : ∀ j, T.obj j ⟶ (Rs j).obj ((Ls j).obj B))
    (hv : ∀ j, s j ≫ v j = (adjs j).unit.app B)
    (heq : ∀ j (f g : A ⟶ T.obj j), f ≫ c.ι.app j = g ≫ c.ι.app j →
      ∃ (k : J) (t : j ⟶ k), f ≫ T.map t = g ≫ T.map t)
    (j₀ : J) (f g : A ⟶ B) (h : L.map f = L.map g) :
    ∃ j, (Ls j).map f = (Ls j).map g := by
  have hunit : f ≫ adj.unit.app B = g ≫ adj.unit.app B := by
    calc
      _ = adj.homEquiv _ _ (L.map f ≫ 𝟙 _) := by
        rw [adj.homEquiv_naturality_left, adj.homEquiv_id]
      _ = adj.homEquiv _ _ (L.map g ≫ 𝟙 _) := by rw [h]
      _ = _ := by rw [adj.homEquiv_naturality_left, adj.homEquiv_id]
  have hpoint : (f ≫ s j₀) ≫ c.ι.app j₀ = (g ≫ s j₀) ≫ c.ι.app j₀ := by
    apply (cancel_mono E.hom).mp
    simpa only [Category.assoc, hE] using hunit
  obtain ⟨j, t, ht⟩ := heq j₀ (f ≫ s j₀) (g ≫ s j₀) hpoint
  have hreps : f ≫ s j = g ≫ s j := by
    simpa only [Category.assoc, hs] using ht
  have hstage : f ≫ (adjs j).unit.app B = g ≫ (adjs j).unit.app B := by
    simpa only [Category.assoc, hv] using congrArg (fun k => k ≫ v j) hreps
  refine ⟨j, ((adjs j).homEquiv _ _).injective ?_⟩
  calc
    _ = f ≫ (adjs j).unit.app B := by
      simpa only [Category.comp_id, Adjunction.homEquiv_id] using
        (adjs j).homEquiv_naturality_left f (𝟙 _)
    _ = g ≫ (adjs j).unit.app B := hstage
    _ = _ := by
      simpa only [Category.comp_id, Adjunction.homEquiv_id] using
        ((adjs j).homEquiv_naturality_left g (𝟙 _)).symm

universe w uC vC

/-- The original fixed-cocone Hom universal property extends from the supplied
generators to their finite-colimit closure, using native finite-limit interchange. -/
def homCoconeIsColimit_of_finiteColimitClosure
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {C : Type uC} [Category.{vC} C] (P : ObjectProperty C)
    {D : J ⥤ C} (c : Cocone D)
    (hgen : ∀ A, P A → IsColimit ((coyoneda.obj (op A)).mapCocone c))
    (A : C) (hA : P.colimitsCardinalClosure Cardinal.aleph0.{vC} A) :
    IsColimit ((coyoneda.obj (op A)).mapCocone c) := by
  let Q : ObjectProperty (C) :=
    fun A => Nonempty (IsColimit ((coyoneda.obj (op A)).mapCocone c))
  have : Q.IsClosedUnderIsomorphisms := {
    of_iso := by
      intro A B e hA
      obtain ⟨hc⟩ := hA
      exact ⟨IsColimit.mapCoconeEquiv (coyoneda.mapIso e.op).symm hc⟩ }
  have hgenerators : P ≤ Q := by
    intro A hA
    exact ⟨hgen A hA⟩
  have hclosure : P.colimitsCardinalClosure Cardinal.aleph0.{vC} ≤ Q := by
    apply (P).colimitsCardinalClosure_le
      Cardinal.aleph0.{vC} ?_ hgenerators
    intro K _ hK
    have hfinite : Finite (Arrow K) := by
      simpa only [hasCardinalLT_aleph0_iff] using hK
    have hKop : HasCardinalLT (Arrow Kᵒᵖ) Cardinal.aleph0.{w} := by
      rw [hasCardinalLT_arrow_op_iff, hasCardinalLT_aleph0_iff]
      exact hfinite
    refine { colimitsOfShape_le := ?_ }
    rintro A ⟨p⟩
    let cA : Cocone p.diag := Cocone.mk A p.ι
    have hcA : IsColimit cA := p.isColimit
    let t := coyoneda.mapCone cA.op
    have ht : IsLimit t := isLimitOfPreserves coyoneda hcA.op
    let : IsCardinalFiltered J Cardinal.aleph0.{w} :=
      (isCardinalFiltered_aleph0_iff J).2 inferInstance
    refine ⟨Functor.Accessible.Limits.isColimitMapCocone t
      (fun B => isLimitOfPreserves
        ((CategoryTheory.evaluation (C)
          (Type vC)).obj B) ht)
      Cardinal.aleph0.{w} hKop c ?_⟩
    intro k
    exact Classical.choice (p.prop_diag_obj k.unop)
  exact Classical.choice (hclosure A hA)

end CategoryTheory.AdjointStageHom

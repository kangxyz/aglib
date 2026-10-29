/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ShortComplex.Adjunction.ExactLeftCycles
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Actual cycle sections through an exact left adjoint

An actual abelian-group cocycle gives a section of the target cycles through
the original adjunction unit and native exact cycle comparisons. Its term
and homology projection retain the supplied maps and native source homology
isomorphism. The source complex is the same native underlying complex `T.map U`.
No resolution, Ext object or target existence hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁ w

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u₁} [Category.{v₁} D] [Abelian D]
  {L : C ⥤ D} {U : D ⥤ C} [L.Additive] [L.PreservesHomology] [U.Additive]
  (adj : L ⊣ U) (E : C ⥤ AddCommGrpCat.{w}) [E.Additive] [E.PreservesHomology]
  (T : ShortComplex D)

/-- Construct the actual target cycle section from an ordinary cocycle and
its canonical homology value. The inclusion uses the supplied term-unit
cancellation; the projection uses the supplied canonical cycle/projection
square and cancels the actual source homology isomorphism. -/
theorem exists_cycleSection (δ : (T.map U).map L ⟶ T) {H : C} (e : H ≅ (T.map U).homology)
    (c : H ⟶ U.obj T.homology)
    (hu : adj.unit.app (T.map U).X₂ ≫ U.map δ.τ₂ = 𝟙 _)
    (hπ : (T.map U).homologyπ ≫ e.inv ≫ c =
      adj.unit.app (T.map U).cycles ≫
        U.map (((T.map U).mapCyclesIso L).inv ≫ ShortComplex.cyclesMap δ ≫ T.homologyπ))
    (x : E.obj H) (s : E.obj (T.map U).X₂) (hs : E.map (T.map U).g s = 0)
    (hx : E.map e.hom x = ((T.map U).mapHomologyIso E).hom
      (((T.map U).map E).homologyπ (((T.map U).map E).abCyclesIso.inv ⟨s, hs⟩))) :
    ∃ z : E.obj (U.obj T.cycles),
      E.map (U.map T.iCycles) z = s ∧
        E.map c x = E.map (U.map T.homologyπ) z := by
  let z₀ := ((T.map U).map E).abCyclesIso.inv ⟨s, hs⟩
  let zK := ((T.map U).mapCyclesIso E).hom z₀
  let τ := adj.unit.app (T.map U).cycles ≫
    U.map (((T.map U).mapCyclesIso L).inv ≫ ShortComplex.cyclesMap δ)
  have hi : τ ≫ U.map T.iCycles = (T.map U).iCycles := by
    have h := adj.cycles_unit_exact_left_iCycles (T.map U) δ
    rw [hu] at h
    simpa only [τ, Functor.id_obj, Category.comp_id, Category.assoc] using h
  have hzK : E.map (T.map U).iCycles zK = s := by
    have h := ConcreteCategory.congr_hom ((T.map U).mapCyclesIso_hom_iCycles E) z₀
    exact h.trans (((T.map U).map E).abCyclesIso_inv_apply_iCycles _)
  have hx₀ : E.map e.hom x = E.map (T.map U).homologyπ zK := by
    rw [hx]
    exact ConcreteCategory.congr_hom
      (ShortComplex.homologyπ_mapHomologyIso_hom E (T.map U)) z₀
  have hx' : E.map e.inv (E.map (T.map U).homologyπ zK) = x := by
    rw [← hx₀]
    exact ConcreteCategory.congr_hom (E.mapIso e).hom_inv_id x
  have hp : (T.map U).homologyπ ≫ e.inv ≫ c = τ ≫ U.map T.homologyπ := by
    simpa only [τ, U.map_comp, Category.assoc] using hπ
  refine ⟨E.map τ zK, ?_, ?_⟩
  · have h := ConcreteCategory.congr_hom (congrArg (fun k => E.map k) hi) zK
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h
    exact h.trans hzK
  · have h := ConcreteCategory.congr_hom (congrArg (fun k => E.map k) hp) zK
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h
    rw [hx'] at h
    exact h

end CategoryTheory.Adjunction

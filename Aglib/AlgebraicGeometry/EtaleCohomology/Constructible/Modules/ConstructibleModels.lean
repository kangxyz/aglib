/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteChartGenerators

/-! # Actual constructible native module objects and arrows at one original stage

Constructibility produces native finite-stage membership internally. Finite
chart descent then models each original object; the existing finite-diagram
engine descends every arrow and its equations at one common original stage.
The stage objects are constructible by the original generator stratification,
not by an assumed coefficient-model certificate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
namespace ModelDescent

universe u v

open Constructible.Modules Constructible.Modules.NativeFreePresentation

variable (R : Type (u + 1)) [Ring R] [IsNoetherianRing R]

private theorem constructible_of_nativeStage
    {X : Scheme.{u}} [X.IsSeparated] (F : Coefficient R X)
    (hF : finiteColimitStages R X F) : Constructible.Modules.IsConstructible F := by
  exact finiteColimitStage_isConstructible R F hF

/-- An original constructible native module object descends to a constructible
object at an actual stage above any specified stage, with the original
native module inverse-image comparison. -/
theorem exists_constructible_object_model
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    [∀ i, (D.obj i).IsSeparated]
    (c : Cone D) (hc : IsLimit c) [CompactSpace c.pt] [c.pt.IsSeparated]
    (i₀ : I) [CompactSpace (D.obj i₀)]
    (F : Coefficient R c.pt) (hF : Constructible.Modules.IsConstructible F) :
    ∃ (i : I) (_ : i ⟶ i₀) (M : Coefficient R (D.obj i)),
      Constructible.Modules.IsConstructible M ∧
        Nonempty ((inverseImage R (c.π.app i)).obj M ≅ F) := by
  obtain ⟨i, q, M, hM, e⟩ :=
    constructible_hasStageModel_of_compactStage R D c hc i₀ F hF (op i₀)
  let : (D.op.obj i).unop.IsSeparated :=
    inferInstanceAs (D.obj i.unop).IsSeparated
  exact ⟨i.unop, q.unop, M, constructible_of_nativeStage R M hM, e⟩

/-- A finite diagram of actual constructible native module coefficients descends
with all of its original arrows, identities, and compositions to one stage.
The natural comparison is the original structural inverse image. -/
theorem exists_constructible_finiteDiagram_model
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    [∀ i, (D.obj i).IsSeparated]
    (c : Cone D) (hc : IsLimit c) [CompactSpace c.pt] [c.pt.IsSeparated]
    (i₀ : I) [CompactSpace (D.obj i₀)]
    {J : Type v} [SmallCategory J] [FinCategory J]
    (L : J ⥤ Coefficient R c.pt)
    (hL : ∀ j, Constructible.Modules.IsConstructible (L.obj j)) :
    ∃ (i : I) (_ : i ⟶ i₀) (M : J ⥤ Coefficient R (D.obj i)),
      (∀ j, Constructible.Modules.IsConstructible (M.obj j)) ∧
        Nonempty (M ⋙ inverseImage R (c.π.app i) ≅ L) := by
  have {k l : Iᵒᵖ} (q : k ⟶ l) : IsAffineHom (D.op.map q).unop :=
    inferInstanceAs (IsAffineHom (D.map q.unop))
  obtain ⟨i, q, M, hM, e⟩ := exists_finiteDiagram_model D.op c.op R hc.op (op i₀) L
    (fun j => constructible_hasStageModel_of_compactStage R D c hc i₀ (L.obj j) (hL j))
  let : (D.op.obj i).unop.IsSeparated :=
    inferInstanceAs (D.obj i.unop).IsSeparated
  exact ⟨i.unop, q.unop, M, fun j => constructible_of_nativeStage R (M.obj j) (hM j), e⟩

end ModelDescent
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

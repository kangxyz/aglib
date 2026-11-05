/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.HomAbove
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.StageBaseChange
public import Aglib.CategoryTheory.Filtered.FiniteDiagramDescent

/-! # Actual finite native coefficient diagrams over one model stage

Object models are placed at one common stage. Original Hom continuity then
descends the actual finite arrows; its eventual-equality statement descends
the actual functor equations. The resulting finite functor retains a native
natural isomorphism after the original structural inverse image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
namespace ModelDescent

universe u v

open Constructible.Modules.NativeFreePresentation

variable {I : Type u} [SmallCategory I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (R : Type (u + 1)) [Ring R]

/-- An actual canonical coefficient model exists above every specified stage.
The witness includes its original structural inverse-image isomorphism. -/
def HasStageModel : ObjectProperty (Coefficient R c.pt.unop) :=
  FiniteDiagramDescent.HasStageModel
    (fun i : I => inverseImage R (c.ι.app i).unop)
    (fun i => finiteColimitStages R (X.obj i).unop)

variable [IsFiltered I]
  [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop] (hc : IsColimit c)

include hc in
/-- Actual object models and original native Hom continuity descend the
whole supplied finite diagram, including all arrows and functor equations. -/
theorem exists_finiteDiagram_model {J : Type v} [SmallCategory J] [FinCategory J]
    (i₀ : I) (L : J ⥤ Coefficient R c.pt.unop)
    (hL : ∀ x, HasStageModel X c R (L.obj x)) :
    ∃ (i : I) (_ : i₀ ⟶ i) (Lᵢ : J ⥤ Coefficient R (X.obj i).unop),
      (∀ x, finiteColimitStages R (X.obj i).unop (Lᵢ.obj x)) ∧
      Nonempty (Lᵢ ⋙ inverseImage R (c.ι.app i).unop ≅ L) := by
  exact (@FiniteDiagramDescent.exists_finiteDiagram_model
    I inferInstance
    (fun i : I => Coefficient R (X.obj i).unop)
    (fun i => inferInstanceAs
      (Category.{u + 1} (Coefficient R (X.obj i).unop)))
    (Coefficient R c.pt.unop)
    (inferInstanceAs (Category.{u + 1} (Coefficient R c.pt.unop))))
    (fun {_ _} q => inverseImage R (X.map q).unop)
    (fun i : I => inverseImage R (c.ι.app i).unop)
    (fun {_ _} q => coneCompIso X c _ R q)
    (fun i => finiteColimitStages R (X.obj i).unop)
    (fun {_ _} q A hA => finiteColimitStage_inverseImage R (X.map q).unop A hA)
    (fun i A hA B γ => exists_nativeHom_above X c i R hc A hA B γ)
    (fun i A hA B f g h => nativeHom_eventually_equal_above X c i R hc A hA B f g h)
    i₀ L hL

end ModelDescent
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

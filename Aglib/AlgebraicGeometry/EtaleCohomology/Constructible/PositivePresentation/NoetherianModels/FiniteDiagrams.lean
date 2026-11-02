/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.HomAbove
public import Aglib.CategoryTheory.Filtered.FiniteDiagramDescent

/-! # Actual finite bounded coefficient diagrams over one model stage

Object models are placed at one common stage. Original Hom continuity then
descends the actual finite arrows; its eventual-equality statement descends
the actual functor equations. The resulting finite functor retains a native
natural isomorphism after the original structural inverse image.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u v

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

variable {I : Type u} [SmallCategory I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (n : ℕ)

/-- An actual canonical coefficient model exists above every specified stage.
The witness includes its original structural inverse-image isomorphism. -/
def HasStageModel : ObjectProperty (BoundedPresentation.Coefficient c.pt.unop n) :=
  FiniteDiagramDescent.HasStageModel
    (fun i : I => boundedInverseImage (c.ι.app i).unop n)
    (fun i => BoundedPresentation.finiteColimitStages (X.obj i).unop n)

variable [IsFiltered I]
  [∀ {i j} (q : i ⟶ j), IsAffineHom (X.map q).unop] (hc : IsColimit c)

include hc in
/-- Actual object models and original bounded Hom continuity descend the
whole supplied finite diagram, including all arrows and functor equations. -/
theorem exists_finiteDiagram_model {J : Type v} [SmallCategory J] [FinCategory J]
    (i₀ : I) (L : J ⥤ BoundedPresentation.Coefficient c.pt.unop n)
    (hL : ∀ x, HasStageModel X c n (L.obj x)) :
    ∃ (i : I) (_ : i₀ ⟶ i) (Lᵢ : J ⥤ BoundedPresentation.Coefficient (X.obj i).unop n),
      (∀ x, BoundedPresentation.finiteColimitStages (X.obj i).unop n (Lᵢ.obj x)) ∧
      Nonempty (Lᵢ ⋙ boundedInverseImage (c.ι.app i).unop n ≅ L) := by
  exact (@FiniteDiagramDescent.exists_finiteDiagram_model
    I inferInstance
    (fun i : I => BoundedPresentation.Coefficient (X.obj i).unop n)
    (fun i => inferInstanceAs
      (Category.{u + 1} (BoundedPresentation.Coefficient (X.obj i).unop n)))
    (BoundedPresentation.Coefficient c.pt.unop n)
    (inferInstanceAs (Category.{u + 1} (BoundedPresentation.Coefficient c.pt.unop n))))
    (fun {_ _} q => boundedInverseImage (X.map q).unop n)
    (fun i : I => boundedInverseImage (c.ι.app i).unop n)
    (fun {_ _} q => boundedConeCompIso X c n q)
    (fun i => BoundedPresentation.finiteColimitStages (X.obj i).unop n)
    (fun {_ _} q A hA => finiteColimitStage_inverseImage (X.map q).unop n A hA)
    (fun i A hA B γ => exists_boundedHom_above X c i hc n A hA B γ)
    (fun i A hA B f g h => boundedHom_eventually_equal_above X c i hc n A hA B f g h)
    i₀ L hL

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

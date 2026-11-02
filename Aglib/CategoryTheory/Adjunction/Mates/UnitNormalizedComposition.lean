/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.RepresentedCoherence
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition of the original unit-normalized left-adjoint comparisons

All six adjunctions are the supplied adjunctions. The composite comparison keeps
its actual conjugate right comparison, and the second comparison is normalized
by the whole unit equation before any component is evaluated.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

universe uA vA uB vB uC vC

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C]
  {L₁ M₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ M₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₀ M₀ : A ⥤ C} {R₀ : C ⥤ A}

/-- The complete comparison pasting follows from the actual conjugate comparison
and the whole unit normalization of the second pair of adjunctions. -/
theorem leftAdjointUniq_comp_of_unit
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₀ : L₀ ⊣ R₀)
    (b₁ : M₁ ⊣ R₁) (b₂ : M₂ ⊣ R₂) (b₀ : M₀ ⊣ R₀)
    (c : L₀ ⟶ L₁ ⋙ L₂) (d : R₂ ⋙ R₁ ⟶ R₀) (e : M₀ ⟶ M₁ ⋙ M₂)
    (hc : conjugateEquiv (a₁.comp a₂) a₀ c = d)
    (hb : (b₁.comp b₂).unit ≫ Functor.whiskerLeft (M₁ ⋙ M₂) d =
      b₀.unit ≫ Functor.whiskerRight e R₀) :
    c ≫ Functor.whiskerRight (a₁.leftAdjointUniq b₁).hom L₂ ≫
        Functor.whiskerLeft M₁ (a₂.leftAdjointUniq b₂).hom =
      (a₀.leftAdjointUniq b₀).hom ≫ e := by
  apply NatTrans.ext
  funext X
  apply (a₀.homEquiv X ((M₁ ⋙ M₂).obj X)).injective
  have hleft := RepresentedCoherence.homEquiv_comp a₁ a₂ a₀ c d hc
    X (M₁.obj X) ((M₁ ⋙ M₂).obj X)
    ((a₁.leftAdjointUniq b₁).hom.app X)
    ((a₂.leftAdjointUniq b₂).hom.app (M₁.obj X))
  simp only [Functor.comp_obj] at hleft
  rw [homEquiv_leftAdjointUniq_hom_app a₁ b₁ X,
    homEquiv_leftAdjointUniq_hom_app a₂ b₂ (M₁.obj X)] at hleft
  have hunit := congrArg (fun η => η.app X) hb
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Adjunction.comp_unit_app, Category.assoc] at hunit
  change a₀.homEquiv X _ (c.app X ≫
      L₂.map ((a₁.leftAdjointUniq b₁).hom.app X) ≫
        (a₂.leftAdjointUniq b₂).hom.app (M₁.obj X)) =
    a₀.homEquiv X _ ((a₀.leftAdjointUniq b₀).hom.app X ≫ e.app X)
  calc
    _ = b₁.unit.app X ≫ R₁.map (b₂.unit.app (M₁.obj X)) ≫
        d.app ((M₁ ⋙ M₂).obj X) := hleft
    _ = b₀.unit.app X ≫ R₀.map (e.app X) := hunit
    _ = _ := by rw [a₀.homEquiv_naturality_right, homEquiv_leftAdjointUniq_hom_app]

/-- Evaluation happens only after the complete original comparison has been pasted. -/
theorem unitNormalizedComparison_comp_app
    (c : L₀ ⟶ L₁ ⋙ L₂) (a₁ : L₁ ⟶ M₁) (a₂ : L₂ ⟶ M₂)
    (a₀ : L₀ ⟶ M₀) (e : M₀ ⟶ M₁ ⋙ M₂)
    (h : c ≫ Functor.whiskerRight a₁ L₂ ≫ Functor.whiskerLeft M₁ a₂ = a₀ ≫ e)
    (X : A) :
    c.app X ≫ L₂.map (a₁.app X) ≫ a₂.app (M₁.obj X) =
      a₀.app X ≫ e.app X := by
  have h := congrArg (fun η => η.app X)
    h
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] using h

end CategoryTheory.Adjunction

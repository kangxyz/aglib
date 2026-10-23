/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.AllModuleCoefficients

/-! # Composition and surjective descent for actual bounded coefficients

The hypotheses concern the actual canonical exchange on all original
coefficients killed by the specified modulus. Genuine injective module tests,
the constructed coefficient retract and finite degree induction prove the
same exchange on the composite or on the descended morphism. The statements
are pointwise in the six independent derived-category universes; they do not
assert base-change stability for a weaker property involving only descending
coefficients.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

section TypedCoefficients

variable {A B C M : Type*} [Category* A] [Category* B] [Category* C] [Category* M]
  {L R : B ⥤ C}

private theorem injectiveTests_of_originalCoefficients
    (single : A ⥤ B) (U : M ⥤ A) (Z : M ⥤ B) (e : Z = U ⋙ single)
    (β : L ⟶ R) (P : A → Prop)
    (h : ∀ F : A, P F → IsIso (β.app (single.obj F)))
    (hU : ∀ (I : M) [Injective I], P (U.obj I)) :
    ∀ (I : M) [Injective I], IsIso (β.app (Z.obj I)) := by
  subst Z
  intro I _
  exact h (U.obj I) (hU I)

end TypedCoefficients

universe u dS dX dY dS' dX' dY'

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

variable {S X Y S' X' Y' : Scheme.{u}}
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dY'} (AbelianSheaf.{u, u + 1} Y')]
  (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
  (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
  (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
  (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f)) (n : ℕ)

/-- Canonical derived exchange for adjacent morphisms on all n-killed original
coefficients implies the canonical composite exchange on every such coefficient. -/
theorem derivedExchange_comp_on_killedCoefficients
    (hOuter : ∀ (F : AbelianSheaf.{u, u + 1} X), n • 𝟙 F = 0 →
      IsIso ((derivedBaseChangeMap f f' g g' h₁).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)))
    (hInner : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      IsIso ((derivedBaseChangeMap k k' g' g'' h₂).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
    (F : AbelianSheaf.{u, u + 1} Y) (hF : n • 𝟙 F = 0) :
    IsIso ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)) := by
  have hOuterI := injectiveTests_of_originalCoefficients
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
    (zmodUnderlying X n) (zmodSingle X n) rfl
    (derivedBaseChangeMap f f' g g' h₁) (fun G => n • 𝟙 G = 0) hOuter
    (fun I _ => zmodUnderlying_nsmul_id X n I)
  have hInnerI := injectiveTests_of_originalCoefficients
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0)
    (zmodUnderlying Y n) (zmodSingle Y n) rfl
    (derivedBaseChangeMap k k' g' g'' h₂) (fun G => n • 𝟙 G = 0) hInner
    (fun I _ => zmodUnderlying_nsmul_id Y n I)
  apply derivedExchange_on_killedCoefficients (k ≫ f) (k' ≫ f') g g'' h n ?_ F hF
  intro I _
  exact derivedExchange_on_zmodInjectives_comp f k f' k' g g' g'' h₁ h₂ h n
    hOuterI hInnerI I

/-- The same adjacent hypotheses imply every original higher-image exchange
component on every original coefficient killed by the specified modulus. -/
theorem higherExchange_comp_on_killedCoefficients
    (hOuter : ∀ (F : AbelianSheaf.{u, u + 1} X), n • 𝟙 F = 0 →
      IsIso ((derivedBaseChangeMap f f' g g' h₁).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)))
    (hInner : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      IsIso ((derivedBaseChangeMap k k' g' g'' h₂).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
    (F : AbelianSheaf.{u, u + 1} Y) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h q).app F) := by
  have := derivedExchange_comp_on_killedCoefficients f k f' k' g g' g'' h₁ h₂ h n
    hOuter hInner F hF
  exact higherBaseChangeMap_isIso_app_of_derived (k ≫ f) (k' ≫ f') g g'' h F q

/-- Source and composite canonical exchange on all original n-killed
coefficients descend along the actual surjection. Properness and cartesianness
are inputs to the applications supplying those two exchange hypotheses. -/
theorem derivedExchange_descent_on_killedCoefficients [Surjective k]
    (hInner : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      IsIso ((derivedBaseChangeMap k k' g' g'' h₂).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
    (hComposite : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      IsIso ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    IsIso ((derivedBaseChangeMap f f' g g' h₁).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) := by
  have hInnerI := injectiveTests_of_originalCoefficients
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0)
    (zmodUnderlying Y n) (zmodSingle Y n) rfl
    (derivedBaseChangeMap k k' g' g'' h₂) (fun G => n • 𝟙 G = 0) hInner
    (fun I _ => zmodUnderlying_nsmul_id Y n I)
  have hCompositeI := injectiveTests_of_originalCoefficients
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0)
    (zmodUnderlying Y n) (zmodSingle Y n) rfl
    (derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h) (fun G => n • 𝟙 G = 0) hComposite
    (fun I _ => zmodUnderlying_nsmul_id Y n I)
  apply derivedExchange_on_killedCoefficients f f' g g' h₁ n ?_ F hF
  intro I _
  exact derivedExchange_on_zmodInjectives_descent f k f' k' g g' g'' h₁ h₂ h n
    hInnerI hCompositeI I

/-- Surjective descent preserves the actual original exchange in every
natural degree, for every actual coefficient killed by the specified modulus. -/
theorem higherExchange_descent_on_killedCoefficients [Surjective k]
    (hInner : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      IsIso ((derivedBaseChangeMap k k' g' g'' h₂).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
    (hComposite : ∀ (F : AbelianSheaf.{u, u + 1} Y), n • 𝟙 F = 0 →
      IsIso ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' h₁ q).app F) := by
  have := derivedExchange_descent_on_killedCoefficients f k f' k' g g' g'' h₁ h₂ h n
    hInner hComposite F hF
  exact higherBaseChangeMap_isIso_app_of_derived f f' g g' h₁ F q

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

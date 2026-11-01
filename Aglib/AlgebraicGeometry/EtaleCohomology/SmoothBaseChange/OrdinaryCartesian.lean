/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Ordinary
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackIsomorphism
public import Aglib.CategoryTheory.Adjunction.Mates.Equivalences

/-! # Bounded ordinary smooth exchange for a specified Cartesian square

The original pullback-corner isomorphism and the original horizontal mate
identity transport the literal-pullback result. Neither the coefficient nor
the exchange transformation is replaced. This is an ordinary, degree-zero
statement, not higher smooth base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

private theorem iso_of_horizontal_comparison
    {C : Type*} [Category C] {A B D E F : C}
    (l : A ⟶ B) (a : B ⟶ D) (b : D ⟶ F) (c : A ⟶ E) (r : E ⟶ F)
    [IsIso l] [IsIso a] [IsIso b] [IsIso r]
    (h : l ≫ a ≫ b = c ≫ r) : IsIso c := by
  have : IsIso (c ≫ r) := by rw [← h]; infer_instance
  exact IsIso.of_isIso_comp_right c r

private theorem property_of_arrow_equalities
    {A B : Sort*} {Q : A → B → Prop} (P : ∀ a b, Q a b → Prop)
    {a a' : A} {b b' : B} (h : Q a b) (h' : Q a' b')
    (ha : a = a') (hb : b = b') (hp : P a b h) : P a' b' h' := by
  subst a'
  subst b'
  exact hp

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Horizontal scheme isomorphisms make the unchanged ordinary mate invertible. -/
theorem baseChangeMap_isIso_of_horizontal_isIso
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : f' ≫ g = g' ≫ f)
    [IsIso g] [IsIso g'] : IsIso (baseChangeMap f f' g g' h) := by
  rw [baseChangeMap_eq_nativeMate]
  exact mateEquiv_isIso_of_equivalences (inverseImageAdjunction f)
    (inverseImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)

/-- Original horizontal pasting at the original coefficient, without any section functor. -/
theorem baseChangeMap_isIso_app_hComp
    {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
    (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (k₁ : X₁ ⟶ X₀) (k₂ : X₂ ⟶ X₁)
    (e₁ : f₁ ≫ g₁ = k₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = k₂ ≫ f₁)
    (e : f₂ ≫ (g₂ ≫ g₁) = (k₂ ≫ k₁) ≫ f₀)
    (F : AbelianSheaf.{u, u + 1} X₀)
    [IsIso ((baseChangeMap f₀ f₁ g₁ k₁ e₁).app F)]
    [IsIso ((baseChangeMap f₁ f₂ g₂ k₂ e₂).app ((inverseImage k₁).obj F))] :
    IsIso ((baseChangeMap f₀ f₂ (g₂ ≫ g₁) (k₂ ≫ k₁) e).app F) :=
  iso_of_horizontal_comparison
    ((inverseImageComp g₁ g₂).hom.app ((directImage f₀).obj F))
    ((inverseImage g₂).map ((baseChangeMap f₀ f₁ g₁ k₁ e₁).app F))
    ((baseChangeMap f₁ f₂ g₂ k₂ e₂).app ((inverseImage k₁).obj F))
    ((baseChangeMap f₀ f₂ (g₂ ≫ g₁) (k₂ ≫ k₁) e).app F)
    ((directImage f₂).map ((inverseImageComp k₁ k₂).hom.app F))
    (baseChangeMap_hComp f₀ f₁ f₂ g₁ g₂ k₁ k₂ e₁ e₂ e F)

/-- Bounded ordinary smooth exchange for the original specified Cartesian square. -/
theorem baseChangeMap_smooth_bounded_isIso_of_isPullback
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : IsPullback g' f' f g) [Smooth g]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    IsIso ((baseChangeMap f f' g g' h.w.symm).app F) := by
  let e : X' ≅ pullback g f := h.flip.isoPullback
  have he₁ : e.hom ≫ pullback.fst g f = f' := h.flip.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd g f = g' := h.flip.isoPullback_hom_snd
  have h₂ : f' ≫ 𝟙 S' = e.hom ≫ pullback.fst g f := by simpa using he₁.symm
  have hc : f' ≫ (𝟙 S' ≫ g) = (e.hom ≫ pullback.snd g f) ≫ f := by
    simpa only [Category.id_comp, he₂] using h.w.symm
  let : IsIso ((baseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition).app F) := SmoothBaseChange.baseChangeMap_smooth_bounded_isIso
        f g F n hn hF
  let : IsIso (baseChangeMap (pullback.fst g f) f' (𝟙 S') e.hom h₂) :=
    baseChangeMap_isIso_of_horizontal_isIso _ _ _ _ h₂
  have hp := baseChangeMap_isIso_app_hComp f (pullback.fst g f) f' g (𝟙 S')
    (pullback.snd g f) e.hom pullback.condition h₂ hc F
  exact property_of_arrow_equalities
    (fun g g' h => IsIso ((baseChangeMap f f' g g' h).app F)) hc h.w.symm
    (Category.id_comp g) he₂ hp

end AlgebraicGeometry.Scheme.EtaleCohomology

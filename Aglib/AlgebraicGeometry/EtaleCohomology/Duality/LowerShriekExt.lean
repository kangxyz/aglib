/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Extension by zero on Ext groups of constant-ring module sheaves

Let `j : U ⟶ X` be an étale morphism of schemes, for example an open immersion, and `Λ` a ring.
Extension by zero `j_! = moduleLowerShriek j Λ` of sheaves of modules over the constant ring
sheaves is exact, so it induces `Ext^q(A, B) → Ext^q(j_! A, j_! B)`, Mathlib's
`Functor.mapExtAddHom`. It is compatible with Yoneda composition, with `Ext.mk₀` and with the
extension class of a short exact sequence (Mathlib `Ext.mapExactFunctor_comp`,
`mapExactFunctor_mk₀`, `mapExactFunctor_extClass`).

The adjunction `j_! ⊣ j^*` of `moduleLowerShriekAdjunction`, with the exact native inverse image
`j^* = moduleInverseImage j Λ`, induces `Ext^q(j_! A, B) ≃+ Ext^q(A, j^* B)`, Mathlib's
`Adjunction.extEquiv`; it is compatible with Yoneda composition on both sides
(`Adjunction.extEquiv_naturality_left` and `_right`). This leaf records these maps and
equations for the actual étale functors; their exactness instances are those of
`Exceptional/Open/ModuleAdjunction` and `Exceptional/Coefficients/Exactness`. No condition on
`Λ` is used; `HasExt` is a size hypothesis, and the Ext universes on `U` and `X` are
independent.
-/

@[expose] public noncomputable section

universe w w' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (Λ : Type (u + 1)) [Ring Λ]
  [HasExt.{w} (ModuleSheaf U Λ)] [HasExt.{w'} (ModuleSheaf X Λ)]

/-- Extension by zero on Ext groups: the Ext map of the exact functor `j_!`. -/
abbrev moduleLowerShriekExt (A B : ModuleSheaf U Λ) (q : ℕ) :
    Ext.{w} A B q →+
      Ext.{w'} ((moduleLowerShriek j Λ).obj A) ((moduleLowerShriek j Λ).obj B) q :=
  (moduleLowerShriek j Λ).mapExtAddHom A B q

theorem moduleLowerShriekExt_apply {A B : ModuleSheaf U Λ} {q : ℕ} (e : Ext.{w} A B q) :
    moduleLowerShriekExt j Λ A B q e = e.mapExactFunctor (moduleLowerShriek j Λ) :=
  rfl

/-- Extension by zero on Ext groups preserves Yoneda composition. -/
theorem moduleLowerShriekExt_comp {A B C : ModuleSheaf U Λ} {a b c : ℕ}
    (α : Ext.{w} A B a) (β : Ext.{w} B C b) (h : a + b = c) :
    moduleLowerShriekExt j Λ A C c (α.comp β h) =
      (moduleLowerShriekExt j Λ A B a α).comp
        (moduleLowerShriekExt j Λ B C b β) h :=
  Ext.mapExactFunctor_comp _ α β h

/-- Extension by zero on degree-zero Ext groups is extension by zero of morphisms. -/
theorem moduleLowerShriekExt_mk₀ {A B : ModuleSheaf U Λ} (f : A ⟶ B) :
    moduleLowerShriekExt j Λ A B 0 (Ext.mk₀ f) =
      Ext.mk₀ ((moduleLowerShriek j Λ).map f) :=
  Ext.mapExactFunctor_mk₀ _ f

/-- Extension by zero sends the extension class of a short exact sequence to the extension
class of its extension by zero. -/
theorem moduleLowerShriekExt_extClass {S : ShortComplex (ModuleSheaf U Λ)}
    (hS : S.ShortExact) :
    moduleLowerShriekExt j Λ S.X₃ S.X₁ 1 hS.extClass =
      (shortExact_moduleLowerShriek j Λ hS).extClass :=
  Ext.mapExactFunctor_extClass _ hS

/-- The adjunction `j_! ⊣ j^*` on Ext groups: `Ext^q(j_! A, B) ≃+ Ext^q(A, j^* B)`. -/
abbrev moduleLowerShriekExtEquiv (A : ModuleSheaf U Λ) (B : ModuleSheaf X Λ) (q : ℕ) :
    Ext.{w'} ((moduleLowerShriek j Λ).obj A) B q ≃+
      Ext.{w} A ((moduleInverseImage j Λ).obj B) q :=
  (moduleLowerShriekAdjunction j Λ).extEquiv

/-- The forward map is the unit followed by the Ext map of `j^*`. -/
theorem moduleLowerShriekExtEquiv_apply {A : ModuleSheaf U Λ} {B : ModuleSheaf X Λ} {q : ℕ}
    (e : Ext.{w'} ((moduleLowerShriek j Λ).obj A) B q) :
    moduleLowerShriekExtEquiv j Λ A B q e =
      (Ext.mk₀ ((moduleLowerShriekAdjunction j Λ).unit.app A)).comp
        (e.mapExactFunctor (moduleInverseImage j Λ)) (zero_add q) :=
  rfl

/-- The inverse map is the Ext map of `j_!` followed by the counit. -/
theorem moduleLowerShriekExtEquiv_symm_apply {A : ModuleSheaf U Λ} {B : ModuleSheaf X Λ}
    {q : ℕ} (e : Ext.{w} A ((moduleInverseImage j Λ).obj B) q) :
    (moduleLowerShriekExtEquiv j Λ A B q).symm e =
      (moduleLowerShriekExt j Λ _ _ q e).comp
        (Ext.mk₀ ((moduleLowerShriekAdjunction j Λ).counit.app B)) (add_zero q) :=
  rfl

/-- In degree zero the Ext adjunction is the adjunction bijection on morphisms. -/
theorem moduleLowerShriekExtEquiv_mk₀ {A : ModuleSheaf U Λ} {B : ModuleSheaf X Λ}
    (f : (moduleLowerShriek j Λ).obj A ⟶ B) :
    moduleLowerShriekExtEquiv j Λ A B 0 (Ext.mk₀ f) =
      Ext.mk₀ ((moduleLowerShriekAdjunction j Λ).homEquiv A B f) :=
  (moduleLowerShriekAdjunction j Λ).extEquiv_mk₀ f

/-- Yoneda compatibility in the source: precomposition with `j_!` of a class on `U`. -/
theorem moduleLowerShriekExtEquiv_comp_left {A₁ A₂ : ModuleSheaf U Λ} {B : ModuleSheaf X Λ}
    {a b c : ℕ} (e : Ext.{w} A₁ A₂ a)
    (e' : Ext.{w'} ((moduleLowerShriek j Λ).obj A₂) B b) (h : a + b = c) :
    moduleLowerShriekExtEquiv j Λ A₁ B c
        ((moduleLowerShriekExt j Λ A₁ A₂ a e).comp e' h) =
      e.comp (moduleLowerShriekExtEquiv j Λ A₂ B b e') h :=
  (moduleLowerShriekAdjunction j Λ).extEquiv_naturality_left e e' h

/-- Yoneda compatibility in the target: postcomposition with a class on `X` becomes
postcomposition with its inverse image. -/
theorem moduleLowerShriekExtEquiv_comp_right {A : ModuleSheaf U Λ} {B₁ B₂ : ModuleSheaf X Λ}
    {a b c : ℕ} (e : Ext.{w'} ((moduleLowerShriek j Λ).obj A) B₁ a) (e' : Ext.{w'} B₁ B₂ b)
    (h : a + b = c) :
    moduleLowerShriekExtEquiv j Λ A B₂ c (e.comp e' h) =
      (moduleLowerShriekExtEquiv j Λ A B₁ a e).comp
        (e'.mapExactFunctor (moduleInverseImage j Λ)) h :=
  (moduleLowerShriekAdjunction j Λ).extEquiv_naturality_right e e' h

end AlgebraicGeometry.Scheme.EtaleCohomology

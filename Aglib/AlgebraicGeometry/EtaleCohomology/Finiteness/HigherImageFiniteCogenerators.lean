/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.HigherImageConstructibleInduction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Higher images of the original finite constant-product cogenerator

Native additive product preservation and composition with the original finite
direct images reduce the product's higher-image constructibility to the actual
composite maps on their original finite constant values. Those fixed-degree
geometric hypotheses remain explicit; this does not prove them for proper maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Native additive finite-product preservation transports constructibility of
the individual higher images to the higher image of the literal product. -/
theorem higherDirectImage_isConstructible_finiteProduct
    {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ) {I : Type v} [Finite I]
    (E : I → AbelianSheaf.{u, u + 1} X)
    (hE : ∀ i, Constructible.IsConstructible ((higherDirectImage f q).obj (E i))) :
    Constructible.IsConstructible ((higherDirectImage f q).obj (∏ᶜ E)) := by
  let : Fintype I := Fintype.ofFinite I
  have hprod := Constructible.FiniteCogenerators.isConstructible_finiteProduct
    (fun i => (higherDirectImage f q).obj (E i)) hE
  exact (Constructible.isConstructible_iff_of_iso
    (PreservesProduct.iso (higherDirectImage f q) E)).mpr hprod

/-- The actual finite constant-product target has constructible higher image
when the same degree images of its original composite finite constants do. -/
theorem higherDirectImage_isConstructible_finiteConstantProductTarget
    {X S : Scheme.{u}} (f : X ⟶ S)
    {F : AbelianSheaf.{u, u + 1} X}
    (t : Constructible.FiniteCogenerators.FiniteConstantProductEmbedding F) (q : ℕ)
    (hcomp : ∀ i, Constructible.IsConstructible
      ((higherDirectImage (t.morphism i ≫ f) q).obj
        (ConstantFinite.coefficient (t.value i) (t.source i)))) :
    Constructible.IsConstructible ((higherDirectImage f q).obj
      (∏ᶜ fun i => (directImage (t.morphism i)).obj
        (ConstantFinite.coefficient (t.value i) (t.source i)))) := by
  apply higherDirectImage_isConstructible_finiteProduct
  intro i
  exact (Constructible.isConstructible_iff_of_iso
    (Finite.higherDirectImageCompFiniteIso f (t.morphism i) q
      (ConstantFinite.coefficient (t.value i) (t.source i)))).mp (hcomp i)

/-- Fixed-degree devissage with no product-image hypothesis: its replacement
is precisely the actual composite finite-constant geometric input. -/
theorem higherDirectImage_isConstructible_succ_of_finiteConstantComposites
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] (f : X ⟶ S)
    {F : AbelianSheaf.{u, u + 1} X}
    (t : Constructible.FiniteCogenerators.FiniteConstantProductEmbedding F)
    (hF : Constructible.IsConstructible F) (n : ℕ)
    (hprev : ∀ G : AbelianSheaf.{u, u + 1} X, Constructible.IsConstructible G →
      Constructible.IsConstructible ((higherDirectImage f n).obj G))
    (hcomp : ∀ i, Constructible.IsConstructible
      ((higherDirectImage (t.morphism i ≫ f) (n + 1)).obj
        (ConstantFinite.coefficient (t.value i) (t.source i)))) :
    Constructible.IsConstructible ((higherDirectImage f (n + 1)).obj F) :=
  higherDirectImage_isConstructible_succ_of_finiteConstantProductEmbedding f t hF n hprev
    (higherDirectImage_isConstructible_finiteConstantProductTarget f t (n + 1) hcomp)

end AlgebraicGeometry.Scheme.EtaleCohomology

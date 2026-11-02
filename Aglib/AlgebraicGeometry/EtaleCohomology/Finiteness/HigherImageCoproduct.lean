/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CoproductSheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.HigherImageFiniteCogenerators

/-! # Relative higher images from the actual finite coproduct branches

This is a fixed-degree relative sheaf statement. It does not replace higher
images by absolute cohomology, or infer constructibility from finite stalks.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Constructibility at the same degree on every actual component gives
constructibility for the original coefficient on the finite coproduct. -/
theorem higherDirectImage_isConstructible_of_finiteCoproduct
    {I : Type u} [Finite I] (Y : I → Scheme.{u}) {S : Scheme.{u}}
    (f : ∀ i, Y i ⟶ S) (F : AbelianSheaf.{u, u + 1} (∐ Y)) (q : ℕ)
    (h : ∀ i, Constructible.IsConstructible
      ((higherDirectImage (f i) q).obj ((inverseImage (Sigma.ι Y i)).obj F))) :
    Constructible.IsConstructible ((higherDirectImage (Sigma.desc f) q).obj F) := by
  let : ∀ i, IsFinite (Sigma.ι Y i) := Finite.sigmaComponent_isFinite Y
  have hp : Constructible.IsConstructible
      ((higherDirectImage (Sigma.desc f) q).obj (∏ᶜ Finite.componentImage Y F)) := by
    apply higherDirectImage_isConstructible_finiteProduct
    intro i
    have hi : Constructible.IsConstructible
        ((higherDirectImage (Sigma.ι Y i ≫ Sigma.desc f) q).obj
          ((inverseImage (Sigma.ι Y i)).obj F)) := by
      simpa only [Sigma.ι_comp_desc] using h i
    exact (Constructible.isConstructible_iff_of_iso
      (Finite.higherDirectImageCompFiniteIso (Sigma.desc f) (Sigma.ι Y i) q
        ((inverseImage (Sigma.ι Y i)).obj F))).mp hi
  exact (Constructible.isConstructible_iff_of_iso
    ((higherDirectImage (Sigma.desc f) q).mapIso (Finite.coproductSheafIso Y F))).mpr hp

end AlgebraicGeometry.Scheme.EtaleCohomology

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ObjectProperty
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Closure
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage

/-! # Constructibility and original higher-image short exact sequences

The complete weak-Serre derived construction applies to the original direct
image. Finite abelian constructibility, not finite generation over an arbitrary
ring, is the property transported by the native long exact sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- If both endpoints have constructible original higher images in every
degree, so does the original middle coefficient. No properness is needed for
this closure theorem; geometric producers must supply the endpoint hypotheses. -/
theorem higherDirectImage_isConstructible_of_shortExact
    {X S : Scheme.{u}} (f : X ⟶ S)
    (T : ShortComplex (AbelianSheaf.{u, u + 1} X)) (hT : T.ShortExact)
    (h₁ : ∀ q : ℕ, Constructible.IsConstructible ((higherDirectImage f q).obj T.X₁))
    (h₃ : ∀ q : ℕ, Constructible.IsConstructible ((higherDirectImage f q).obj T.X₃))
    (q : ℕ) : Constructible.IsConstructible ((higherDirectImage f q).obj T.X₂) :=
  Functor.rightDerived_property_of_shortExact (directImage f)
    (Constructible.IsConstructible (X := S)) T hT h₁ h₃ q

end AlgebraicGeometry.Scheme.EtaleCohomology

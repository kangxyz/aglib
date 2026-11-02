/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SerreInduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Noetherian.StrongSerre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.ConstructibleTarget

/-! # Fixed-degree constructibility induction for original higher images

On a Noetherian target the original long exact sequence uses the proved strong
Serre property. For an actual finite constant-product embedding its original
cokernel is constructible, so induction in the preceding degree applies to
that same coefficient. Constructibility of the next image of the product is
still a geometric input, not inferred from constructibility of the product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- Only the preceding quotient image and the next middle image are needed
in the original connecting row. The source need not be Noetherian here. -/
theorem higherDirectImage_isConstructible_succ_of_shortExact
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    (T : ShortComplex (AbelianSheaf.{u, u + 1} X)) (hT : T.ShortExact) (n : ℕ)
    (hQ : Constructible.IsConstructible ((higherDirectImage f n).obj T.X₃))
    (hE : Constructible.IsConstructible ((higherDirectImage f (n + 1)).obj T.X₂)) :
    Constructible.IsConstructible ((higherDirectImage f (n + 1)).obj T.X₁) :=
  Functor.rightDerived_property_succ_of_shortExact (directImage f)
    (Constructible.IsConstructible (X := S)) T hT n hQ hE

/-- The original mono and its actual cokernel give the required short exact
sequence, without a replacement quotient or exactness certificate input. -/
theorem higherDirectImage_isConstructible_succ_of_mono
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    {F E : AbelianSheaf.{u, u + 1} X} (a : F ⟶ E) [Mono a] (n : ℕ)
    (hQ : Constructible.IsConstructible ((higherDirectImage f n).obj (cokernel a)))
    (hE : Constructible.IsConstructible ((higherDirectImage f (n + 1)).obj E)) :
    Constructible.IsConstructible ((higherDirectImage f (n + 1)).obj F) := by
  let T := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel a }
  exact higherDirectImage_isConstructible_succ_of_shortExact f T hT n hQ hE

/-- Fixed-degree induction applies to the same original cogenerator cokernel.
The hypothesis on the next image of the literal product remains explicit. -/
theorem higherDirectImage_isConstructible_succ_of_finiteConstantProductEmbedding
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] (f : X ⟶ S)
    {F : AbelianSheaf.{u, u + 1} X}
    (t : Constructible.FiniteCogenerators.FiniteConstantProductEmbedding F)
    (hF : Constructible.IsConstructible F) (n : ℕ)
    (hprev : ∀ G : AbelianSheaf.{u, u + 1} X, Constructible.IsConstructible G →
      Constructible.IsConstructible ((higherDirectImage f n).obj G))
    (hE : Constructible.IsConstructible ((higherDirectImage f (n + 1)).obj
      (∏ᶜ fun i => (directImage (t.morphism i)).obj
        (ConstantFinite.coefficient (t.value i) (t.source i))))) :
    Constructible.IsConstructible ((higherDirectImage f (n + 1)).obj F) :=
  higherDirectImage_isConstructible_succ_of_mono f t.map n
    (hprev (cokernel t.map) (t.isConstructible_cokernel hF)) hE

end AlgebraicGeometry.Scheme.EtaleCohomology

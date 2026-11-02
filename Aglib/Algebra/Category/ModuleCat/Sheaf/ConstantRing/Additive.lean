/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Additivity of the original constant-ring coefficient equivalence

The existing equivalence preserves binary products and zero maps. The native
general theorem therefore proves additivity of its original functor; the
inverse is additive through that same equivalence. No map is reconstructed and
no global linear structure on the module-sheaf category is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c h r m

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ] [HasWeakSheafify J RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{m} Λ) AddCommGrpCat.{m})]

/-- The original coefficient-equivalence functor is additive at independent scalar/value sizes. -/
instance moduleSheafEquivalence_functor_additive :
    (moduleSheafEquivalence.{c, h, r, m} J Λ).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The original inverse coefficient-equivalence functor is additive. -/
instance moduleSheafEquivalence_inverse_additive :
    (moduleSheafEquivalence.{c, h, r, m} J Λ).inverse.Additive :=
  Equivalence.inverse_additive (moduleSheafEquivalence J Λ)

end ModuleCat.Sheaf.ConstantRing

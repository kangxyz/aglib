/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModImages
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.InjectiveRetract
public import Aglib.CategoryTheory.Adjunction.InjectiveTests
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf
public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.ZMod

/-! # Genuine injective module retracts along an actual surjection

The original abelian inverse image of an n-killed coefficient is again
n-killed. Give it the published canonical genuine-module structure, embed in
an injective module sheaf upstairs, and use the original abelian adjunction.
Faithful inverse image makes that adjoint map monic. Full genuine ZMod
forgetting then lifts it to the module category, where injectivity downstairs
splits it. No forgotten injective is declared injective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

/-- The original underlying coefficient of a genuine ZMod-module sheaf is
annihilated by the literal modulus on its original identity map. -/
theorem zmodUnderlying_nsmul_id (X : Scheme.{u}) (n : ℕ) (I : ZModSheaf X n) :
    n • 𝟙 ((zmodUnderlying X n).obj I) = 0 :=
  TorsionZMod.sheafUnderlying_nsmul_id.{u + 1, u, u + 1} X.smallEtaleTopology n I

/-- The actual genuine module pullback is faithful along a surjective scheme map,
by its original scalar-underlying comparison and the original abelian pullback. -/
instance zmodInverseImage_faithful_of_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] (n : ℕ) :
    (zmodInverseImage f n).Faithful := by
  let : (inverseImage f).Faithful := inverseImage_faithful_of_surjective f
  let : (zmodUnderlying S n ⋙ inverseImage f).Faithful := inferInstance
  let : (zmodInverseImage f n ⋙ zmodUnderlying X n).Faithful :=
    Functor.Faithful.of_iso (zmodInverseImageUnderlyingIso f n).symm
  exact Functor.Faithful.of_comp (zmodInverseImage f n) (zmodUnderlying X n)

/-- Every genuine module injective downstairs is an actual coefficient retract
of the genuine direct image of an actual module injective upstairs, for an
arbitrary surjective scheme morphism and every modulus. -/
theorem exists_zmodInjective_directImage_retract
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    (n : ℕ) (I : ZModSheaf S n) [Injective I] :
    ∃ J : ZModSheaf X n, Injective J ∧
      Nonempty (Retract I ((zmodDirectImage f n).obj J)) := by
  let : (zmodInverseImage f n).Faithful := zmodInverseImage_faithful_of_surjective f n
  let : EnoughInjectives (ZModSheaf X n) :=
    TorsionZMod.enoughInjectivesStandard.{u + 1, u} X.smallEtaleTopology n
  exact CategoryTheory.Adjunction.exists_injective_rightAdjoint_retract
    (C := ZModSheaf S n) (D := ZModSheaf X n)
    (zmodInverseImage f n) (zmodDirectImage f n) (zmodImageAdjunction f n) I

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

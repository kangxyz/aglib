/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Linear.ModuleValuedTransform
public import Aglib.CategoryTheory.Sites.Linear
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Original cohomology of actual constant module sheaves

The native constant-module underlying-sheaf comparison induces a natural linear
isomorphism on the original cohomology groups. Both actions are the original
coefficient actions: compatibility uses actual linearity of the constant-sheaf
functor and naturality of the underlying comparison at scalar endomorphisms.
No action is identified merely because the additive carriers agree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace ModuleCat.Sheaf

universe u v r e

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [CommRing R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

attribute [local instance] hasSheafify

/-- The original constant-module underlying comparison on original cohomology,
linear for the actual actions on both sides and natural in the coefficient module. -/
def constantUnderlyingCohomologyIso (q : ℕ) :
    constantSheaf J (ModuleCat.{max u v} R) ⋙ cohomology J R q ≅
      constantCohomology J R q :=
  Functor.moduleValuedCompIso R (constantSheaf J (ModuleCat.{max u v} R))
      (underlying R J ⋙ CategoryTheory.Sheaf.functorH J q) ≪≫
    Functor.moduleValuedNatIso R
      (Functor.isoWhiskerRight (constantUnderlyingIso R J) (CategoryTheory.Sheaf.functorH J q))

/-- The linear comparison's forward map is literally the original cohomology map
of the native constant-module underlying-sheaf isomorphism. -/
theorem constantUnderlyingCohomologyIso_hom_app_apply (q : ℕ)
    (M : ModuleCat.{max u v} R)
    (x : (cohomology J R q).obj ((constantSheaf J (ModuleCat.{max u v} R)).obj M)) :
    (constantUnderlyingCohomologyIso J R q).hom.app M x =
      CategoryTheory.Sheaf.H.map ((constantUnderlyingIso R J).hom.app M) q x := rfl

/-- Finite generation transports across the actual scalar-compatible original
cohomology comparison, including for coefficients with infinite underlying group. -/
theorem finite_cohomology_constant_iff (q : ℕ) (M : ModuleCat.{max u v} R) :
    Module.Finite R
        ((cohomology J R q).obj ((constantSheaf J (ModuleCat.{max u v} R)).obj M)) ↔
      Module.Finite R ((constantCohomology J R q).obj M) :=
  Module.Finite.equiv_iff ((constantUnderlyingCohomologyIso J R q).app M).toLinearEquiv

end ModuleCat.Sheaf

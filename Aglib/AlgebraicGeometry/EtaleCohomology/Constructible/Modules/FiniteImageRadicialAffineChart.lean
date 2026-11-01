/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GenericRadicialAffineChart

/-! # Native finite radicial chart specialization

The coefficient-free geometry constructs the same actual entire-pullback map.
This native wrapper retains the original public interface and maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

/-- An entire finite-etale source chart descends on a nonempty affine target
open, in a form directly usable by original coefficient pullback. -/
theorem exists_affine_radicial_chart_factorization
    {Y X : Scheme.{u}} [IsAffine Y] [IsAffine X] [IsIntegral Y] [IsIntegral X]
    [IsNoetherian X] (f : Y ⟶ X) [IsFinite f] [UniversallyInjective f] [Surjective f]
    (W : Scheme.FiniteEtale Y) [Surjective W.obj.hom] :
    ∃ (U : Scheme.{u}) (j : U ⟶ X), IsAffine U ∧ IsOpenImmersion j ∧ Nonempty U ∧
      ∃ T : Scheme.FiniteEtale U, Surjective T.obj.hom ∧
        ∃ a : pullback f (T.obj.hom ≫ j) ⟶ W.obj.left,
          a ≫ W.obj.hom = pullback.fst f (T.obj.hom ≫ j) :=
  Scheme.FiniteEtale.PurelyInseparable.exists_affine_radicial_chart_factorization f W

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SurjectivePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying

/-! # Faithfulness of the original module inverse image under surjective maps -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Faithfulness descends from the original abelian inverse image through
its actual native constant-ring comparison. -/
theorem moduleInverseImage_faithful_of_surjective_map
    {T' T : Scheme.{u}} (f : T' ⟶ T) [Surjective f]
    (Λ : Type (u + 1)) [Ring Λ] :
    (moduleInverseImage f Λ).Faithful := by
  let : (inverseImage f).Faithful :=
    Proper.Reduction.inverseImage_faithful_of_surjective f
  let : (SheafOfModules.toSheaf (constantRing T Λ) ⋙ inverseImage f).Faithful :=
    inferInstance
  let : (moduleInverseImage f Λ ⋙
      SheafOfModules.toSheaf (constantRing T' Λ)).Faithful :=
    Functor.Faithful.of_iso (moduleInverseImageUnderlyingIso Λ f).symm
  exact Functor.Faithful.of_comp (moduleInverseImage f Λ)
    (SheafOfModules.toSheaf (constantRing T' Λ))

end AlgebraicGeometry.Scheme.EtaleCohomology

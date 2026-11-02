/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.StalkMap

/-!
# Injectivity of the original stalk map of a dominant integral morphism

The original function-field/stalk square proves injectivity directly. This
owns the proof formerly used inside the complete-surface stalk application.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A dominant morphism between integral schemes induces injective original
stalk homomorphisms. No properness, Noetherianity or finiteness is required. -/
theorem Hom.stalkMap_injective_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply (functionFieldMap f).injective
  rw [functionFieldMap_stalk, functionFieldMap_stalk]
  exact congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hab

end AlgebraicGeometry.Scheme

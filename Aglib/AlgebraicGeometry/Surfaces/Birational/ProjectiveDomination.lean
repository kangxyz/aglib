/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The original comparison graph in projective domination

For the supplied exact triangle `a ≫ π = β`, the graph into the literal
fibre product `Y ×[Z] W` is closed when `π` is separated. The two projection
equations retain the original maps. This is the graph step of projective
domination; it does not supply projectivity of the fibre product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Birational

variable {Y Z W : Scheme.{u}} (β : Y ⟶ Z) (π : W ⟶ Z)
  (a : Y ⟶ W) (ha : a ≫ π = β)

/-- The graph of the original comparison map with its exact supplied triangle. -/
def comparisonGraph : Y ⟶ pullback β π :=
  pullback.lift (𝟙 Y) a (by simpa only [Category.id_comp] using ha.symm)

@[reassoc (attr := simp)]
theorem comparisonGraph_fst : comparisonGraph β π a ha ≫ pullback.fst β π = 𝟙 Y :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem comparisonGraph_snd : comparisonGraph β π a ha ≫ pullback.snd β π = a :=
  pullback.lift_snd _ _ _

/-- Separation closes the graph of the actual comparison morphism. -/
theorem comparisonGraph_isClosedImmersion [IsSeparated π] :
    IsClosedImmersion (comparisonGraph β π a ha) := by
  subst β
  exact inferInstanceAs
    (IsClosedImmersion (pullback.lift (𝟙 Y) a (Category.id_comp (a ≫ π))))

end AlgebraicGeometry.Scheme.Birational

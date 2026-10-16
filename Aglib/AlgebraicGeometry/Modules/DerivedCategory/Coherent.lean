/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.ObjectProperty.ExactFive
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Extensions.Global
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Coherent homology of original bounded-below derived objects

On a locally Noetherian scheme, this object property says exactly that all
native homology sheaves of an actual D-plus object are coherent. There is
no upper bound in the target property and no condition on representative
terms. Isomorphism, zero and distinguished-triangle extension closure use
the original homology functors and long exact sequence. The supplied native
derived-category instance is retained, with an independent universe.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped ZeroObject

universe u w

namespace AlgebraicGeometry.Scheme.Modules

open QuasiCoherent

/-- Coherence of every original native homology sheaf of a D-plus object.
This target property imposes no upper cohomological bound. -/
@[nolint unusedArguments]
def coherentHomologyObjects (X : Scheme.{u}) [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] : ObjectProperty (DerivedCategory.Plus X.Modules) := fun K =>
  ∀ i : ℤ, affineLocallyFiniteType X ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K)

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

instance coherentHomologyObjects_isClosedUnderIsomorphisms :
    (coherentHomologyObjects X).IsClosedUnderIsomorphisms where
  of_iso e h i :=
    (affineLocallyFiniteType X).prop_of_iso
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).mapIso e) (h i)

instance coherentHomologyObjects_containsZero : (coherentHomologyObjects X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun i =>
    (affineLocallyFiniteType X).prop_of_isZero
      ((DerivedCategory.Plus.homologyFunctor X.Modules i).map_isZero (isZero_zero _))⟩

/-- Coherent native homology is closed under distinguished-triangle
extensions. The exact-five argument only uses kernels and cokernels of
maps between known coherent homology sheaves. -/
theorem coherentHomologyObjects_of_distinguished_triangle
    (T : Triangle (DerivedCategory.Plus X.Modules)) (hT : T ∈ distTriang _)
    (h₁ : coherentHomologyObjects X T.obj₁) (h₃ : coherentHomologyObjects X T.obj₃) :
    coherentHomologyObjects X T.obj₂ := by
  intro i
  let T' := (DerivedCategory.Plus.ι :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory X.Modules).mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := (DerivedCategory.Plus.ι).map_distinguished T hT
  exact (affineLocallyFiniteType X).prop_middle_of_exact_five
    (DerivedCategory.HomologySequence.δ T' (i - 1) i (by omega))
    ((DerivedCategory.homologyFunctor X.Modules i).map T'.mor₁)
    ((DerivedCategory.homologyFunctor X.Modules i).map T'.mor₂)
    (DerivedCategory.HomologySequence.δ T' i (i + 1) rfl)
    (DerivedCategory.HomologySequence.exact₁ T' hT' (i - 1) i (by omega))
    (DerivedCategory.HomologySequence.exact₂ T' hT' i)
    (DerivedCategory.HomologySequence.exact₃ T' hT' i (i + 1) rfl)
    (h₃ (i - 1)) (h₁ i) (h₃ i) (h₁ (i + 1))

instance coherentHomologyObjects_isTriangulatedClosed₂ :
    (coherentHomologyObjects X).IsTriangulatedClosed₂ :=
  .mk' (coherentHomologyObjects_of_distinguished_triangle X)

end AlgebraicGeometry.Scheme.Modules

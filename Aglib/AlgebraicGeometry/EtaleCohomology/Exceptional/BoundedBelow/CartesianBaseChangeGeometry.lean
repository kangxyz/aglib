/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Actual geometry of the Cartesian base-change presentation -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u
variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  (g : T ⟶ S) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)

include sq in
/-- Quasi-compactness of the presented morphism follows from the actual Cartesian square. -/
theorem moduleCartesianBaseChange_quasiCompact [QuasiCompact f] : QuasiCompact f' :=
  MorphismProperty.of_isPullback sq inferInstance

/-- On the literal pullback, its actual universal source isomorphism is the identity. -/
theorem moduleCartesianBaseChange_literalSourceIso :
    (IsPullback.of_hasPullback g f).flip.flip.isoPullback = Iso.refl (pullback g f) := by
  apply Iso.ext
  apply pullback.hom_ext
  · simp only [IsPullback.isoPullback_hom_fst, Iso.refl_hom, Category.id_comp]
  · simp only [IsPullback.isoPullback_hom_snd, Iso.refl_hom, Category.id_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology

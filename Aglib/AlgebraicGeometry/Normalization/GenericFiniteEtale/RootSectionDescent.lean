/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodRootLimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Original root-cover sections at a genuine etale stage

The native Hom-limit theorem descends the actual lift into the unchanged
finitely presented cover. Both its root-base equation and its original
colimit comparison are retained, after any prescribed neighborhood. No
normalization/base-change or strict-local Noetherianity premise is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

/-- Descend an actual lift over the fixed original root spectrum, after any
specified genuine etale neighborhood. Its pointwise values are retained by
the exact original cone comparison, not merely by an unspecified isomorphism. -/
theorem exists_rootStage_lift
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] (N : ℕ) (f : R)
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of (RootAlgebra N f)))
    [LocallyOfFinitePresentation p]
    (a : Spec (.of (RootAlgebra N (algebraMap R (GeometricEtaleColimit R Ω) f))) ⟶ Z)
    (ha : a ≫ p = Spec.map (CommRingCat.ofHom
      (rootBaseChangeHom (GeometricEtaleColimit R Ω) N f).toRingHom))
    (X₀ : GeometricEtaleNeighborhood R Ω) :
    ∃ (Y : GeometricEtaleNeighborhood R Ω) (_ : X₀ ⟶ Y)
      (b : (rootDiagram R Ω N f).obj (op Y) ⟶ Z),
      b ≫ p = (rootStructure R Ω N f).app (op Y) ∧
      (rootCone R Ω N f).π.app (op Y) ≫ b = a := by
  have hbase : (rootCone R Ω N f).π ≫ rootStructure R Ω N f =
      (Functor.const _).map (a ≫ p) := by
    rw [ha]
    exact rootCone_structure R Ω N f
  obtain ⟨i, b, hb, hbp⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (rootDiagram R Ω N f) (rootStructure R Ω N f) p
    (rootCone R Ω N f) (rootConeIsLimit R Ω N f) a hbase
  let Y := IsFiltered.max X₀ i.unop
  let g : op Y ⟶ i := (IsFiltered.rightToMax X₀ i.unop).op
  refine ⟨Y, IsFiltered.leftToMax X₀ i.unop, (rootDiagram R Ω N f).map g ≫ b, ?_, ?_⟩
  · rw [Category.assoc, hbp]
    exact ((rootStructure R Ω N f).naturality g).trans (Category.comp_id _)
  · rw [← Category.assoc, (rootCone R Ω N f).w g, hb]

end AlgebraicGeometry.Scheme.Kummer

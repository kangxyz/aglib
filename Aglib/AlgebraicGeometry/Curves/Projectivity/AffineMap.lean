/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Native
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Integral

/-!
# Affine morphisms from proper integral curves to the projective line

A proper integral dimension-one scheme over any field has an affine morphism
to the literal `Scheme.ProjectiveLine.projectiveP1` over that field. The map
is the existing finite dominant map to the native projective line composed
with the original comparison isomorphism. No smoothness, geometric
integrality, rational point or Picard construction is required.

The proof uses
`OverField.Curve.Projectivity.exists_finite_dominant_map_to_nativeP1` from
`Curves/Projectivity/Integral.lean` and
`ProjectiveLine.projectiveLineOverIsoNative` from
`Curves/ProjectiveLine/Native.lean`, without replacing either construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

/-- A proper integral scheme of dimension one over a field has an affine morphism to the
projective line: the finite dominant map of `exists_finite_dominant_map_to_nativeP1`, followed by
the identification of the native projective line with `Proj k[x, y]`. -/
theorem exists_isAffineHom_to_projectiveP1 {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] [IsIntegral X] (hdim : topologicalKrullDim X = 1) :
    ∃ ρ : X ⟶ Scheme.ProjectiveLine.projectiveP1 k, IsAffineHom ρ := by
  have : IsProper (Over.mk p).hom := ‹IsProper p›
  have : IsIntegral (Over.mk p).left := ‹IsIntegral X›
  obtain ⟨π₁, hπ₁, -⟩ := exists_finite_dominant_map_to_nativeP1 (Over.mk p) hdim
  let isoP1 := (Over.forget _).mapIso (ProjectiveLine.projectiveLineOverIsoNative k)
  have : IsAffineHom π₁.left := inferInstance
  exact ⟨π₁.left ≫ isoP1.inv, inferInstance⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Smooth.RelativeRepresentative
public import Aglib.AlgebraicGeometry.Picard.Scheme.Properties

/-!
# Relative Picard smoothness from an actual affine map to the projective line

Over a Noetherian ring, the original fppf Picard representative of a proper flat
geometrically integral family with a section is smooth if the family admits an
actual affine morphism to a projective line. The two affine charts lift line
bundles across square-zero thickenings, and the original infinitesimal criterion
then proves smoothness. Local finite type is necessary for that criterion.

For a closed finite-dimensional projective family, the existing Picard construction
supplies both the representative and local finite type. No smoothness or finite
torsion-kernel assumption is imposed. Existence of the affine map over a dense open
base, and finiteness of the relative torsion kernel, are separate statements.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

/-- The actual constructed projective Picard scheme is smooth under the same affine-map
hypothesis. Its local finite type and representation come from the original construction. -/
theorem smooth_picardScheme_of_isAffineHom_projectiveP1
    {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
    {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i]
    [Flat (i ≫ toSpec A ι)] [GeometricallyIntegral (i ≫ toSpec A ι)]
    {N : ℕ} {e : ι ≃ Fin (N + 1)}
    (h : Strata.FineStrataRepresentableByHQuasiProjective i N e)
    (o : Spec (.of A) ⟶ X) (ho : o ≫ i ≫ toSpec A ι = 𝟙 _)
    {R₀ : Type u} [CommRing R₀] (ρ : X ⟶ ProjectiveLine.projectiveP1 R₀)
    [IsAffineHom ρ] : Smooth (picardScheme h).obj.hom := by
  have := isProper_comp_toSpec_of_isClosedImmersion i e
  exact smooth_representative_of_isAffineHom_projectiveP1
    (i ≫ toSpec A ι) o ho (picardScheme h) (picardSchemeRepresentableBy h) ρ

/-- A finite-dimensional projective embedding constructs a smooth original Picard
representative, without an external representability or smoothness input. -/
theorem exists_smooth_representative_of_projective_of_isAffineHom_projectiveP1
    {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i]
    [Flat (i ≫ toSpec A ι)] [GeometricallyIntegral (i ≫ toSpec A ι)]
    {N : ℕ} (e : ι ≃ Fin (N + 1))
    (o : Spec (.of A) ⟶ X) (ho : o ≫ i ≫ toSpec A ι = 𝟙 _)
    {R₀ : Type u} [CommRing R₀] (ρ : X ⟶ ProjectiveLine.projectiveP1 R₀)
    [IsAffineHom ρ] :
    ∃ P : LocallyNoetherianOver (Spec (.of A)),
      Nonempty (((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) ∧
        Smooth P.obj.hom := by
  let h := Strata.fineStrataRepresentableByHQuasiProjective i e
  exact ⟨picardScheme h, ⟨picardSchemeRepresentableBy h⟩,
    smooth_picardScheme_of_isAffineHom_projectiveP1 h o ho ρ⟩

end AlgebraicGeometry.Scheme.RelativePicard

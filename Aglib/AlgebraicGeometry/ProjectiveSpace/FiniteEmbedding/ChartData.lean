/-
Copyright (c) 2026 R5Lab contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure

/-!
# Original chart coefficients for finite projective embeddings

The coefficient rings are the actual sections on inverse images of the standard
projective charts. Their scalar actions come from the original scheme morphism.
The transition convention uses `coordinateTransitionOn i j = Xᵢ / Xⱼ`.
-/




@[expose] public section

noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding

variable {R : Type u} [CommRing R] {ι : Type u} {Y : Scheme.{u}}
  (f : Y ⟶ ProjectiveSpace R ι)

/-- The original inverse image of a standard projective coordinate open. -/
abbrev sourceOpen (i : ι) : Y.Opens := f ⁻¹ᵁ coordinateOpen R ι i

/-- The scalar action on actual preimage sections induced by the original morphism. -/
abbrev preimageSectionsAlgebra (U : (ProjectiveSpace R ι).Opens) :
    Algebra Γ(ProjectiveSpace R ι, U) Γ(Y, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

/-- Restriction on the original preimages of two nested base opens. -/
abbrev restrictPreimageSections {V W : (ProjectiveSpace R ι).Opens} (h : V ≤ W) :
    Γ(Y, f ⁻¹ᵁ W) →+* Γ(Y, f ⁻¹ᵁ V) :=
  sectionRestrict Y (f.preimage_mono h)

/-- A finite family of actual chart generators in one positive homogeneous degree.
Its realization from a finite morphism is supplied separately; no realization is
assumed in the generic finite-embedding theorem. -/
structure ChartData where
  /-- The finite index type of the additional homogeneous coordinates. -/
  J : Type u
  /-- Finiteness is independent of an arbitrary choice of enumeration. -/
  finite_J : Finite J
  /-- The common degree of the homogeneous coordinates. -/
  d : ℕ
  /-- Positivity permits the mixed monomials `Xₖ^(d-1) * Xₗ`. -/
  one_le_d : 1 ≤ d
  /-- Original sections on the original affine preimages. -/
  b : ∀ i : ι, J → Γ(Y, sourceOpen f i)
  /-- The coefficients span each preimage algebra over the actual base-chart sections. -/
  span_b : ∀ i : ι,
    letI := preimageSectionsAlgebra f (coordinateOpen R ι i)
    Submodule.span Γ(ProjectiveSpace R ι, coordinateOpen R ι i) (Set.range (b i)) = ⊤
  /-- On every common base subopen, the `j` coefficient is `(Xᵢ/Xⱼ)^d`
  times the `i` coefficient, pulled back by the original structure-sheaf map. -/
  transition : ∀ (i j : ι) (V : (ProjectiveSpace R ι).Opens)
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) (a : J),
    restrictPreimageSections f hj (b j a) =
      (f.app V) (((coordinateTransitionOn R ι i j hi hj) ^ d).val) *
        restrictPreimageSections f hi (b i a)

attribute [instance] ChartData.finite_J

end AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding

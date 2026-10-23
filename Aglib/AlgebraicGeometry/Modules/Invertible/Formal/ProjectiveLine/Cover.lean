/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Basic
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The actual two-affine cover above the projective line

The two charts are the inverse images of the original coordinate opens.
Their intersection and their categorical pullback are affine whenever the
original map to the projective line is affine, in particular when it is finite.
No flatness, reducedness or Noetherian hypothesis is required.

The native polynomial `Proj` permits a base ring in an arbitrary universe
while retaining the original coordinate type `Fin 2`. For small base rings
it is definitionally `ProjectiveSpace R (Fin 2)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Scheme.ProjectiveLine.projectiveP1 R)

/-- Where the literal `Fin 2` projective-space notation is well typed, it
is the existing universe-polymorphic native projective line. -/
theorem projectiveP1_eq_projectiveSpace (R : Type) [CommRing R] :
    Scheme.ProjectiveLine.projectiveP1 R = ProjectiveSpace R (Fin 2) := rfl

/-- The inverse image of an original coordinate open of the projective line. -/
def projectiveLineChartOpen (i : Fin 2) : Y.Opens :=
  p ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X i)

/-- The actual open subscheme above an original coordinate chart. -/
abbrev projectiveLineChart (i : Fin 2) : Scheme.{u} :=
  (projectiveLineChartOpen p i).toScheme

/-- The original open immersion of the chart into the source scheme. -/
abbrev projectiveLineChartι (i : Fin 2) : projectiveLineChart p i ⟶ Y :=
  (projectiveLineChartOpen p i).ι

/-- The two actual inverse-image coordinate opens cover the source. -/
theorem projectiveLineChartOpen_sup :
    projectiveLineChartOpen p 0 ⊔ projectiveLineChartOpen p 1 = ⊤ := by
  have htwo : (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (MvPolynomial.X i)) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 0) ⊔
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) := by
    apply eq_of_forall_ge_iff
    intro U
    simp only [iSup_le_iff, Fin.forall_fin_two, sup_le_iff]
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)
    (MvPolynomial.irrelevant_homogeneousSubmodule_eq_idealOfVars R (Fin 2)).le
  rw [htwo] at h
  simp only [projectiveLineChartOpen, ← Scheme.Hom.preimage_sup, h,
    Scheme.Hom.preimage_top]

/-- The original chart immersions jointly cover the source. -/
theorem projectiveLineChartι_cover :
    (projectiveLineChartι p 0).opensRange ⊔
      (projectiveLineChartι p 1).opensRange = ⊤ := by
  simpa only [projectiveLineChartι, Scheme.Opens.opensRange_ι] using
    projectiveLineChartOpen_sup p

variable [IsAffineHom p]

/-- The actual inverse-image coordinate charts are affine opens. -/
theorem isAffineOpen_projectiveLineChartOpen (i : Fin 2) :
    IsAffineOpen (projectiveLineChartOpen p i) :=
  (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).preimage p

instance projectiveLineChart_isAffine (i : Fin 2) : IsAffine (projectiveLineChart p i) :=
  isAffineOpen_projectiveLineChartOpen p i

/-- The actual intersection of the two inverse-image coordinate charts is affine. -/
theorem isAffineOpen_projectiveLineChartIntersection :
    IsAffineOpen (projectiveLineChartOpen p 0 ⊓ projectiveLineChartOpen p 1) := by
  have h := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (MvPolynomial.X 0 * MvPolynomial.X 1)
    ((MvPolynomial.isHomogeneous_X R (0 : Fin 2)).mul
      (MvPolynomial.isHomogeneous_X R (1 : Fin 2))) (by decide : 0 < 1 + 1)
  rw [Proj.basicOpen_mul] at h
  exact h.preimage p

/-- The categorical pullback of the original chart immersions is affine. -/
instance projectiveLineChartPullback_isAffine :
    IsAffine (Limits.pullback (projectiveLineChartι p 0) (projectiveLineChartι p 1)) := by
  let : IsAffine ((projectiveLineChartOpen p 0 ⊓ projectiveLineChartOpen p 1).toScheme) :=
    isAffineOpen_projectiveLineChartIntersection p
  exact IsAffine.of_isIso
    (isPullback_opens_inf (projectiveLineChartOpen p 0)
      (projectiveLineChartOpen p 1)).isoPullback.inv

end AlgebraicGeometry.Scheme.Modules.Invertible

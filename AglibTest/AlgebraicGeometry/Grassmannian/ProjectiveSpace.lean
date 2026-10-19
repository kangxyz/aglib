/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace.FunctorOfPoints
public import Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace.UniversalQuotient

/-!
# Projective space as the Grassmannian of rank-one quotients

The declarations below restate, for the coordinate types `Fin (n + 1)` (base rings in universe
`0`) and `ULift (Fin (n + 1))` (every universe), the comparison of Aglib's projective space with the
glued Grassmannian of rank-one quotients, the functor of points of projective space obtained from
it, and the universal point on the standard charts, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TensorProduct MvPolynomial
open scoped Module.Grassmannian

universe u

set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AglibTest.ProjectiveSpaceGrassmannian

/-- `Gr(R^{n+1}, 1) ≅ P^n_R` over `Spec R`, for base rings in universe `0`. -/
def grassmannianOverIso (R : CommRingCat.{0}) (n : ℕ) :
    Grassmannian.schemeOver R 1 (n + 1) ≅ ProjectiveSpace.schemeOver R (Fin (n + 1)) :=
  ProjectiveSpace.grassmannianOverIso R (Equiv.refl (Fin (n + 1)))

/-- `Gr(R^{n+1}, 1) ≅ P^n_R` over `Spec R`, in every universe. -/
def grassmannianOverIsoULift (R : CommRingCat.{u}) (n : ℕ) :
    Grassmannian.schemeOver R 1 (n + 1) ≅ ProjectiveSpace.schemeOver R (ULift.{u} (Fin (n + 1))) :=
  ProjectiveSpace.grassmannianOverIso R Equiv.ulift

/-- The comparison is compatible with the structure morphisms. -/
example (R : CommRingCat.{0}) (n : ℕ) :
    (grassmannianOverIso R n).hom.left ≫ ProjectiveSpace.toSpec R (Fin (n + 1)) =
      Grassmannian.toBase R 1 (n + 1) :=
  Over.w (grassmannianOverIso R n).hom

/-- Maps `Spec A ⟶ P^n_R` over `Spec R` are the submodules of `A ⊗[R] R^{n+1}` with finite
projective quotient of rank one. -/
def representableEquiv (R : CommRingCat.{0}) (n : ℕ) (A : CommAlgCat.{0} R) :
    ((algSpec R).obj (op A) ⟶ ProjectiveSpace.schemeOver R (Fin (n + 1))) ≃
      G(1, A ⊗[R] (Fin (n + 1) → R); A) :=
  ProjectiveSpace.representableEquiv R (Equiv.refl (Fin (n + 1))) A

/-- The identification is natural: precomposition with `Spec h` is base change along `h`. -/
theorem representableEquiv_comp (R : CommRingCat.{0}) (n : ℕ) {A B : CommAlgCat.{0} R}
    (h : A ⟶ B) (g : (algSpec R).obj (op A) ⟶ ProjectiveSpace.schemeOver R (Fin (n + 1))) :
    representableEquiv R n B ((algSpec R).map h.op ≫ g) =
      Module.Grassmannian.map h.hom (representableEquiv R n A g) :=
  ProjectiveSpace.representableEquiv_comp R (Equiv.refl _) h g

/-- Projective space represents Mathlib's Grassmannian functor of rank-one quotients. -/
def representableIso (R : CommRingCat.{0}) (n : ℕ) :
    (algSpec R).rightOp ⋙ yoneda.obj (ProjectiveSpace.schemeOver R (Fin (n + 1))) ≅
      Module.Grassmannian.functor.{0, 0, 0} (R := R) (M := Fin (n + 1) → R) 1 :=
  ProjectiveSpace.representableIso R (Equiv.refl _)

/-- Maps from any scheme over `Spec R` into `P^n_R` are the natural transformations from its
functor of points on `R`-algebras to Mathlib's Grassmannian functor of rank-one quotients. -/
def homEquivNatTrans (R : CommRingCat.{u}) (n : ℕ) (T : Over (Spec R)) :
    (T ⟶ ProjectiveSpace.schemeOver R (ULift.{u} (Fin (n + 1)))) ≃
      ((algSpec R).rightOp ⋙ yoneda.obj T ⟶
        Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin (n + 1) → R) 1) :=
  ProjectiveSpace.homEquivNatTrans R Equiv.ulift T

/-- `P^n_R` represents the extension of Mathlib's functor to all schemes over `Spec R`. -/
def localFunctorRepresentableBy (R : CommRingCat.{u}) (n : ℕ) :
    (Grassmannian.localFunctor R 1 (n + 1)).RepresentableBy
      (ProjectiveSpace.schemeOver R (ULift.{u} (Fin (n + 1)))) :=
  ProjectiveSpace.localFunctorRepresentableBy R Equiv.ulift

/-- The identity of `P^n_R` classifies, on the standard chart `D₊(Xᵢ)`, the coordinate quotient
`e_j ↦ X_j / X_i`. -/
theorem homEquivNatTrans_id_app_chartOver (R : CommRingCat.{0}) (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveSpace.homEquivNatTrans R (Equiv.refl (Fin (n + 1)))
        (ProjectiveSpace.schemeOver R (Fin (n + 1))) (𝟙 _)).app
        (ProjectiveSpace.coordinateAlg R i) (ProjectiveSpace.chartOver R i) =
      Module.Grassmannian.ofChartSection
        (ProjectiveSpace.chartRatioSection R (Equiv.refl (Fin (n + 1))) i)
        (ProjectiveSpace.chartRatioSection_mem R (Equiv.refl _)
          (ProjectiveSpace.chartIndex (Equiv.refl _) i).down i rfl) :=
  ProjectiveSpace.homEquivNatTrans_id_app_chartOver R _ i

/-- The chart section has the coordinate ratios as components. -/
example (R : CommRingCat.{0}) (n : ℕ) (i j : Fin (n + 1)) :
    ProjectiveSpace.chartRatioSection R (Equiv.refl (Fin (n + 1))) i (Pi.single j 1) 0 =
      ProjectiveSpace.coordinateRatio R (Fin (n + 1)) i j :=
  ProjectiveSpace.chartRatioSection_single R _ i j 0

/-- On `D₊(Xᵢ)`, the chart quotient is the universal quotient `O^{n+1} ↠ O(1)` by the coordinate
sections, in the standard frame. -/
theorem awayToSection_chartRatioSection (R : Type) [CommRing R] (n : ℕ) (i j : Fin (n + 1)) :
    Proj.awayToSection (homogeneousSubmodule (Fin (n + 1)) R) (X i)
        (ProjectiveSpace.chartRatioSection R (Equiv.refl (Fin (n + 1))) i (Pi.single j 1) 0) =
      ProjectiveSpace.twistingSectionsEquiv R (Fin (n + 1)) ((1 : ℕ) : ℤ) i le_rfl
        ((ProjectiveSpace.coordinatePowerGeneratingMap R (Fin (n + 1)) 1).val.app
          (op (ProjectiveSpace.coordinateOpen R (Fin (n + 1)) i))
          ((SheafOfModules.freeSection
            (R := (ProjectiveSpace R (Fin (n + 1))).ringCatSheaf) j).val
              (op (ProjectiveSpace.coordinateOpen R (Fin (n + 1)) i)))) :=
  ProjectiveSpace.awayToSection_chartRatioSection R (Equiv.refl _) i j

/-- On `D₊(Xᵢ Xⱼ)` the chart sections differ by the transition unit `Xᵢ / Xⱼ` of the twisting
sheaves. -/
theorem overlapRight_chartRatioSection (R : Type) [CommRing R] (n : ℕ) (i j : Fin (n + 1))
    (v : Fin (n + 1) → R) :
    ProjectiveSpace.coordinateRightToOverlap R (Fin (n + 1)) i j
        (ProjectiveSpace.chartRatioSection R (Equiv.refl (Fin (n + 1))) j v 0) =
      (ProjectiveSpace.coordinateTransitionUnit R (Fin (n + 1)) i j :
          ProjectiveSpace.coordinateOverlapRing R (Fin (n + 1)) i j) *
        ProjectiveSpace.coordinateLeftToOverlap R (Fin (n + 1)) i j
          (ProjectiveSpace.chartRatioSection R (Equiv.refl (Fin (n + 1))) i v 0) :=
  ProjectiveSpace.overlapRight_chartRatioSection R _ i j v

/-- A map `Spec A ⟶ P^n_R` given by a chart section at `e_i` factors through `D₊(Xᵢ)`. -/
example (R : CommRingCat.{0}) (n : ℕ) (i : Fin (n + 1)) {A : CommAlgCat.{0} R}
    (φ : (Fin (n + 1) → R) →ₗ[R] (Fin 1 → A))
    (hφ : φ ∈ Module.Grassmannian.chartSections R A
      (Module.Grassmannian.coordinateTuple R
        (ProjectiveSpace.chartIndex (Equiv.refl (Fin (n + 1))) i).down)) :
    (representableEquiv R n A).symm (Module.Grassmannian.ofChartSection φ hφ) =
      (algSpec R).map (ProjectiveSpace.chartSectionToCoordinate R (Equiv.refl _) i φ hφ).op ≫
        ProjectiveSpace.chartOver R i :=
  ProjectiveSpace.representableEquiv_symm_ofChartSection R _ i φ hφ

/-- An endomorphism of `P^n_R` classifying the coordinate quotients on the standard charts is the
identity. -/
theorem eq_id_of_chartOver (R : CommRingCat.{0}) (n : ℕ)
    (g : ProjectiveSpace.schemeOver R (Fin (n + 1)) ⟶ ProjectiveSpace.schemeOver R (Fin (n + 1)))
    (h : ∀ i, representableEquiv R n (ProjectiveSpace.coordinateAlg R i)
        (ProjectiveSpace.chartOver R i ≫ g) =
      Module.Grassmannian.ofChartSection
        (ProjectiveSpace.chartRatioSection R (Equiv.refl (Fin (n + 1))) i)
        (ProjectiveSpace.chartRatioSection_mem R (Equiv.refl _)
          (ProjectiveSpace.chartIndex (Equiv.refl _) i).down i rfl)) :
    g = 𝟙 _ :=
  ProjectiveSpace.eq_id_of_representableEquiv_chartOver R (Equiv.refl _) g h

/-- The term-mode bridge `smul_eq_algebraMap_mul` rewrites scalar actions on standard chart
rings, whose goals elaborate to Mathlib's `HomogeneousLocalization.instSMul`. -/
example (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) (r : R)
    (z : ProjectiveSpace.coordinateRing R (Fin (n + 1)) i) :
    r • z = algebraMap R (ProjectiveSpace.coordinateRing R (Fin (n + 1)) i) r * z := by
  rw [ProjectiveSpace.smul_eq_algebraMap_mul]

end AglibTest.ProjectiveSpaceGrassmannian

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.grassmannianOverIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.grassmannianOverIso

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.grassmannianOverIsoULift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.grassmannianOverIsoULift

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.representableEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.representableEquiv

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.representableEquiv_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.representableEquiv_comp

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.representableIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.representableIso

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.homEquivNatTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.homEquivNatTrans

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.localFunctorRepresentableBy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.localFunctorRepresentableBy

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.homEquivNatTrans_id_app_chartOver' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.homEquivNatTrans_id_app_chartOver

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.awayToSection_chartRatioSection' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.awayToSection_chartRatioSection

/-- info: 'AlgebraicGeometry.ProjectiveSpace.representableEquiv_symm_ofChartSection' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.representableEquiv_symm_ofChartSection

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.eq_id_of_chartOver' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.eq_id_of_chartOver

/-- info: 'AglibTest.ProjectiveSpaceGrassmannian.overlapRight_chartRatioSection' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.ProjectiveSpaceGrassmannian.overlapRight_chartRatioSection

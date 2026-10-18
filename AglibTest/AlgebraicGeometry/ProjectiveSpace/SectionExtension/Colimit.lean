/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension.Colimit

/-! Focused consumer of the description of standard-chart sections as the colimit of morphisms
from negative twists under multiplication by a coordinate ([Stacks, Tag 01PW]; Hartshorne,
II.5.14), with axiom guards. -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

/-- Surjectivity: every chart section is the value of a morphism from every sufficiently negative
twist on the standard chart generator. -/
example {R : Type u} [CommRing R] {ι : Type u} [Finite ι] (M : (ProjectiveSpace R ι).Modules)
    [M.IsQuasicoherent] (i : ι) (s : Γ(M, coordinateOpen R ι i)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ φ : twistingSheaf R ι (-(N : ℤ)) ⟶ M,
      φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι (-(N : ℤ)) i le_rfl) = s :=
  exists_negativeTwistHom_generator_eventually R ι M i s

/-- Compatibility: precomposition with a coordinate power keeps the chart value. -/
example {R : Type u} [CommRing R] {ι : Type u} (M : (ProjectiveSpace R ι).Modules) (i : ι)
    (r N : ℕ) (hN : r ≤ N) (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M) :
    (negativeTwistCoordinatePowerMap R ι i r N hN ≫ φ).val.app (op (coordinateOpen R ι i))
        (twistingGenerator R ι (-(N : ℤ)) i le_rfl) =
      φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι (-(r : ℤ)) i le_rfl) :=
  negativeTwistCoordinatePowerMap_comp_generator M i r N hN φ

/-- Injectivity: the kernel of chart evaluation is killed by coordinate powers. -/
example {R : Type u} [CommRing R] {ι : Type u} [Finite ι] (M : (ProjectiveSpace R ι).Modules)
    [M.IsQuasicoherent] (i : ι) (r : ℕ) (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M) :
    φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι (-(r : ℤ)) i le_rfl) = 0 ↔
      ∃ (N : ℕ) (hN : r ≤ N), negativeTwistCoordinatePowerMap R ι i r N hN ≫ φ = 0 :=
  twistingGenerator_eq_zero_iff_exists_comp_eq_zero M i r φ

/-- On another chart, multiplication by `X_i^{N-r}` is multiplication by `(X_i / X_j)^{N-r}`. -/
example {R : Type u} [CommRing R] {ι : Type u} (i j : ι) (r N : ℕ) (hN : r ≤ N) :
    (negativeTwistCoordinatePowerMap R ι i r N hN).val.app (op (coordinateOpen R ι j))
        (twistingGenerator R ι (-(N : ℤ)) j le_rfl) =
      coordinateRatioSection R ι j i ^ (N - r) • twistingGenerator R ι (-(r : ℤ)) j le_rfl :=
  negativeTwistCoordinatePowerMap_generator_chart R ι i j r N hN

/-- The coordinate-power precompositions form a directed system, linear over any specified
structural ring map. -/
example {R : Type u} [CommRing R] {ι : Type u} (M : (ProjectiveSpace R ι).Modules)
    {A : Type u} [CommRing A] (α : A →+* Γ(ProjectiveSpace R ι, ⊤)) (i : ι) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    DirectedSystem (fun r : ℕ => twistingSheaf R ι (-(r : ℤ)) ⟶ M)
      (negativeTwistHomTransition M α i · · ·) :=
  directedSystem_negativeTwistHomTransition M α i

/-- The chart sections are the direct limit of `Hom(O(-r), M)` along multiplication by `X_i`;
the class of `φ` goes to its value on the chart generator. -/
example {R : Type u} [CommRing R] {ι : Type u} [Finite ι] (M : (ProjectiveSpace R ι).Modules)
    [M.IsQuasicoherent] {A : Type u} [CommRing A] (α : A →+* Γ(ProjectiveSpace R ι, ⊤))
    (i : ι) (r : ℕ) (φ : twistingSheaf R ι (-(r : ℤ)) ⟶ M) :
    letI := Scheme.Modules.moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    negativeTwistHomDirectLimitLinearEquiv M α i
        (Module.DirectLimit.of A ℕ _ (negativeTwistHomTransition M α i) r φ) =
      φ.val.app (op (coordinateOpen R ι i)) (twistingGenerator R ι (-(r : ℤ)) i le_rfl) :=
  negativeTwistHomDirectLimitLinearEquiv_of M α i r φ

/--
info: 'AlgebraicGeometry.ProjectiveSpace.homogeneousChartSection_coordinatePower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.homogeneousChartSection_coordinatePower

/--
info: 'AlgebraicGeometry.ProjectiveSpace.negativeTwistCoordinatePowerMap_generator_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.negativeTwistCoordinatePowerMap_generator_chart

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingHom_eq_zero_of_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingHom_eq_zero_of_generator

/--
info: 'AlgebraicGeometry.ProjectiveSpace.negativeTwistCoordinatePowerMap_comp_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.negativeTwistCoordinatePowerMap_comp_generator

/--
info: 'AlgebraicGeometry.ProjectiveSpace.exists_negativeTwistCoordinatePowerMap_comp_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.exists_negativeTwistCoordinatePowerMap_comp_eq_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingGenerator_eq_zero_iff_exists_comp_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingGenerator_eq_zero_iff_exists_comp_eq_zero

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingHom_ext_of_generator' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingHom_ext_of_generator

/--
info: 'AlgebraicGeometry.ProjectiveSpace.negativeTwistCoordinatePowerMap_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.negativeTwistCoordinatePowerMap_self

/--
info: 'AlgebraicGeometry.ProjectiveSpace.negativeTwistCoordinatePowerMap_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.negativeTwistCoordinatePowerMap_comp

/--
info: 'AlgebraicGeometry.ProjectiveSpace.directedSystem_negativeTwistHomTransition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.directedSystem_negativeTwistHomTransition

/--
info: 'AlgebraicGeometry.ProjectiveSpace.negativeTwistHomDirectLimitLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.negativeTwistHomDirectLimitLinearEquiv

/--
info: 'AlgebraicGeometry.ProjectiveSpace.negativeTwistHomDirectLimitLinearEquiv_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.negativeTwistHomDirectLimitLinearEquiv_of

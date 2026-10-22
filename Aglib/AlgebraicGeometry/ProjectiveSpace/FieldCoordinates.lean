/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.PrincipalOpen
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Original projective coordinates of field-valued points

Every actual field-valued point factors through an original standard chart.
Its chart homomorphism gives coordinates in that same field with one original
coordinate equal to one. A relative point retains its original coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R] {ι : Type u}

/-- The original coordinates extracted from an actual standard-chart ring map. -/
def chartHomCoordinates {A : Type v} [CommRing A] (i : ι)
    (φ : coordinateRing R ι i →+* A) : ι → A :=
  fun j => φ (coordinateRatio R ι i j)

@[simp]
theorem chartHomCoordinates_self {A : Type v} [CommRing A] (i : ι)
    (φ : coordinateRing R ι i →+* A) : chartHomCoordinates i φ i = 1 := by
  simp [chartHomCoordinates]

/-- An actual field-valued point factors through one of its original standard
charts, with the literal original projective morphism recovered. -/
theorem exists_coordinateChart_factorization {K : Type u} [Field K]
    (g : Spec (.of K) ⟶ ProjectiveSpace R ι) :
    ∃ (i : ι) (φ : coordinateRing R ι i →+* K),
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i)
          Nat.zero_lt_one = g := by
  classical
  have hx : g (default : Spec (.of K)) ∈ (⨆ i, coordinateOpen R ι i) := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U := Proj.basicOpen (homogeneousSubmodule ι R) (X i)
  have hrange : Set.range g ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    have hxi : g x ∈ U := by
      simpa only [coordinateOpen, Subsingleton.elim x (default : Spec (.of K))] using hi
    exact ⟨⟨g x, hxi⟩, rfl⟩
  let e := Proj.basicOpenIsoSpec (homogeneousSubmodule ι R) (X i)
    (isHomogeneous_X R i) Nat.zero_lt_one
  let a := IsOpenImmersion.lift U.ι g hrange ≫ e.hom
  refine ⟨i, (Spec.preimage a).hom, ?_⟩
  change Spec.map (Spec.preimage a) ≫ _ = g
  rw [Spec.map_preimage]
  change (IsOpenImmersion.lift U.ι g hrange ≫ e.hom) ≫ (e.inv ≫ U.ι) = g
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact IsOpenImmersion.lift_fac U.ι g hrange

/-- The actual chart homomorphism of a point over the original base retains the
original coefficient algebra and recovers the original projective morphism. -/
theorem exists_coordinateChart_factorization_over {K : Type u} [Field K] [Algebra R K]
    (g : Spec (.of K) ⟶ ProjectiveSpace R ι)
    (hg : g ≫ toSpec R ι = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ (i : ι) (φ : coordinateRing R ι i →+* K),
      φ.comp (coordinateRingCoefficient R ι i) = algebraMap R K ∧
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i)
            Nat.zero_lt_one = g := by
  obtain ⟨i, φ, hφ⟩ := exists_coordinateChart_factorization g
  refine ⟨i, φ, ?_, hφ⟩
  have hc : CommRingCat.ofHom (coordinateRingCoefficient R ι i) ≫
      CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    have ht : Proj.awayι (homogeneousSubmodule ι R) (X i)
        (isHomogeneous_X R i) Nat.zero_lt_one ≫ toSpec R ι =
          Spec.map (CommRingCat.ofHom (coordinateRingCoefficient R ι i)) :=
      coordinateChart_toSpec R ι i
    rw [Spec.map_comp, ← ht, ← Category.assoc, hφ, hg]
  exact congrArg CommRingCat.Hom.hom hc

end AlgebraicGeometry.ProjectiveSpace

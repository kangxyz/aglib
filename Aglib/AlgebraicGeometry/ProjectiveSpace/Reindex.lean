/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Reindexing polynomial projective space over its original base

A coordinate equivalence gives inverse graded polynomial renamings and hence inverse
`Proj.map` morphisms. The resulting isomorphism preserves the actual coefficient map
to `Spec R`. Literal finite coordinates can therefore be lifted to the ring universe
without replacing either the projective scheme or its structural morphism.
-/




@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial
variable (R : Type u) [CommRing R] {ι : Type v} {κ : Type w}

/-- Polynomial renaming preserves the original total-degree homogeneous submodules. -/
def gradedRename (f : ι → κ) : homogeneousSubmodule ι R →+*ᵍ homogeneousSubmodule κ R where
  __ := (rename f).toRingHom
  map_mem hp := hp.rename_isHomogeneous

@[simp] theorem gradedRename_apply (f : ι → κ) (p : MvPolynomial ι R) :
    gradedRename R f p = rename f p := rfl

/-- Inverse coordinate renaming is inverse as an actual graded ring map. -/
@[simp] theorem gradedRename_symm_comp (e : ι ≃ κ) :
    (gradedRename R e.symm).comp (gradedRename R e) = GradedRingHom.id _ := by
  apply GradedRingHom.ext
  intro p
  exact (renameEquiv R e).symm_apply_apply p

/-- Coordinate renaming is inverse to its reverse graded ring map. -/
@[simp] theorem gradedRename_comp_symm (e : ι ≃ κ) :
    (gradedRename R e).comp (gradedRename R e.symm) = GradedRingHom.id _ := by
  apply GradedRingHom.ext
  intro p
  exact (renameEquiv R e).apply_symm_apply p

/-- An equivalence of coordinates maps onto the entire target irrelevant ideal. -/
theorem irrelevant_le_map_gradedRename (e : ι ≃ κ) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule κ R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).map (gradedRename R e) := by
  refine (HomogeneousIdeal.irrelevant_le _).mpr ?_
  intro d hd p hp
  have hm : rename e.symm p ∈ HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hd hp.rename_isHomogeneous
  change p ∈ Ideal.map (rename e).toRingHom
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R)).toIdeal
  rw [← (renameEquiv R e).apply_symm_apply p]
  exact Ideal.mem_map_of_mem (rename e).toRingHom hm
end MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

/-- The coefficient structure map on literal polynomial `Proj`, allowing coordinates
in a smaller universe than the coefficient ring. -/
def polynomialToSpec (R : Type (max u v)) [CommRing R] (ι : Type v) :
    Proj (MvPolynomial.homogeneousSubmodule ι R) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial.homogeneousSubmodule ι R 0)))

/-- At the native common universe this is exactly Aglib's projective structure map. -/
@[simp] theorem polynomialToSpec_eq_toSpec (R : Type u) [CommRing R] (ι : Type u) :
    polynomialToSpec R ι = toSpec R ι := rfl

variable (R : Type (max u v w)) [CommRing R] {ι : Type v} {κ : Type w}

/-- Reindex homogeneous coordinates through the actual inverse graded renamings.
The coefficient universe contains both coordinate universes, so both schemes remain
in the same geometric category. -/
def reindexIso (e : ι ≃ κ) :
    Proj (MvPolynomial.homogeneousSubmodule ι R) ≅
      Proj (MvPolynomial.homogeneousSubmodule κ R) where
  hom := Proj.map (MvPolynomial.gradedRename R e.symm)
    (MvPolynomial.irrelevant_le_map_gradedRename R e.symm)
  inv := Proj.map (MvPolynomial.gradedRename R e)
    (MvPolynomial.irrelevant_le_map_gradedRename R e)
  hom_inv_id := by
    simp only [← Proj.map_comp, MvPolynomial.gradedRename_symm_comp, Proj.map_id]
  inv_hom_id := by
    simp only [← Proj.map_comp, MvPolynomial.gradedRename_comp_symm, Proj.map_id]

/-- Coordinate reindexing preserves the original coefficient structure morphism. -/
@[reassoc] theorem reindexIso_hom_toSpec (e : ι ≃ κ) :
    (reindexIso.{u, v, w} R e).hom ≫ polynomialToSpec.{max u v, w} R κ =
      polynomialToSpec.{max u w, v} R ι := by
  let f := MvPolynomial.gradedRename R e.symm
  let hf := MvPolynomial.irrelevant_le_map_gradedRename R e.symm
  change Proj.map f hf ≫ polynomialToSpec.{max u v, w} R κ =
    polynomialToSpec.{max u w, v} R ι
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change (Σ i : ℕ+, MvPolynomial.homogeneousSubmodule κ R i) at s
  change Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (f s.2)
      (f.map_mem s.2.2) s.1.2 ≫
        (Proj.map f hf ≫ polynomialToSpec.{max u v, w} R κ) =
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (f s.2)
      (f.map_mem s.2.2) s.1.2 ≫ polynomialToSpec.{max u w, v} R ι
  rw [Proj.awayι_comp_map_assoc f hf s.1.2 (s.2 : MvPolynomial κ R) s.2.2]
  simp only [polynomialToSpec, Proj.awayι_toSpecZero_assoc]
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.map, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.map_mk, f, MvPolynomial.gradedRename]

/-- The coordinate comparison as an isomorphism over the original spectrum. -/
def reindexOverIso (e : ι ≃ κ) :
    Over.mk (polynomialToSpec.{max u w, v} R ι) ≅
      Over.mk (polynomialToSpec.{max u v, w} R κ) :=
  Over.isoMk (reindexIso.{u, v, w} R e) (reindexIso_hom_toSpec.{u, v, w} R e)

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveSpace
variable (R : Type u) [CommRing R]

/-- Lift literal finite coordinates to the coefficient universe by an actual `Proj` isomorphism. -/
def finUliftIso (m : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin m) R) ≅
      ProjectiveSpace R (ULift.{u} (Fin m)) :=
  reindexIso.{u, 0, u} R Equiv.ulift.symm

/-- The literal-to-lifted comparison retains the actual map to the original coefficient spectrum. -/
@[reassoc] theorem finUliftIso_hom_toSpec (m : ℕ) :
    (finUliftIso R m).hom ≫ toSpec R (ULift.{u} (Fin m)) = polynomialToSpec.{u, 0} R (Fin m) := by
  exact reindexIso_hom_toSpec.{u, 0, u} R Equiv.ulift.symm

/-- Literal and lifted finite projective spaces are canonically isomorphic
over the original base. -/
def finUliftOverIso (m : ℕ) :
    Over.mk (polynomialToSpec.{u, 0} R (Fin m)) ≅ Over.mk (toSpec R (ULift.{u} (Fin m))) :=
  Over.isoMk (finUliftIso R m) (finUliftIso_hom_toSpec R m)
end AlgebraicGeometry.ProjectiveSpace

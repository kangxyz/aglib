/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.ExactSequences
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Homology.Single
/-!
# Cech augmentation on the opens of a topological space

For a presheaf on topological opens with preadditive coefficients and products,
restriction from the whole space defines the degree-zero Cech augmentation.
The signed first differential annihilates this map. With a zero object, it
extends to a cochain map from the complex concentrated in degree zero and
is natural in the coefficient presheaf.

Extraction source: the general augmentation block of
`R5Lab.AlgebraicGeometry.Curves.Cohomology.CechComparison` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. The construction and component proofs are generalized
  from scheme opens to
topological opens, retaining the original Cech complex and signs.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace Opposite
namespace TopCat.Sheaf.Cech
universe u
section CechAugmentation
open CategoryTheory.Cech HomologicalComplex
universe v
variable (X : TopCat.{u}) {ι : Type u} (U : ι → Opens X)

section General
variable {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]
variable (P : (Opens X)ᵒᵖ ⥤ A)

/-- Restriction of global sections to all degree-zero Cech intersections. -/
def cechAugmentationZero : P.obj (op ⊤) ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  Pi.lift fun _ => P.map (homOfLE le_top).op

@[reassoc (attr := simp)]
theorem cechAugmentationZero_π (a : Fin 1 → ι) :
    cechAugmentationZero X U P ≫
      Pi.π (fun b : Fin 1 → ι => P.obj (op (∏ᶜ fun i => U (b i)))) a =
        P.map (homOfLE le_top).op := by
  exact Pi.lift_comp_π _ a

theorem cechAugmentationZero_d :
    cechAugmentationZero X U P ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 := by
  apply Pi.hom_ext (f := fun b : Fin 2 → ι => P.obj (op (∏ᶜ fun i => U (b i))))
  intro a
  change (cechAugmentationZero X U P ≫ ((cechComplexFunctor U).obj P).d 0 1) ≫
    Pi.π (fun b : Fin 2 → ι => P.obj (op (∏ᶜ fun i => U (b i)))) a = 0 ≫ _
  rw [Category.assoc, cech_d_comp_π]
  have ht (j : Fin 2) :
      cechAugmentationZero X U P ≫
        (Pi.π (fun b : Fin 1 → ι => P.obj (op (∏ᶜ fun i => U (b i))))
          (fun k => a (j.succAbove k)) ≫
        P.map (Pi.lift (fun k => Pi.π (fun i => U (a i)) (j.succAbove k))).op) =
          P.map (homOfLE le_top).op := by
    rw [← Category.assoc]
    erw [cechAugmentationZero_π]
    rw [← P.map_comp]
    rfl
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ht, zero_comp]
  erw [Fin.sum_univ_two]
  simp

variable [HasZeroObject A]

/-- The cochain augmentation of global sections into the Cech complex. -/
def cechAugmentation : (CochainComplex.single₀ A).obj (P.obj (op ⊤)) ⟶
    (cechComplexFunctor U).obj P :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨cechAugmentationZero X U P, cechAugmentationZero_d X U P⟩

@[simp] theorem cechAugmentation_f_zero :
    (cechAugmentation X U P).f 0 = cechAugmentationZero X U P := by
  simp [cechAugmentation]

theorem cechAugmentation_naturality {P Q : (Opens X)ᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (CochainComplex.single₀ A).map (f.app (op ⊤)) ≫ cechAugmentation X U Q =
      cechAugmentation X U P ≫ (cechComplexFunctor U).map f := by
  apply from_single_hom_ext
  simp only [comp_f, CochainComplex.single₀_map_f_zero, cechAugmentation_f_zero]
  apply Pi.hom_ext (f := fun b : Fin 1 → ι => Q.obj (op (∏ᶜ fun i => U (b i))))
  intro a
  change (f.app (op ⊤) ≫ cechAugmentationZero X U Q) ≫
    Pi.π (fun b : Fin 1 → ι => Q.obj (op (∏ᶜ fun i => U (b i)))) a =
      (cechAugmentationZero X U P ≫ Limits.Pi.map
        (fun b : Fin 1 → ι => f.app (op (∏ᶜ fun i => U (b i))))) ≫ _
  simp only [Category.assoc, Pi.map_π]
  erw [cechAugmentationZero_π]
  rw [← Category.assoc]
  erw [cechAugmentationZero_π]
  exact (f.naturality _).symm

end General

end CechAugmentation

end TopCat.Sheaf.Cech

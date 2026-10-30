/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cech.Augmentation
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Scheme views of the original Cech augmentation

The construction is the topological augmentation on the original Cech complex.
These transparent views retain the Scheme API and its literal component maps.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.CechComparison` at
R5Lab revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u v
open CategoryTheory.Cech HomologicalComplex
variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]
  (P : X.Opensᵒᵖ ⥤ A)

/-- Restriction of global sections to all degree-zero Cech intersections. -/
abbrev cechAugmentationZero := TopCat.Sheaf.Cech.cechAugmentationZero X.toTopCat U P

@[reassoc]
theorem cechAugmentationZero_π (a : Fin 1 → ι) :
    cechAugmentationZero X U P ≫
      Pi.π (fun b : Fin 1 → ι => P.obj (op (∏ᶜ fun i => U (b i)))) a =
        P.map (homOfLE le_top).op :=
  TopCat.Sheaf.Cech.cechAugmentationZero_π X.toTopCat U P a

theorem cechAugmentationZero_d :
    cechAugmentationZero X U P ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 :=
  TopCat.Sheaf.Cech.cechAugmentationZero_d X.toTopCat U P

variable [HasZeroObject A]

/-- The original cochain augmentation is the topological construction. -/
abbrev cechAugmentation := TopCat.Sheaf.Cech.cechAugmentation X.toTopCat U P

theorem cechAugmentation_f_zero :
    (cechAugmentation X U P).f 0 = cechAugmentationZero X U P :=
  TopCat.Sheaf.Cech.cechAugmentation_f_zero X.toTopCat U P

theorem cechAugmentation_naturality {P Q : X.Opensᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (CochainComplex.single₀ A).map (f.app (op ⊤)) ≫ cechAugmentation X U Q =
      cechAugmentation X U P ≫ (cechComplexFunctor U).map f :=
  TopCat.Sheaf.Cech.cechAugmentation_naturality X.toTopCat U f

end AlgebraicGeometry.Scheme.Cohomology

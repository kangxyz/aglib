/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Values
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Point
public import Aglib.AlgebraicGeometry.Cohomology.Group.Augmentation
public import Aglib.Algebra.Graded.TensorProduct.PointMaps

/-!
# Whole point laws for the original total Kunneth operator

The original augmentation and unrestricted pullback along a point give both
whole tensor-unit diagrams. The point section is not required to be flat.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The complete left point diagram uses the original augmentation and no flat point. -/
theorem structureExternalLinearMap_point_left_diagram (X Y : FScheme k)
    [IsProper X.hom] [GeometricallyIntegral X.hom] (e : 𝟙_ (FScheme k) ⟶ X) :
    @DirectSum.tensorPointLeftDiagram k
      ‹Field k›
      (structureCohomology k X) (structureCohomology k Y)
      (structureCohomology k (X ⊗ Y))
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k X n)).toAddCommMonoid)
      (structureCohomologyModule X)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k Y n)).toAddCommMonoid)
      (structureCohomologyModule Y)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k (X ⊗ Y) n)).toAddCommMonoid)
      (structureCohomologyModule (X ⊗ Y))
      (@structureExternalCup k ‹Field k› X Y)
      (@structureCohomologyPullbackLinear k ‹Field k› Y (X ⊗ Y)
      (lift (C := FScheme k) (T := Y) (X := X) (Y := Y) (toUnit Y ≫ e) (𝟙 Y)))
      (structureCohomologyAugmentationLinear X) := by
  refine @DirectSum.tensorPointLeftDiagramOfValues k
    ‹Field k›
    (structureCohomology k X) (structureCohomology k Y)
    (structureCohomology k (X ⊗ Y))
    (fun n => (inferInstance :
      AddCommGroup (structureCohomology k X n)).toAddCommMonoid)
    (structureCohomologyModule X)
    (fun n => (inferInstance :
      AddCommGroup (structureCohomology k Y n)).toAddCommMonoid)
    (structureCohomologyModule Y)
    (fun n => (inferInstance :
      AddCommGroup (structureCohomology k (X ⊗ Y) n)).toAddCommMonoid)
    (structureCohomologyModule (X ⊗ Y))
    (@structureExternalCup k ‹Field k› X Y)
    (@structureCohomologyPullbackLinear k ‹Field k› Y (X ⊗ Y)
      (lift (C := FScheme k) (T := Y) (X := X) (Y := Y) (toUnit Y ≫ e) (𝟙 Y)))
    (structureCohomologyAugmentationLinear X)
    (fun x => (structureH0ScalarEquiv X).symm x)
    (fun _ => rfl) ?_ ?_
  · as_aux_lemma =>
      let kField : Field k := ‹Field k›
      have hProper : IsProper X.hom := ‹IsProper X.hom›
      have hIntegral : GeometricallyIntegral X.hom :=
        ‹GeometricallyIntegral X.hom›
      exact fun (n : ℕ) (x : structureCohomology k X 0)
          (y : structureCohomology k Y n) =>
        @structureExternalCup_point_left_zero k kField X Y
          hProper hIntegral e n x y
  · as_aux_lemma =>
      let kField : Field k := ‹Field k›
      exact fun (p q : ℕ) (x : structureCohomology k X (p + 1))
          (y : structureCohomology k Y (q)) =>
        @structureExternalCup_point_left_succ k kField X Y e
          p q (p + 1 + q) rfl x y

/-- The complete right point diagram is the original other counit diagram. -/
theorem structureExternalLinearMap_point_right_diagram (X Y : FScheme k)
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (e : 𝟙_ (FScheme k) ⟶ Y) :
    @DirectSum.tensorPointRightDiagram k
      ‹Field k›
      (structureCohomology k X) (structureCohomology k Y)
      (structureCohomology k (X ⊗ Y))
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k X n)).toAddCommMonoid)
      (structureCohomologyModule X)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k Y n)).toAddCommMonoid)
      (structureCohomologyModule Y)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k (X ⊗ Y) n)).toAddCommMonoid)
      (structureCohomologyModule (X ⊗ Y))
      (@structureExternalCup k ‹Field k› X Y)
      (@structureCohomologyPullbackLinear k ‹Field k› X (X ⊗ Y)
      (lift (C := FScheme k) (T := X) (X := X) (Y := Y) (𝟙 X) (toUnit X ≫ e)))
      (structureCohomologyAugmentationLinear Y) := by
  refine @DirectSum.tensorPointRightDiagramOfValues k
    ‹Field k›
    (structureCohomology k X) (structureCohomology k Y)
    (structureCohomology k (X ⊗ Y))
    (fun n => (inferInstance :
      AddCommGroup (structureCohomology k X n)).toAddCommMonoid)
    (structureCohomologyModule X)
    (fun n => (inferInstance :
      AddCommGroup (structureCohomology k Y n)).toAddCommMonoid)
    (structureCohomologyModule Y)
    (fun n => (inferInstance :
      AddCommGroup (structureCohomology k (X ⊗ Y) n)).toAddCommMonoid)
    (structureCohomologyModule (X ⊗ Y))
    (@structureExternalCup k ‹Field k› X Y)
    (@structureCohomologyPullbackLinear k ‹Field k› X (X ⊗ Y)
      (lift (C := FScheme k) (T := X) (X := X) (Y := Y) (𝟙 X) (toUnit X ≫ e)))
    (structureCohomologyAugmentationLinear Y)
    (fun y => (structureH0ScalarEquiv Y).symm y)
    (fun _ => rfl) ?_ ?_
  · as_aux_lemma =>
      let kField : Field k := ‹Field k›
      have hProper : IsProper Y.hom := ‹IsProper Y.hom›
      have hIntegral : GeometricallyIntegral Y.hom :=
        ‹GeometricallyIntegral Y.hom›
      exact fun (n : ℕ) (x : structureCohomology k X n)
          (y : structureCohomology k Y 0) =>
        @structureExternalCup_point_right_zero k kField X Y
          hProper hIntegral e n x y
  · as_aux_lemma =>
      let kField : Field k := ‹Field k›
      exact fun (p q : ℕ) (x : structureCohomology k X (p))
          (y : structureCohomology k Y (q + 1)) =>
        @structureExternalCup_point_right_succ k kField X Y e
          p q (p + (q + 1)) rfl x y

/-- The left point law in terms of the original total linear maps. -/
abbrev structureExternalLinearMapPointLeft (X Y : FScheme k)
    [IsProper X.hom] [GeometricallyIntegral X.hom] (e : 𝟙_ (FScheme k) ⟶ X) :=
  let diagram := structureExternalLinearMap_point_left_diagram X Y e
  DirectSum.tensorPointLeftDiagramWithTotals diagram (structureExternalLinearMap X Y)
    (structureCohomologyAlgebraPullbackLinear (lift (toUnit Y ≫ e) (𝟙 Y))) rfl rfl

/-- The right point law in terms of the original total linear maps. -/
abbrev structureExternalLinearMapPointRight (X Y : FScheme k)
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (e : 𝟙_ (FScheme k) ⟶ Y) :=
  let diagram := structureExternalLinearMap_point_right_diagram X Y e
  DirectSum.tensorPointRightDiagramWithTotals diagram (structureExternalLinearMap X Y)
    (structureCohomologyAlgebraPullbackLinear (lift (𝟙 X) (toUnit X ≫ e))) rfl rfl

/-- The left point equation for the original total external product. -/
theorem structureExternalLinearMap_point_left (X Y : FScheme k)
    [IsProper X.hom] [GeometricallyIntegral X.hom] (e : 𝟙_ (FScheme k) ⟶ X) :
    type_of% (structureExternalLinearMapPointLeft X Y e) :=
  structureExternalLinearMapPointLeft X Y e

/-- The right point equation for the original total external product. -/
theorem structureExternalLinearMap_point_right (X Y : FScheme k)
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (e : 𝟙_ (FScheme k) ⟶ Y) :
    type_of% (structureExternalLinearMapPointRight X Y e) :=
  structureExternalLinearMapPointRight X Y e

end AlgebraicGeometry.Scheme.Cohomology

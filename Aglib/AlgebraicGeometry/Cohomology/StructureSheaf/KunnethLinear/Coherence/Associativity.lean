/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethLinear.Values
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup.PullbackLinear
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Coherence
public import Aglib.Algebra.Graded.TensorProduct.CoherenceInputs

/-!
# Associativity of the original total Kunneth operator

The chosen native operator has the original homogeneous values, product
naturality and associativity. Original unrestricted pullback laws are imported
from their lower owner before group coalgebra assembly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y Z : FScheme k)

/-- The original geometric associator with its source and target fixed. -/
abbrev originalAssociatorHom :
    ((X ⊗ Y) ⊗ Z) ⟶ X ⊗ (Y ⊗ Z) :=
  (@MonoidalCategoryStruct.associator (FScheme k) inferInstance inferInstance X Y Z).hom

/-- The original degreewise pullbacks along the fixed geometric associator. -/
abbrev originalAssociatorPullback :=
  fun n => structureCohomologyPullbackLinear (originalAssociatorHom X Y Z) n

/-- The original four cup families and geometric associator compatibility as one typed input. -/
def structureExternalAssociativityInputs :
    @DirectSum.AssociativityInputs k
      ‹Field k›
      (structureCohomology k X) (structureCohomology k Y) (structureCohomology k Z)
      (structureCohomology k (X ⊗ Y)) (structureCohomology k (Y ⊗ Z))
      (structureCohomology k (X ⊗ (Y ⊗ Z)))
      (structureCohomology k ((X ⊗ Y) ⊗ Z))
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k X n)).toAddCommMonoid)
      (structureCohomologyModule X)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k Y n)).toAddCommMonoid)
      (structureCohomologyModule Y)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k Z n)).toAddCommMonoid)
      (structureCohomologyModule Z)
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k (X ⊗ Y) n)).toAddCommMonoid)
      (structureCohomologyModule (X ⊗ Y))
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k (Y ⊗ Z) n)).toAddCommMonoid)
      (structureCohomologyModule (Y ⊗ Z))
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k (X ⊗ (Y ⊗ Z)) n)).toAddCommMonoid)
      (structureCohomologyModule (X ⊗ (Y ⊗ Z)))
      (fun n => (inferInstance :
        AddCommGroup (structureCohomology k ((X ⊗ Y) ⊗ Z) n)).toAddCommMonoid)
      (structureCohomologyModule ((X ⊗ Y) ⊗ Z)) where
  cupMN := @structureExternalCup k ‹Field k› X Y
  cupPO := @structureExternalCup k ‹Field k› (X ⊗ Y) Z
  cupNO := @structureExternalCup k ‹Field k› Y Z
  cupMQ := @structureExternalCup k ‹Field k› X (Y ⊗ Z)
  pullback := @originalAssociatorPullback k ‹Field k› X Y Z
  compatibility := by
    as_aux_lemma =>
      let kField : Field k := ‹Field k›
      exact fun (i j r : ℕ) (x : structureCohomology k X i)
          (y : structureCohomology k Y j) (z : structureCohomology k Z r) =>
        @structureExternalCup_assoc k kField X Y Z
          i j r (i + j) (j + r) (i + j + r) rfl rfl rfl x y z

/-- The associator pullback assembled from its original degreewise components. -/
theorem structureExternalAssociativityInputs_totalPullback :
    structureCohomologyAlgebraPullbackLinear (originalAssociatorHom X Y Z) =
      DirectSum.lmap (structureExternalAssociativityInputs X Y Z).pullback := rfl

/-- The whole tensor associativity diagram is the original external-cup associativity. -/
abbrev structureExternalLinearMap_assoc :=
  let input := @structureExternalAssociativityInputs k ‹Field k› X Y Z
  let pullback := structureCohomologyAlgebraPullbackLinear (originalAssociatorHom X Y Z)
  let hp := structureExternalAssociativityInputs_totalPullback X Y Z
  DirectSum.AssociativityInputs.diagramWithMaps input
    (structureExternalLinearMap X Y) (structureExternalLinearMap (X ⊗ Y) Z)
    (structureExternalLinearMap Y Z) (structureExternalLinearMap X (Y ⊗ Z))
    pullback rfl rfl rfl rfl hp

end AlgebraicGeometry.Scheme.Cohomology

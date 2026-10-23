/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSliceTopology
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.ExtComparison
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Original cohomology on the small-etale slice

The actual sheaf equivalence carries the constant integer source to the
constant integer source by the original constant-sheaf adjunction. The exact
adjunction comparison then identifies original `Sheaf.H`, at the stated value
and Ext universes. No replacement cohomology or Galois comparison is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w₁ w₂

variable {X : Scheme.{u}} (U : X.Etale)

instance sliceSheafEquivalence_functor_additive :
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{v}).functor.Additive where
  map_add := by intros; rfl

instance sliceSheafEquivalence_inverse_additive :
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{v}).inverse.Additive where
  map_add := by intros; rfl

variable [HasSheafify ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{v}]
  [HasSheafify (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{v}]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original constant-sheaf source commutes with the actual slice equivalence. -/
def sliceConstantSheafIso :
    constantSheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{v} ⋙
      (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{v}).functor ≅
        constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{v} :=
  ((constantSheafAdj ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{v}
      Over.mkIdTerminal).comp
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{v}).toAdjunction).leftAdjointUniq
      (constantSheafAdj (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{v}
        (MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) U.left))

variable [HasExt.{w₁} (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{v})]
  [HasExt.{w₂} (Sheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{v})]

/-- Original cohomology of a chart equals original cohomology on the etale
slice, with the actual restriction coefficient supplied by the sheaf equivalence. -/
def sliceCohomologyEquiv
    (A : Sheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{v}) (n : ℕ) :
    Sheaf.H.{w₂} A n ≃+
      Sheaf.H.{w₁} ((Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{v}).inverse.obj A) n :=
  (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{v}).toAdjunction.sourceExtComparison
    ((sliceConstantSheafIso U).app (AddCommGrpCat.of (ULift.{v} ℤ))) A n

end AlgebraicGeometry.Scheme.EtaleCohomology

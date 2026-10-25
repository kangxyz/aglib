/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.AffineIntegralConstants.SheafColimit

/-! # Original finite-stage maps through an actual containing subalgebra

The actual subalgebra inclusion maps define the relative scheme maps. Their
composite is the original finite-stage cone leg, so the literal finite-constant
pushforward transitions compose to the original cocone leg. This keeps each
original affine finite-stage factor when it enters one global generated algebra.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

attribute [local instance] hasSheafifyLarge

open AffineIntegralConstants

private theorem map_op_cone_leg_of_comp
    {C D : Type*} [Category* C] [Category* D] (P : Cᵒᵖ ⥤ D)
    {I : Type*} [Category* I] {F : I ⥤ C} (c : Cone F) (k : I)
    {T : C} (a : c.pt ⟶ T) (b : T ⟶ F.obj k) (h : a ≫ b = c.π.app k) :
    P.map b.op ≫ P.map a.op = (P.mapCocone c.op).ι.app (op k) :=
  (P.map_comp b.op a.op).symm.trans (congrArg (fun z => P.map z.op) h)

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The original inclusion of an actual subalgebra, as a relative scheme map. -/
def subalgebraOverMap (C : Subalgebra R A) :
    Over.mk (Spec.algebraMap R A) ⟶ Over.mk (Spec.algebraMap R C) :=
  Over.homMk (Spec.map (CommRingCat.ofHom C.val.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1)

/-- The original inclusion of a finite-generated stage into its actual
containing subalgebra, as a relative scheme map. -/
def stageIntoSubalgebraOverMap (C : Subalgebra R A) (s : Finset A)
    (h : Algebra.FiniteTypeSubalgebraLimit.stage R A s ≤ C) :
    Over.mk (Spec.algebraMap R C) ⟶
      Over.mk (Spec.algebraMap R (Algebra.FiniteTypeSubalgebraLimit.stage R A s)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1)

/-- The composite of the original inclusion maps is the original cone leg. -/
theorem subalgebraOverMap_stageIntoSubalgebraOverMap
    (C : Subalgebra R A) (s : Finset A)
    (h : Algebra.FiniteTypeSubalgebraLimit.stage R A s ≤ C) :
    subalgebraOverMap R A C ≫ stageIntoSubalgebraOverMap R A C s h =
      (Scheme.FiniteTypeSubalgebraLimit.baseCone R A).π.app (op s) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom C.val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (Algebra.FiniteTypeSubalgebraLimit.stage R A s).val.toRingHom)
  rw [← Spec.map_comp]
  congr 1

/-- Original finite-constant transitions through a containing subalgebra
compose to the original finite-stage constant cocone arrow. -/
theorem subalgebra_stage_pushforward_map
    (B : Type u) [AddCommGroup B] [Finite B] (C : Subalgebra R A) (s : Finset A)
    (h : Algebra.FiniteTypeSubalgebraLimit.stage R A s ≤ C) :
    (constantPushforwardFunctor (X := Spec (.of R)) B).map
        (stageIntoSubalgebraOverMap R A C s h).op ≫
      (constantPushforwardFunctor (X := Spec (.of R)) B).map (subalgebraOverMap R A C).op =
      (constantPushforwardCocone R A B).ι.app (op (op s)) := by
  exact map_op_cone_leg_of_comp (constantPushforwardFunctor (X := Spec (.of R)) B)
    (Scheme.FiniteTypeSubalgebraLimit.baseCone R A) (op s)
    (subalgebraOverMap R A C) (stageIntoSubalgebraOverMap R A C s h)
    (subalgebraOverMap_stageIntoSubalgebraOverMap R A C s h)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

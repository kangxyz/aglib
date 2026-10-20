/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric-point injectivity detects an integral separated retraction

A right inverse of a morphism of schemes over a field is also a left inverse
when the source is integral and separated over the field and the morphism is
injective on all algebraically closed field-valued points. The proof tests at
an algebraic closure of the source function field and then uses equality of
scheme morphisms on a dominant map into a reduced source. In particular, it
does not infer scheme isomorphism merely from a bijection of geometric points.

Provenance: the reusable retraction step for `K2-018#prop:k2018-arithmetic-characters`
and `K2-018#lem:k2018-geometric-exact-order`, mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`. This file formalizes only the
stated general retraction lemma, not the Picard/Abel construction or either
whole mathematical claim. Frozen engineering basis:
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`; mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, using its proved
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`. No external theorem
family is retained as a premise.
-/


/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/



@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Hom.GeometricRetraction

/-- The actual geometric generic point, formed by extending the function field
of an integral scheme to its same-universe algebraic closure. -/
noncomputable def geometricGenericPoint (X : Scheme.{u}) [IsIntegral X] :
    Spec (CommRingCat.of (AlgebraicClosure X.functionField)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField (AlgebraicClosure X.functionField))) ≫
    X.fromSpecStalk (genericPoint X)

/-- The geometric generic point is dominant: its image contains the generic point. -/
theorem isDominant_geometricGenericPoint (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (geometricGenericPoint X) := by
  have : IsDominant (X.fromSpecStalk (genericPoint X)) := by
    refine ⟨?_⟩
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
      ← (genericPoint_spec X)]
    apply closure_mono
    rintro x rfl
    exact ⟨IsLocalRing.closedPoint _, X.fromSpecStalk_closedPoint⟩
  unfold geometricGenericPoint
  infer_instance

variable {F : Type u} [Field F]
  {X Y : Over (Spec (CommRingCat.of F))} [IsIntegral X.left] [IsSeparated X.hom]

/-- A scheme retraction onto an integral separated source is the identity if
postcomposition is injective on all algebraically closed field-valued points.
The structural field morphism is arbitrary, not a fixed algebra structure. -/
theorem retraction_comp_eq_id_of_geometric_injective
    (f : X ⟶ Y) (j : Y ⟶ X) (hj : j ≫ f = 𝟙 Y)
    (hinj : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (k : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F)),
      Function.Injective (fun x : Over.mk k ⟶ X => x ≫ f)) :
    f ≫ j = 𝟙 X := by
  let K := AlgebraicClosure X.left.functionField
  let z : Spec (CommRingCat.of K) ⟶ X.left := geometricGenericPoint X.left
  let k : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) := z ≫ X.hom
  let z' : Over.mk k ⟶ X := Over.homMk z
  have hzf : (z' ≫ f ≫ j) ≫ f = z' ≫ f := by simp [Category.assoc, hj]
  have hz : z' ≫ f ≫ j = z' := hinj K k hzf
  have hzleft : z ≫ (f ≫ j).left = z ≫ (𝟙 X : X ⟶ X).left := by
    simpa [z', Over.comp_left, Category.assoc] using
      congrArg (fun q => q.left) hz
  have : IsDominant z := isDominant_geometricGenericPoint X.left
  ext1
  apply ext_of_isDominant_of_isSeparated X.hom
    ((Over.w (f ≫ j)).trans (Over.w (𝟙 X)).symm) z hzleft

/-- A morphism with a right inverse is an isomorphism under the same integral,
separated, and full geometric-point injectivity hypotheses. -/
theorem isIso_of_retraction_of_geometric_injective
    (f : X ⟶ Y) (j : Y ⟶ X) (hj : j ≫ f = 𝟙 Y)
    (hinj : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (k : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F)),
      Function.Injective (fun x : Over.mk k ⟶ X => x ≫ f)) : IsIso f :=
  ⟨⟨j, retraction_comp_eq_id_of_geometric_injective f j hj hinj, hj⟩⟩

end AlgebraicGeometry.Scheme.Hom.GeometricRetraction

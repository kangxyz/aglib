/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Group.Connected
public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology

/-!
# Evaluation of the original external product at a rational point

Positive-degree classes vanish after restricting to an affine neighborhood
of the point. Only that open restriction is used for flat cup naturality;
the final pullback along the point itself uses unrestricted original
cohomology composition. A rational point is never assumed flat.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)

private theorem rationalPoint_factors_affine (e : 𝟙_ (FScheme k) ⟶ X) :
    ∃ (U : FScheme k) (i : U ⟶ X) (e' : 𝟙_ (FScheme k) ⟶ U),
      IsAffine U.left ∧ IsOpenImmersion i.left ∧ e' ≫ i = e := by
  let : Subsingleton (𝟙_ (FScheme k)).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  let C := X.left.affineCover
  let j := C.idx (e.left (IsLocalRing.closedPoint k))
  let U : FScheme k := Over.mk (C.f j ≫ X.hom)
  have h : Set.range e.left ⊆ Set.range (C.f j) := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hx]
    exact C.covers _
  let i : U ⟶ X := Over.homMk (C.f j) rfl
  let e' : 𝟙_ (FScheme k) ⟶ U :=
    Over.homMk (IsOpenImmersion.lift (C.f j) e.left h) (by
      change IsOpenImmersion.lift (C.f j) e.left h ≫ (C.f j ≫ X.hom) = 𝟙 _
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact e.w)
  refine ⟨U, i, e', inferInstanceAs (IsAffine (X.left.affineCover.X j)),
    inferInstanceAs (IsOpenImmersion (X.left.affineCover.f j)), ?_⟩
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (C.f j) e.left h

/-- Evaluating the first factor at a rational point kills every positive
first-factor degree, without flatness of that point. -/
theorem structureExternalCup_point_left_succ (e : 𝟙_ (FScheme k) ⟶ X)
    {p q n : ℕ} (h : p + 1 + q = n)
    (x : structureCohomology k X (p + 1)) (y : structureCohomology k Y q) :
    structureCohomologyPullbackLinear (lift (toUnit Y ≫ e) (𝟙 Y)) n
      (structureExternalCup X Y h x y) = 0 := by
  obtain ⟨U, i, e', hU, hi, he⟩ := rationalPoint_factors_affine X e
  let := hU
  let := hi
  let l : Y ⟶ U ⊗ Y := lift (toUnit Y ≫ e') (𝟙 Y)
  have hf : l ≫ (i ⊗ₘ 𝟙 Y) = lift (toUnit Y ≫ e) (𝟙 Y) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [l, Category.assoc, he]
  let : Subsingleton (structureCohomology k U (p + 1)) :=
    structureCohomology_subsingleton_of_isAffine U p
  have hz : structureCohomologyPullbackLinear i (p + 1) x = 0 := Subsingleton.elim _ _
  rw [← hf, structureCohomologyPullbackLinear_comp, LinearMap.comp_apply,
    structureExternalCup_naturality i (𝟙 Y) h x y, hz]
  simp only [LinearMap.map_zero, LinearMap.zero_apply]

/-- The scalar-unit term evaluates to the original scalar multiple of the
second class at every rational point, again with no flatness premise. -/
theorem structureExternalCup_point_left_scalar (e : 𝟙_ (FScheme k) ⟶ X)
    (a : k) {n : ℕ} (y : structureCohomology k Y n) :
    structureCohomologyPullbackLinear (lift (toUnit Y ≫ e) (𝟙 Y)) n
      (structureExternalCup X Y (Nat.zero_add n) (a • structureCupUnit X) y) = a • y := by
  rw [LinearMap.map_smul, LinearMap.smul_apply, structureExternalCup_unit_left,
    LinearMap.map_smul]
  have h := LinearMap.congr_fun
    (structureCohomologyPullbackLinear_comp (snd X Y)
      (lift (toUnit Y ≫ e) (𝟙 Y)) n) y
  simpa only [lift_snd, structureCohomologyPullbackLinear_id, LinearMap.id_apply,
    LinearMap.comp_apply] using congrArg (a • ·) h.symm

/-- Proper geometric integrality identifies the degree-zero coefficient
with the actual inverse structural-scalar map. -/
theorem structureExternalCup_point_left_zero [IsProper X.hom] [GeometricallyIntegral X.hom]
    (e : 𝟙_ (FScheme k) ⟶ X) {n : ℕ}
    (x : structureCohomology k X 0) (y : structureCohomology k Y n) :
    structureCohomologyPullbackLinear (lift (toUnit Y ≫ e) (𝟙 Y)) n
      (structureExternalCup X Y (Nat.zero_add n) x y) =
        (structureH0ScalarEquiv X).symm x • y := by
  obtain ⟨a, rfl⟩ := (structureH0ScalarEquiv X).surjective x
  rw [LinearEquiv.symm_apply_apply, structureH0ScalarEquiv_apply]
  exact structureExternalCup_point_left_scalar X Y e a y

/-- Evaluating the second factor kills its positive degrees by the same
actual affine restriction argument. -/
theorem structureExternalCup_point_right_succ (e : 𝟙_ (FScheme k) ⟶ Y)
    {p q n : ℕ} (h : p + (q + 1) = n)
    (x : structureCohomology k X p) (y : structureCohomology k Y (q + 1)) :
    structureCohomologyPullbackLinear (lift (𝟙 X) (toUnit X ≫ e)) n
      (structureExternalCup X Y h x y) = 0 := by
  obtain ⟨U, i, e', hU, hi, he⟩ := rationalPoint_factors_affine Y e
  let := hU
  let := hi
  let l : X ⟶ X ⊗ U := lift (𝟙 X) (toUnit X ≫ e')
  have hf : l ≫ (𝟙 X ⊗ₘ i) = lift (𝟙 X) (toUnit X ≫ e) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [l, Category.assoc, he]
  let : Subsingleton (structureCohomology k U (q + 1)) :=
    structureCohomology_subsingleton_of_isAffine U q
  have hz : structureCohomologyPullbackLinear i (q + 1) y = 0 := Subsingleton.elim _ _
  rw [← hf, structureCohomologyPullbackLinear_comp, LinearMap.comp_apply,
    structureExternalCup_naturality (𝟙 X) i h x y, hz]
  simp only [LinearMap.map_zero]

/-- The right scalar-unit term evaluates to the original scalar multiple
of the first class at every rational point. -/
theorem structureExternalCup_point_right_scalar (e : 𝟙_ (FScheme k) ⟶ Y)
    (a : k) {n : ℕ} (x : structureCohomology k X n) :
    structureCohomologyPullbackLinear (lift (𝟙 X) (toUnit X ≫ e)) n
      (structureExternalCup X Y (Nat.add_zero n) x (a • structureCupUnit Y)) = a • x := by
  rw [LinearMap.map_smul, structureExternalCup_unit_right, LinearMap.map_smul]
  have h := LinearMap.congr_fun
    (structureCohomologyPullbackLinear_comp (fst X Y)
      (lift (𝟙 X) (toUnit X ≫ e)) n) x
  simpa only [lift_fst, structureCohomologyPullbackLinear_id, LinearMap.id_apply,
    LinearMap.comp_apply] using congrArg (a • ·) h.symm

/-- The right degree-zero formula uses the actual proper H0 scalar comparison. -/
theorem structureExternalCup_point_right_zero [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (e : 𝟙_ (FScheme k) ⟶ Y) {n : ℕ}
    (x : structureCohomology k X n) (y : structureCohomology k Y 0) :
    structureCohomologyPullbackLinear (lift (𝟙 X) (toUnit X ≫ e)) n
      (structureExternalCup X Y (Nat.add_zero n) x y) =
        (structureH0ScalarEquiv Y).symm y • x := by
  obtain ⟨a, rfl⟩ := (structureH0ScalarEquiv Y).surjective y
  rw [LinearEquiv.symm_apply_apply, structureH0ScalarEquiv_apply]
  exact structureExternalCup_point_right_scalar X Y e a x

end AlgebraicGeometry.Scheme.Cohomology

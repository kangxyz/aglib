/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineComplement
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Coordinates of rational points on the literal cubic

Source: ordinary R5 Weierstrass.Points, lines 72–231.
Evaluation and the original affine and infinity maps are explicit.
These are set maps; addition compatibility is a separate input.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
namespace WeierstrassCurve.Projective
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type u} [Field k]

/-- Evaluation of the affine Weierstrass coordinate ring at coordinates satisfying its equation. -/
def affinePointEval (W : WeierstrassCurve k) (x y : k) (h : W.toAffine.Equation x y) :
    affineRing W →+* k :=
  AdjoinRoot.lift (Polynomial.evalRingHom x) y (by
    simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_evalRingHom,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    convert (WeierstrassCurve.Affine.equation_iff' _ _).mp h using 1; ring)

@[simp] theorem affinePointEval_x (W : WeierstrassCurve k) (x y : k)
    (h : W.toAffine.Equation x y) : affinePointEval W x y h (affineX W) = x := by
  simp [affinePointEval, affineX, AdjoinRoot.lift_of]

@[simp] theorem affinePointEval_y (W : WeierstrassCurve k) (x y : k)
    (h : W.toAffine.Equation x y) : affinePointEval W x y h (affineY W) = y := by
  simp [affinePointEval, affineY, AdjoinRoot.lift_root]

@[simp] theorem affinePointEval_constant (W : WeierstrassCurve k) (x y : k)
    (h : W.toAffine.Equation x y) (a : k) :
    affinePointEval W x y h (algebraMap k (affineRing W) a) = a := by
  change affinePointEval W x y h (AdjoinRoot.of _ (Polynomial.C a)) = a
  simp [affinePointEval, AdjoinRoot.lift_of]

lemma affinePointEval_structure (W : WeierstrassCurve k) (x y : k)
    (h : W.toAffine.Equation x y) :
    (affinePointEval W x y h).comp (algebraMap k (affineRing W)) = RingHom.id k := by
  ext a
  exact affinePointEval_constant W x y h a

/-- The actual rational affine point, with its k-morphism condition proved. -/
def affinePointOver (W : WeierstrassCurve k) (x y : k) (h : W.toAffine.Equation x y) :
    𝟙_ (FScheme k) ⟶ affineOver W :=
  Over.homMk (Spec.map (CommRingCat.ofHom (affinePointEval W x y h))) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of k))
    rw [← Spec.map_comp]
    convert Spec.map_id (.of k) using 1
    exact congrArg (fun f : k →+* k => Spec.map (CommRingCat.ofHom f))
      (affinePointEval_structure W x y h))

/-- Canonical actual scheme point map, using the constructed affine chart and infinity section. -/
def coordinatePoint (W : WeierstrassCurve k) :
    W.toAffine.Point → (𝟙_ (FScheme k) ⟶ curveOver W)
  | .zero => originOver W
  | .some x y h => affinePointOver W x y h.1 ≫ affineChartOver W

@[simp] theorem coordinatePoint_zero (W : WeierstrassCurve k) :
    coordinatePoint W 0 = originOver W := rfl

@[simp] theorem coordinatePoint_some (W : WeierstrassCurve k) (x y : k)
    (h : W.toAffine.Nonsingular x y) :
    coordinatePoint W (.some x y h) = affinePointOver W x y h.1 ≫ affineChartOver W := rfl

lemma affinePointEval_ext (W : WeierstrassCurve k)
    (f g : affineRing W →+* k)
    (hc : ∀ a, f (algebraMap k (affineRing W) a) = g (algebraMap k (affineRing W) a))
    (hx : f (affineX W) = g (affineX W)) (hy : f (affineY W) = g (affineY W)) :
    f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · exact hc
    · exact hx
  · exact hy

lemma affinePointOver_surjective (W : WeierstrassCurve k)
    (P : 𝟙_ (FScheme k) ⟶ affineOver W) :
    ∃ (x y : k) (h : W.toAffine.Equation x y), affinePointOver W x y h = P := by
  let f : affineRing W →+* k := (Spec.preimage P.left).hom
  have hf : Spec.map (CommRingCat.ofHom f) = P.left := Spec.map_preimage P.left
  have hc (a : k) : f (algebraMap k (affineRing W) a) = a := by
    have hw := P.w
    change P.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) = 𝟙 _ at hw
    rw [← hf, ← Spec.map_comp] at hw
    change Spec.map _ = 𝟙 (Spec (.of k)) at hw
    rw [← Spec.map_id] at hw
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective hw)) a
  let x := f (affineX W)
  let y := f (affineY W)
  have heq : W.toAffine.Equation x y := by
    have h := congrArg f (affine_relation W)
    simp only [map_sub, map_add, map_mul, map_pow, map_zero, hc] at h
    rw [WeierstrassCurve.Affine.equation_iff']
    change y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0
    dsimp [x, y]
    exact h
  refine ⟨x, y, heq, ?_⟩
  have heval : affinePointEval W x y heq = f := by
    apply affinePointEval_ext W
    · intro a
      simp [hc]
    · exact affinePointEval_x W x y heq
    · exact affinePointEval_y W x y heq
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (affinePointEval W x y heq)) = _
  rw [heval, hf]

lemma coordinatePoint_some_ne_zero (W : WeierstrassCurve k) (x y : k)
    (h : W.toAffine.Nonsingular x y) :
    coordinatePoint W (.some x y h) ≠ coordinatePoint W 0 := by
  intro heq
  have hp := congrArg (fun P : 𝟙_ (FScheme k) ⟶ curveOver W =>
    P.left (IsLocalRing.closedPoint k)) heq
  have hmem : (coordinatePoint W (.some x y h)).left (IsLocalRing.closedPoint k) ∈
      Set.range (affineChart W) := ⟨_, rfl⟩
  rw [hp, affineChart_range_complement] at hmem
  exact hmem rfl

lemma coordinatePoint_injective (W : WeierstrassCurve k) :
    Function.Injective (coordinatePoint W) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) heq
  · rfl
  · exact (coordinatePoint_some_ne_zero W x' y' h' heq.symm).elim
  · exact (coordinatePoint_some_ne_zero W x y h heq).elim
  · have hm := congrArg (fun P : 𝟙_ (FScheme k) ⟶ curveOver W => P.left) heq
    change Spec.map _ ≫ affineChart W = Spec.map _ ≫ affineChart W at hm
    have hf := Spec.map_injective ((cancel_mono (affineChart W)).mp hm)
    have hx := congrArg (fun f : CommRingCat.of (affineRing W) ⟶ CommRingCat.of k =>
      f.hom (affineX W)) hf
    have hy := congrArg (fun f : CommRingCat.of (affineRing W) ⟶ CommRingCat.of k =>
      f.hom (affineY W)) hf
    change affinePointEval W x y h.1 (affineX W) =
      affinePointEval W x' y' h'.1 (affineX W) at hx
    change affinePointEval W x y h.1 (affineY W) =
      affinePointEval W x' y' h'.1 (affineY W) at hy
    simp only [affinePointEval_x, affinePointEval_y] at hx hy
    cases hx
    cases hy
    rfl

/-- The literal affine chart plus its exact infinity complement proves exhaustion
of actual scheme-valued rational points. No coordinate bijection is assumed. -/
lemma coordinatePoint_surjective [IsAlgClosed k] (W : WeierstrassCurve k) (hΔ : W.Δ ≠ 0) :
    Function.Surjective (coordinatePoint W) := by
  intro P
  by_cases hp : P.left (IsLocalRing.closedPoint k) = infinityPoint W
  · refine ⟨0, ?_⟩
    apply Over.OverMorphism.ext
    apply ext_of_apply_closedPoint_eq (structureMap W)
    · exact (coordinatePoint W 0).w
    · exact P.w
    · exact hp.symm
  · have hr : Set.range P.left ⊆ Set.range (affineChart W) := by
      rintro _ ⟨a, rfl⟩
      rw [affineChart_range_complement]
      have ha : a = IsLocalRing.closedPoint k :=
        @Subsingleton.elim (Spec (.of k)) _ a (IsLocalRing.closedPoint k)
      change P.left a ≠ infinityPoint W
      rwa [ha]
    let f := IsOpenImmersion.lift (affineChart W) P.left hr
    have hfac : f ≫ affineChart W = P.left := IsOpenImmersion.lift_fac _ _ hr
    let Q : 𝟙_ (FScheme k) ⟶ affineOver W := Over.homMk f (by
      change f ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) = 𝟙 _
      rw [← affineChart_structure W, ← Category.assoc, hfac]
      exact P.w)
    obtain ⟨x, y, heq, hQ⟩ := affinePointOver_surjective W Q
    refine ⟨.some x y
      ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq), ?_⟩
    rw [coordinatePoint_some, hQ]
    apply Over.OverMorphism.ext
    exact hfac


end WeierstrassCurve.Projective

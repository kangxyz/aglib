/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Points
public import Aglib.AlgebraicGeometry.RationalPoint.ExtensionSource

/-!
# Field-extension points of the original projective cubic

Source: ordinary R5 Weierstrass.Points, lines 297–532.
The coordinate bijection holds for every field map k → K when Δ is nonzero.
Its codomain consists of K-valued points of the original k-scheme.
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
variable {k K : Type u} [Field k] [Field K]

/-- Original affine coordinate algebra evaluated in an extension field. -/
def affinePointEvalExtension (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Equation x y) : affineRing W →+* K :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom f x) y (by
    simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom]
    convert (WeierstrassCurve.Affine.equation_iff' _ _).mp h using 1
    simp [WeierstrassCurve.map]
    ring)

@[simp] theorem affinePointEvalExtension_x (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Equation x y) :
    affinePointEvalExtension W f x y h (affineX W) = x := by
  simp [affinePointEvalExtension, affineX, AdjoinRoot.lift_of]

@[simp] theorem affinePointEvalExtension_y (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Equation x y) :
    affinePointEvalExtension W f x y h (affineY W) = y := by
  simp [affinePointEvalExtension, affineY, AdjoinRoot.lift_root]

@[simp] theorem affinePointEvalExtension_constant (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Equation x y) (a : k) :
    affinePointEvalExtension W f x y h (algebraMap k (affineRing W) a) = f a := by
  change affinePointEvalExtension W f x y h (AdjoinRoot.of _ (Polynomial.C a)) = f a
  simp [affinePointEvalExtension, AdjoinRoot.lift_of]

lemma affinePointEvalExtension_structure (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Equation x y) :
    (affinePointEvalExtension W f x y h).comp (algebraMap k (affineRing W)) = f := by
  ext a
  exact affinePointEvalExtension_constant W f x y h a

/-- The actual extension point and its actual base triangle. -/
def affinePointOverExtension (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Equation x y) :
    extensionPointSource f ⟶ affineOver W :=
  Over.homMk (Spec.map (CommRingCat.ofHom (affinePointEvalExtension W f x y h))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    exact congrArg (fun g : k →+* K => Spec.map (CommRingCat.ofHom g))
      (affinePointEvalExtension_structure W f x y h))

/-- The original infinity section, evaluated over Spec K. -/
def originOverExtension (W : WeierstrassCurve k) (f : k →+* K) :
    extensionPointSource f ⟶ curveOver W :=
  Over.homMk (Spec.map (CommRingCat.ofHom f) ≫ infinitySection W) (by
    change (Spec.map (CommRingCat.ofHom f) ≫ infinitySection W) ≫ structureMap W = Spec.map _
    simp only [Category.assoc, infinitySection_structure, Category.comp_id])

@[simp] theorem originOverExtension_closedPoint (W : WeierstrassCurve k) (f : k →+* K) :
    (originOverExtension W f).left (IsLocalRing.closedPoint K) = infinityPoint W := by
  change infinitySection W (Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint K)) = _
  congr 1
  exact Subsingleton.elim _ _

/-- Coordinate points of W mapped to K become points of the original k-scheme. -/
def coordinatePointExtension (W : WeierstrassCurve k) (f : k →+* K) :
    (W.map f).toAffine.Point → (extensionPointSource f ⟶ curveOver W)
  | .zero => originOverExtension W f
  | .some x y h => affinePointOverExtension W f x y h.1 ≫ affineChartOver W

@[simp] theorem coordinatePointExtension_zero (W : WeierstrassCurve k) (f : k →+* K) :
    coordinatePointExtension W f 0 = originOverExtension W f := rfl

@[simp] theorem coordinatePointExtension_some (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Nonsingular x y) :
    coordinatePointExtension W f (.some x y h) =
      affinePointOverExtension W f x y h.1 ≫ affineChartOver W := rfl

lemma affinePointEvalExtension_ext (W : WeierstrassCurve k)
    (f g : affineRing W →+* K)
    (hc : ∀ a, f (algebraMap k (affineRing W) a) = g (algebraMap k (affineRing W) a))
    (hx : f (affineX W) = g (affineX W)) (hy : f (affineY W) = g (affineY W)) :
    f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · exact hc
    · exact hx
  · exact hy

lemma affinePointOverExtension_surjective (W : WeierstrassCurve k) (f : k →+* K)
    (P : extensionPointSource f ⟶ affineOver W) :
    ∃ (x y : K) (h : (W.map f).toAffine.Equation x y),
      affinePointOverExtension W f x y h = P := by
  let g : affineRing W →+* K := (Spec.preimage P.left).hom
  have hg : Spec.map (CommRingCat.ofHom g) = P.left := Spec.map_preimage P.left
  have hc (a : k) : g (algebraMap k (affineRing W) a) = f a := by
    have hw := P.w
    change P.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) = Spec.map _ at hw
    rw [← hg, ← Spec.map_comp] at hw
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective hw)) a
  let x := g (affineX W)
  let y := g (affineY W)
  have heq : (W.map f).toAffine.Equation x y := by
    have h := congrArg g (affine_relation W)
    simp only [map_sub, map_add, map_mul, map_pow, map_zero, hc] at h
    rw [WeierstrassCurve.Affine.equation_iff']
    change y ^ 2 + f W.a₁ * x * y + f W.a₃ * y -
      (x ^ 3 + f W.a₂ * x ^ 2 + f W.a₄ * x + f W.a₆) = 0
    dsimp [x, y]
    exact h
  refine ⟨x, y, heq, ?_⟩
  have heval : affinePointEvalExtension W f x y heq = g := by
    apply affinePointEvalExtension_ext W
    · intro a
      simp [hc]
    · exact affinePointEvalExtension_x W f x y heq
    · exact affinePointEvalExtension_y W f x y heq
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (affinePointEvalExtension W f x y heq)) = _
  rw [heval, hg]

lemma coordinatePointExtension_some_ne_zero (W : WeierstrassCurve k) (f : k →+* K)
    (x y : K) (h : (W.map f).toAffine.Nonsingular x y) :
    coordinatePointExtension W f (.some x y h) ≠ coordinatePointExtension W f 0 := by
  intro heq
  have hp := congrArg (fun P : extensionPointSource f ⟶ curveOver W =>
    P.left (IsLocalRing.closedPoint K)) heq
  have hmem : (coordinatePointExtension W f (.some x y h)).left (IsLocalRing.closedPoint K) ∈
      Set.range (affineChart W) := ⟨_, rfl⟩
  rw [hp, affineChart_range_complement] at hmem
  exact hmem (originOverExtension_closedPoint W f)

lemma coordinatePointExtension_injective (W : WeierstrassCurve k) (f : k →+* K) :
    Function.Injective (coordinatePointExtension W f) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) heq
  · rfl
  · exact (coordinatePointExtension_some_ne_zero W f x' y' h' heq.symm).elim
  · exact (coordinatePointExtension_some_ne_zero W f x y h heq).elim
  · have hm := congrArg (fun P : extensionPointSource f ⟶ curveOver W => P.left) heq
    change Spec.map _ ≫ affineChart W = Spec.map _ ≫ affineChart W at hm
    have hf := Spec.map_injective ((cancel_mono (affineChart W)).mp hm)
    have hx := congrArg (fun g : CommRingCat.of (affineRing W) ⟶ CommRingCat.of K =>
      g.hom (affineX W)) hf
    have hy := congrArg (fun g : CommRingCat.of (affineRing W) ⟶ CommRingCat.of K =>
      g.hom (affineY W)) hf
    change affinePointEvalExtension W f x y h.1 (affineX W) =
      affinePointEvalExtension W f x' y' h'.1 (affineX W) at hx
    change affinePointEvalExtension W f x y h.1 (affineY W) =
      affinePointEvalExtension W f x' y' h'.1 (affineY W) at hy
    simp only [affinePointEvalExtension_x, affinePointEvalExtension_y] at hx hy
    cases hx
    cases hy
    rfl

@[reassoc] lemma chart_structure (W : WeierstrassCurve k) (i : Fin 3) :
    chart W i ≫ structureMap W = Spec.map (CommRingCat.ofHom (chartConstant W i)) := by
  rw [chart, structureMap, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- A field-valued point supported at the original rational infinity is its unique
base-compatible extension. No algebraic closure or new group over K is used. -/
lemma eq_originOverExtension_of_closedPoint (W : WeierstrassCurve k) (f : k →+* K)
    (P : extensionPointSource f ⟶ curveOver W)
    (hp : P.left (IsLocalRing.closedPoint K) = infinityPoint W) :
    P = originOverExtension W f := by
  have hr : Set.range P.left ⊆ Set.range (chart W 1) := by
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint K := @Subsingleton.elim (Spec (.of K)) _ _ _
    rw [ha, hp, infinityPoint_eq_chart]
    exact ⟨_, rfl⟩
  let Q := IsOpenImmersion.lift (chart W 1) P.left hr
  have hfac : Q ≫ chart W 1 = P.left := IsOpenImmersion.lift_fac _ _ hr
  let g : chartRing W 1 →+* K := (Spec.preimage Q).hom
  have hg : Spec.map (CommRingCat.ofHom g) = Q := Spec.map_preimage Q
  have hstr : Q ≫ Spec.map (CommRingCat.ofHom (chartConstant W 1)) =
      Spec.map (CommRingCat.ofHom f) := by
    rw [← chart_structure, ← Category.assoc, hfac]
    exact P.w
  have hc (a : k) : g (chartConstant W 1 a) = f a := by
    rw [← hg, ← Spec.map_comp] at hstr
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective hstr)) a
  have hpoint : Q (IsLocalRing.closedPoint K) = infinityChartPoint W := by
    apply (chart W 1).isOpenEmbedding.injective
    change (Q ≫ chart W 1) (IsLocalRing.closedPoint K) = infinityPoint W
    rw [hfac]
    exact hp
  have hker : RingHom.ker g = RingHom.ker (infinityChartEval W) := by
    have ht := congrArg PrimeSpectrum.asIdeal hpoint
    rw [← hg, infinityChartPoint_asIdeal] at ht
    change Ideal.comap g (IsLocalRing.maximalIdeal K) = _ at ht
    rwa [IsLocalRing.maximalIdeal_eq_bot] at ht
  have hx : g (normalizedCoordinate W 1 0) = 0 := by
    change normalizedCoordinate W 1 0 ∈ RingHom.ker g
    rw [hker]
    simp [RingHom.mem_ker]
  have hz : g (normalizedCoordinate W 1 2) = 0 := by
    change normalizedCoordinate W 1 2 ∈ RingHom.ker g
    rw [hker]
    simp [RingHom.mem_ker]
  have heval : g = f.comp (infinityChartEval W) := by
    have h : g.comp (normalizePolynomial W 1) =
        (f.comp (infinityChartEval W)).comp (normalizePolynomial W 1) := by
      ext a
      · simp only [RingHom.comp_apply, normalizePolynomial, MvPolynomial.eval₂Hom_C,
          infinityChartEval_chartConstant, hc]
      · fin_cases a <;> simp [normalizePolynomial, hx, hz]
    exact RingHom.ext fun a => by
      obtain ⟨p, rfl⟩ := normalizePolynomial_surjective W 1 a
      exact DFunLike.congr_fun h p
  apply Over.OverMorphism.ext
  change P.left = Spec.map (CommRingCat.ofHom f) ≫ infinitySection W
  rw [← hfac, ← hg, heval]
  change Spec.map (CommRingCat.ofHom (infinityChartEval W) ≫ CommRingCat.ofHom f) ≫ _ = _
  rw [Spec.map_comp, Category.assoc]
  rfl

/-- Exhaustion by the original affine chart and infinity, over every extension
field. Algebraic closure is not needed for this coordinate bijection. -/
lemma coordinatePointExtension_surjective (W : WeierstrassCurve k) (f : k →+* K)
    (hΔ : W.Δ ≠ 0) : Function.Surjective (coordinatePointExtension W f) := by
  intro P
  by_cases hp : P.left (IsLocalRing.closedPoint K) = infinityPoint W
  · exact ⟨0, (eq_originOverExtension_of_closedPoint W f P hp).symm⟩
  · have hr : Set.range P.left ⊆ Set.range (affineChart W) := by
      rintro _ ⟨a, rfl⟩
      rw [affineChart_range_complement]
      have ha : a = IsLocalRing.closedPoint K := @Subsingleton.elim (Spec (.of K)) _ _ _
      change P.left a ≠ infinityPoint W
      rwa [ha]
    let g := IsOpenImmersion.lift (affineChart W) P.left hr
    have hfac : g ≫ affineChart W = P.left := IsOpenImmersion.lift_fac _ _ hr
    let Q : extensionPointSource f ⟶ affineOver W := Over.homMk g (by
      change g ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) = Spec.map _
      rw [← affineChart_structure W, ← Category.assoc, hfac]
      exact P.w)
    obtain ⟨x, y, heq, hQ⟩ := affinePointOverExtension_surjective W f Q
    have hΔ' : (W.map f).Δ ≠ 0 := by simpa using f.injective.ne hΔ
    refine ⟨.some x y
      ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').mp heq), ?_⟩
    rw [coordinatePointExtension_some, hQ]
    apply Over.OverMorphism.ext
    exact hfac

/-- Constructed coordinate equivalence with the original scheme's K-valued points. -/
def coordinateExtensionEquiv (W : WeierstrassCurve k) (f : k →+* K) (hΔ : W.Δ ≠ 0) :
    (W.map f).toAffine.Point ≃ (extensionPointSource f ⟶ curveOver W) :=
  Equiv.ofBijective (coordinatePointExtension W f)
    ⟨coordinatePointExtension_injective W f, coordinatePointExtension_surjective W f hΔ⟩


@[simp] theorem coordinateExtensionEquiv_apply (W : WeierstrassCurve k)
    (f : k →+* K) (hΔ : W.Δ ≠ 0) (P : (W.map f).toAffine.Point) :
    coordinateExtensionEquiv W f hΔ P = coordinatePointExtension W f P := rfl

@[simp] theorem coordinateExtensionEquiv_symm_coordinatePoint (W : WeierstrassCurve k)
    (f : k →+* K) (hΔ : W.Δ ≠ 0) (P : (W.map f).toAffine.Point) :
    (coordinateExtensionEquiv W f hΔ).symm (coordinatePointExtension W f P) = P :=
  (coordinateExtensionEquiv W f hΔ).symm_apply_apply P

end WeierstrassCurve.Projective

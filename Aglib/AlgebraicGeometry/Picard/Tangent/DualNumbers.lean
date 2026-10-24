/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Generator
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.DualNumber

/-!
# The dual-number thickening `X[ε] = X ×_{Spec k} Spec k[ε]`

For a commutative ring `k` and a scheme `X` with a morphism `sX : X ⟶ Spec k`, the scheme
`dualScheme k sX` is Mathlib's fibre product `X ×_{Spec k} Spec k[ε]`, with
`k[ε] = DualNumber k`. The projection `p` and the closed fibre `i` (from `ε ↦ 0`) satisfy
`i ≫ p = 𝟙 X`. On each affine open `W` of `X`, `Γ(X[ε], p⁻¹ W)` is the pushout of `Γ(X, W)`
and `Γ(Spec k[ε], ⊤)` over `Γ(Spec k, ⊤)` (Mathlib's `isIso_pushoutSection_of_isAffineOpen`);
the pushout property gives the coordinates `Γ(X[ε], p⁻¹ W) → Γ(X, W)[ε]`, inverse to
`a + b ε ↦ p^♯ a + ε p^♯ b`. Hence the global section `ε` is an `IdealGenerator`
(`dualIdealGenerator`).

Consequently (`unitsComplex_shortExact`, `unitsSplitting`) the truncated exponential
sequence `0 → 𝒪_X → 𝒪_{X[ε]}^* → 𝒪_X^* → 1`, `b ↦ 1 + b ε`, is short exact and split on the
underlying space of `X` (Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, p. 43), unit
cohomology splits as `H^n(𝒪_{X[ε]}^*) ≃+ H^n(X, 𝒪_X) × H^n(𝒪_X^*)`
(`unitsCohomologyEquiv`), the kernel of `H^n(𝒪_{X[ε]}^*) → H^n(𝒪_X^*)` is `H^n(X, 𝒪_X)`
(`unitsCohomologyKerEquiv`), and, under a
unit-cohomology comparison, `ker(Pic(X[ε]) → Pic(X)) ≃+ H^1(X, 𝒪_X)` and
`Pic(X[ε]) ≃+ Pic(X) × H^1(X, 𝒪_X)` (the kernel of the top row of Kleiman's Square (5.11.4),
p. 43, through `Pic = H^1(𝒪^*)`; the passage to `T_0 Pic_{X/k}` through (5.11.3) and the
vertical maps of (5.11.4) is not formalized).
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.SplitThickening
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
open TrivSqZeroExt

namespace AlgebraicGeometry.Scheme.DualNumbers

universe u

section RingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The ring map `A[ε] →+* B`, `a + b ε ↦ f a + e f b`, for `e * e = 0`. -/
def liftRingHom (f : A →+* B) (e : B) (he : e * e = 0) : DualNumber A →+* B where
  toFun x := f x.fst + e * f x.snd
  map_one' := by simp only [fst_one, snd_one, map_one, map_zero, mul_zero, add_zero]
  map_mul' x y := by
    simp only [fst_mul, DualNumber.snd_mul, map_mul, map_add]
    linear_combination (-(f x.snd * f y.snd)) * he
  map_zero' := by simp only [fst_zero, snd_zero, map_zero, mul_zero, add_zero]
  map_add' x y := by
    simp only [fst_add, snd_add, map_add]
    ring

theorem liftRingHom_apply (f : A →+* B) (e : B) (he : e * e = 0) (x : DualNumber A) :
    liftRingHom f e he x = f x.fst + e * f x.snd := rfl

theorem liftRingHom_inl (f : A →+* B) (e : B) (he : e * e = 0) (a : A) :
    liftRingHom f e he (inl a) = f a := by
  rw [liftRingHom_apply, fst_inl, snd_inl, map_zero, mul_zero, add_zero]

theorem liftRingHom_eps (f : A →+* B) (e : B) (he : e * e = 0) :
    liftRingHom f e he DualNumber.eps = e := by
  rw [liftRingHom_apply, DualNumber.fst_eps, DualNumber.snd_eps, map_zero, map_one, mul_one,
    zero_add]

end RingHom

theorem le_preimage_top {Z T : Scheme.{u}} (f : Z ⟶ T) (V : Z.Opens) : V ≤ f ⁻¹ᵁ ⊤ := by
  simp

variable (k : Type u) [CommRing k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The structure morphism `Spec k[ε] ⟶ Spec k`. -/
abbrev dualMap : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

/-- The closed point `Spec k ⟶ Spec k[ε]`, from `ε ↦ 0`. -/
abbrev closedPoint : Spec (.of k) ⟶ Spec (.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

theorem closedPoint_dualMap : closedPoint k ≫ dualMap k = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  rfl

/-- The dual-number thickening `X[ε] = X ×_{Spec k} Spec k[ε]`. -/
abbrev dualScheme : Scheme.{u} := pullback sX (dualMap k)

/-- The projection `p : X[ε] ⟶ X`. -/
abbrev projection : dualScheme k sX ⟶ X := pullback.fst sX (dualMap k)

/-- The closed fibre `i : X ⟶ X[ε]`. -/
def inclusion : X ⟶ dualScheme k sX :=
  pullback.lift (𝟙 X) (sX ≫ closedPoint k) (by
    rw [Category.id_comp, Category.assoc, closedPoint_dualMap, Category.comp_id])

@[reassoc (attr := simp)]
theorem inclusion_projection : inclusion k sX ≫ projection k sX = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem inclusion_snd : inclusion k sX ≫ pullback.snd sX (dualMap k) = sX ≫ closedPoint k :=
  pullback.lift_snd _ _ _

/-- The global section `ε` of `X[ε]`. -/
def eps : Γ(dualScheme k sX, ⊤) :=
  (pullback.snd sX (dualMap k)).appTop.hom
    ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom DualNumber.eps)

theorem eps_mul_self : eps k sX * eps k sX = 0 := by
  rw [eps, ← map_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero, map_zero]

theorem app_top_eps : ((inclusion k sX).app ⊤).hom (eps k sX) = 0 := by
  have e2 := congrArg (fun φ : CommRingCat.of (DualNumber k) ⟶ Γ(Spec (.of k), ⊤) =>
    φ.hom DualNumber.eps)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e2
  change ((inclusion k sX ≫ pullback.snd sX (dualMap k)).appTop).hom
    ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom DualNumber.eps) = 0
  rw [inclusion_snd]
  change sX.appTop.hom ((closedPoint k).appTop.hom
    ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom DualNumber.eps)) = 0
  rw [← e2]
  change sX.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom
    (DualNumber.eps : DualNumber k).fst) = 0
  rw [DualNumber.fst_eps, map_zero, map_zero]

section Affine

variable {k}
variable (W : X.Opens) (hW : IsAffineOpen W)

include hW in
/-- `Γ(X[ε], p⁻¹ W)` is the pushout of `Γ(X, W)` and `Γ(Spec k[ε], ⊤)` over
`Γ(Spec k, ⊤)`, for an affine open `W` of `X`. -/
theorem isPushout :
    IsPushout (sX.appLE ⊤ W (le_preimage_top sX W))
      ((dualMap k).appLE ⊤ ⊤ (le_preimage_top (dualMap k) ⊤))
      ((projection k sX).appLE W (projection k sX ⁻¹ᵁ W) le_rfl)
      ((pullback.snd sX (dualMap k)).appLE ⊤ (projection k sX ⁻¹ᵁ W)
        (le_preimage_top _ _)) := by
  have H : IsPullback (projection k sX) (pullback.snd sX (dualMap k)) sX (dualMap k) :=
    IsPullback.of_hasPullback sX (dualMap k)
  have hUY : projection k sX ⁻¹ᵁ W =
      projection k sX ⁻¹ᵁ W ⊓ pullback.snd sX (dualMap k) ⁻¹ᵁ ⊤ := by
    simp
  have := isIso_pushoutSection_of_isAffineOpen H (le_preimage_top (dualMap k) ⊤)
    (le_preimage_top sX W) hUY (isAffineOpen_top _) (isAffineOpen_top _) hW
  exact (isIso_pushoutSection_iff H _ _ hUY).mp this

/-- The structure map `k →+* Γ(X, W)`. -/
def structureMap : k →+* Γ(X, W) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ W (le_preimage_top sX W)).hom

/-- `k[ε] →+* Γ(X, W)[ε]`. -/
def dualStructureMap : DualNumber k →+* DualNumber Γ(X, W) :=
  liftRingHom ((inlHom Γ(X, W) Γ(X, W)).comp (structureMap sX W)) DualNumber.eps
    DualNumber.eps_mul_eps

theorem dualMap_appLE_eq :
    (dualMap k).appLE ⊤ ⊤ (le_preimage_top (dualMap k) ⊤) = (dualMap k).app ⊤ :=
  Scheme.Hom.appLE_eq_app _

theorem coordinates_w :
    sX.appLE ⊤ W (le_preimage_top sX W) ≫ CommRingCat.ofHom (inlHom Γ(X, W) Γ(X, W)) =
      (dualMap k).appLE ⊤ ⊤ (le_preimage_top (dualMap k) ⊤) ≫
        (Scheme.ΓSpecIso (.of (DualNumber k))).hom ≫
          CommRingCat.ofHom (dualStructureMap sX W) := by
  rw [dualMap_appLE_eq, ← Category.assoc, Scheme.ΓSpecIso_naturality]
  ext z : 2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  have halg : algebraMap k (DualNumber k) ((Scheme.ΓSpecIso (.of k)).hom.hom z) =
      inl ((Scheme.ΓSpecIso (.of k)).hom.hom z) := rfl
  have hz : (Scheme.ΓSpecIso (.of k)).inv.hom ((Scheme.ΓSpecIso (.of k)).hom.hom z) = z :=
    CommRingCat.inv_hom_apply _ z
  rw [halg, dualStructureMap, liftRingHom_inl, RingHom.comp_apply, structureMap,
    CommRingCat.hom_comp, RingHom.comp_apply, hz]

/-- The coordinates `Γ(X[ε], p⁻¹ W) ⟶ Γ(X, W)[ε]`, from the pushout property. -/
def coordinates : Γ(dualScheme k sX, projection k sX ⁻¹ᵁ W) ⟶
    CommRingCat.of (DualNumber Γ(X, W)) :=
  (isPushout sX W hW).desc (CommRingCat.ofHom (inlHom Γ(X, W) Γ(X, W)))
    ((Scheme.ΓSpecIso (.of (DualNumber k))).hom ≫
      CommRingCat.ofHom (dualStructureMap sX W)) (coordinates_w sX W)

theorem coordinates_projection (a : Γ(X, W)) :
    (coordinates sX W hW).hom (((projection k sX).app W).hom a) = inl a := by
  have e := congrArg (fun φ => φ.hom a) ((isPushout sX W hW).inl_desc
    (CommRingCat.ofHom (inlHom Γ(X, W) Γ(X, W))) _ (coordinates_w sX W))
  rw [coordinates]
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Scheme.Hom.appLE_eq_app, inlHom_apply] using e

/-- `ε` restricted to `p⁻¹ W`, written through the original second projection. -/
theorem restrictTop_eps :
    restrictTop (projection k sX) (eps k sX) W =
      ((pullback.snd sX (dualMap k)).appLE ⊤ (projection k sX ⁻¹ᵁ W)
        (le_preimage_top _ _)).hom
          ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom DualNumber.eps) := rfl

theorem coordinates_eps :
    (coordinates sX W hW).hom (restrictTop (projection k sX) (eps k sX) W) =
      DualNumber.eps := by
  have e := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom
    DualNumber.eps)) ((isPushout sX W hW).inr_desc
      (CommRingCat.ofHom (inlHom Γ(X, W) Γ(X, W))) _ (coordinates_w sX W))
  have hε : (Scheme.ΓSpecIso (.of (DualNumber k))).hom.hom
      ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom DualNumber.eps) = DualNumber.eps :=
    CommRingCat.hom_inv_apply _ _
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [hε] at e
  rw [restrictTop_eps]
  refine e.trans ?_
  rw [dualStructureMap, liftRingHom_eps]

/-- `Γ(X, W)[ε] →+* Γ(X[ε], p⁻¹ W)`, `a + b ε ↦ p^♯ a + ε p^♯ b`. -/
def fromCoordinates :
    DualNumber Γ(X, W) →+* Γ(dualScheme k sX, projection k sX ⁻¹ᵁ W) :=
  liftRingHom ((projection k sX).app W).hom (restrictTop (projection k sX) (eps k sX) W) (by
    rw [← map_mul, eps_mul_self, map_zero])

include hW in
theorem fromCoordinates_dualStructureMap (x : DualNumber k) :
    fromCoordinates sX W (dualStructureMap sX W x) =
      ((pullback.snd sX (dualMap k)).appLE ⊤ (projection k sX ⁻¹ᵁ W)
        (le_preimage_top _ _)).hom ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom x) := by
  have hring : (fromCoordinates sX W).comp (dualStructureMap sX W) =
      ((pullback.snd sX (dualMap k)).appLE ⊤ (projection k sX ⁻¹ᵁ W)
        (le_preimage_top _ _)).hom.comp (Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom := by
    apply DualNumber.ringHom_ext
    · ext r
      have e1 := congrArg (fun φ => φ.hom r)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (DualNumber k))))
      have e2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r))
        (isPushout sX W hW).w
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
        Scheme.Hom.appLE_eq_app] at e1 e2
      rw [dualMap_appLE_eq] at e2
      change fromCoordinates sX W (dualStructureMap sX W (inl r)) =
        ((pullback.snd sX (dualMap k)).appLE ⊤ (projection k sX ⁻¹ᵁ W)
          (le_preimage_top _ _)).hom
            ((Scheme.ΓSpecIso (.of (DualNumber k))).inv.hom (algebraMap k (DualNumber k) r))
      rw [e1, dualStructureMap, liftRingHom_inl, RingHom.comp_apply, inlHom_apply,
        fromCoordinates, liftRingHom_inl]
      exact e2
    · simp only [RingHom.comp_apply]
      rw [dualStructureMap, liftRingHom_eps, fromCoordinates, liftRingHom_eps]
      rfl
  exact congrArg (fun φ => φ x) hring

theorem fromCoordinates_coordinates (b : Γ(dualScheme k sX, projection k sX ⁻¹ᵁ W)) :
    fromCoordinates sX W ((coordinates sX W hW).hom b) = b := by
  have key : coordinates sX W hW ≫ CommRingCat.ofHom (fromCoordinates sX W) = 𝟙 _ := by
    apply (isPushout sX W hW).hom_ext
    · rw [Category.comp_id, Scheme.Hom.appLE_eq_app]
      ext a
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      rw [coordinates_projection, fromCoordinates, liftRingHom_inl]
    · rw [Category.comp_id, coordinates, IsPushout.inr_desc_assoc]
      ext z
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      rw [fromCoordinates_dualStructureMap sX W hW]
      congr 1
      exact CommRingCat.inv_hom_apply _ z
  exact congrArg (fun φ => φ.hom b) key

include hW in
theorem mul_injective :
    Function.Injective fun a : Γ(X, W) =>
      restrictTop (projection k sX) (eps k sX) W * ((projection k sX).app W).hom a := by
  intro a b hab
  have e := congrArg (fun t => ((coordinates sX W hW).hom t).snd) hab
  have hsnd : ∀ c : Γ(X, W), (DualNumber.eps * inl c : DualNumber Γ(X, W)).snd = c := by
    intro c
    rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, snd_inl, fst_inl, zero_mul,
      one_mul, zero_add]
  simp only [map_mul] at e
  rw [coordinates_eps, coordinates_projection, coordinates_projection, hsnd, hsnd] at e
  exact e

include hW in
theorem exists_eq_mul (b : Γ(dualScheme k sX, projection k sX ⁻¹ᵁ W))
    (hb : ((reduction (inclusion k sX) (projection k sX)
      (inclusion_projection k sX)).hom.app (op W)).hom b = 0) :
    ∃ a : Γ(X, W), restrictTop (projection k sX) (eps k sX) W *
      ((projection k sX).app W).hom a = b := by
  have hb' := fromCoordinates_coordinates sX W hW b
  rw [fromCoordinates, liftRingHom_apply] at hb'
  refine ⟨((coordinates sX W hW).hom b).snd, ?_⟩
  have hfst : ((coordinates sX W hW).hom b).fst = 0 := by
    have e := congrArg ((reduction (inclusion k sX) (projection k sX)
      (inclusion_projection k sX)).hom.app (op W)).hom hb'
    rw [hb, map_add, map_mul, reduction_projection _ _ _ (op W),
      reduction_projection _ _ _ (op W),
      reduction_restrictTop _ _ _ (eps k sX) (app_top_eps k sX), zero_mul, add_zero] at e
    exact e
  rw [hfst, map_zero, zero_add] at hb'
  exact hb'

end Affine

/-- The dual-number generator `ε` of the ideal of `X ⟶ X[ε]`. -/
def dualIdealGenerator :
    IdealGenerator (inclusion k sX) (projection k sX) (inclusion_projection k sX) where
  ε := eps k sX
  eps_mul_self := eps_mul_self k sX
  app_top_eps := app_top_eps k sX
  injective W hW := mul_injective sX W hW
  exists_eq W hW b hb := exists_eq_mul sX W hW b hb

/-- The truncated exponential sequence `0 → 𝒪_X → 𝒪_{X[ε]}^* → 𝒪_X^* → 1`, with first map
`b ↦ 1 + b ε` (`IdealGenerator.oneAddMap_app_apply`), is short exact on `|X|`
(Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, p. 43). -/
theorem unitsComplex_shortExact : (dualIdealGenerator k sX).unitsComplex.ShortExact :=
  (dualIdealGenerator k sX).unitsComplex_shortExact

/-- The truncated exponential sequence is split by `a ↦ a + 0 · ε`. -/
def unitsSplitting : (dualIdealGenerator k sX).unitsComplex.Splitting :=
  (dualIdealGenerator k sX).unitsSplitting

/-- `H^n(𝒪_{X[ε]}^*) ≃+ H^n(X, 𝒪_X) × H^n(𝒪_X^*)` on `|X|`, in every degree. -/
def unitsCohomologyEquiv (n : ℕ) :
    Sheaf.H (ringSheaf (projection k sX)).units n ≃+
      Sheaf.H (Scheme.structureAddSheaf X) n × Sheaf.H X.sheaf.units n :=
  (SplitThickening.unitsCohomologyEquiv (inclusion k sX) (projection k sX)
    (inclusion_projection k sX) (dualIdealGenerator k sX).reduction_ker_sq n).trans
      (AddEquiv.prodCongr ((dualIdealGenerator k sX).cohomologyEquiv n) (AddEquiv.refl _))

/-- The kernel of `H^n(𝒪_{X[ε]}^*) → H^n(𝒪_X^*)` on `|X|` is `H^n(X, 𝒪_X)`, through
`b ↦ 1 + b ε` (Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, p. 43, for `n = 1`). -/
def unitsCohomologyKerEquiv (n : ℕ) :
    (Sheaf.H.map (Sheaf.unitsMap (reduction (inclusion k sX) (projection k sX)
      (inclusion_projection k sX))) n).ker ≃+ Sheaf.H (Scheme.structureAddSheaf X) n :=
  (SplitThickening.unitsCohomologyKerEquiv (inclusion k sX) (projection k sX)
    (inclusion_projection k sX) (dualIdealGenerator k sX).reduction_ker_sq n).trans
      ((dualIdealGenerator k sX).cohomologyEquiv n)

/-- Under a unit-cohomology comparison, `ker(Pic(X[ε]) → Pic(X)) ≃+ H^1(X, 𝒪_X)` (the top
row of Kleiman's Square (5.11.4), p. 43; this is the absolute group `Pic(X[ε])`, not
`Pic_{X/k}(k_ε)`). -/
def picardKerEquiv
    (C : UnitsCohomologyComparison (inclusion k sX) (projection k sX)
      (inclusion_projection k sX)) :
    (pullbackHom (inclusion k sX)).ker ≃+ Sheaf.H (Scheme.structureAddSheaf X) 1 :=
  (dualIdealGenerator k sX).picardKerEquiv C

/-- Under a unit-cohomology comparison, `Pic(X[ε]) ≃+ Pic(X) × H^1(X, 𝒪_X)` through the
retraction; the first component is pullback along `X ⟶ X[ε]`. -/
def picardEquiv
    (C : UnitsCohomologyComparison (inclusion k sX) (projection k sX)
      (inclusion_projection k sX)) :
    PicardGroup (dualScheme k sX) ≃+ PicardGroup X × Sheaf.H (Scheme.structureAddSheaf X) 1 :=
  (dualIdealGenerator k sX).picardEquiv C

end AlgebraicGeometry.Scheme.DualNumbers

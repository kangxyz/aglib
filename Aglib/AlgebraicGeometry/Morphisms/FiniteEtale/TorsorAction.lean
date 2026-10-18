/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.Group
public import Aglib.CategoryTheory.TorsorAction.Basic
public import Aglib.TopologicalGroup.PointedAffineActions

/-!
# Affine fibre actions extracted from actual scheme torsors

Source: `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex`, at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, SHA-256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
This snapshot applies to every declaration below.

The torsor, its action morphism and its points are actual schemes and scheme
maps. Unique scheme-point transport gives coordinates on its finite fibre.
Conjugating the canonical natural automorphism evaluation on that fibre
constructs the permutation homomorphism; no representation is an input.
Naturality on the actual finite product and the represented torsor action
proves affinity. The canonical fibre-automorphism topology proves continuity.
No Galois-category/fibre-classification assumption or point-endomorphism action
is needed for this forward extraction.

A coefficient-point group marking, its equivariance through a given projection,
and a point fixed by a given section remain intentional module/point data.
This layer does not establish cover classification, geometric connectedness,
or an H¹/isogeny equivalence.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj FintypeCatDiscrete
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite finiteFiber)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions

universe u
attribute [local instance] Over.cartesianMonoidalCategory GroupDescent.coverCartesian

variable {B : Scheme.{u}} {K : Type u} [Field K]
  (s : Spec (CommRingCat.of K) ⟶ B)

/-- Naturality of actual fibre evaluation on an actual cover morphism,
the scheme-action compatibility used in
`K2-018#prop:k2018-arithmetic-characters`. -/
theorem evaluation_naturality (γ : FiberAutGroup s) {Z W : Scheme.FiniteEtale B}
    (f : Z.obj ⟶ W.obj) (x : Fiber s Z) :
    γ.hom.app W (x ≫ f) = γ.hom.app Z x ≫ f := by
  have h := ConcreteCategory.congr_hom
    (γ.hom.naturality (ObjectProperty.homMk f)) x
  exact h

variable (A : Grp (Over B)) [IsFinite A.X.hom] [Etale A.X.hom] (Y : Scheme.FiniteEtale B)

/-- The actual coefficient scheme as a finite-etale cover, for the fibre
action extraction in `K2-018#prop:k2018-arithmetic-characters`. -/
abbrev coefficientCover : Scheme.FiniteEtale B := ⟨A.X, ⟨inferInstance, inferInstance⟩⟩

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Actual pullback-product point projections in the scheme Over category,
used for `K2-018#prop:k2018-arithmetic-characters`'s action naturality. -/
private theorem point_lift_fst (a : Over.mk s ⟶ A.X) (x : Fiber s Y) :
    lift a x ≫ fst A.X Y.obj = a := by
  apply Over.OverMorphism.ext
  have hf : (fst A.X Y.obj).left = Limits.pullback.fst A.X.hom Y.obj.hom := rfl
  simp only [Over.comp_left, Over.lift_left, hf, Limits.pullback.lift_fst]

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Actual second pullback-product point projection for the same finite
scheme action naturality in `K2-018#prop:k2018-arithmetic-characters`. -/
private theorem point_lift_snd (a : Over.mk s ⟶ A.X) (x : Fiber s Y) :
    lift a x ≫ snd A.X Y.obj = x := by
  apply Over.OverMorphism.ext
  have hf : (snd A.X Y.obj).left = Limits.pullback.snd A.X.hom Y.obj.hom := rfl
  simp only [Over.comp_left, Over.lift_left, hf, Limits.pullback.lift_snd]

/-- Evaluation on the actual product cover preserves the pair of point
lifts, by naturality on its projections, for
`K2-018#prop:k2018-arithmetic-characters`. -/
theorem evaluation_product (γ : FiberAutGroup s) (a : Over.mk s ⟶ A.X)
    (x : Fiber s Y) :
    γ.hom.app (coefficientCover A ⊗ Y) (lift a x) =
      lift (γ.hom.app (coefficientCover A) a) (γ.hom.app Y x) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h := evaluation_naturality s γ (Z := coefficientCover A ⊗ Y)
      (W := coefficientCover A) (fst A.X Y.obj) (lift a x)
    rw [point_lift_fst s A Y] at h
    exact h.symm.trans (point_lift_fst s A Y _ _).symm
  · have h := evaluation_naturality s γ (Z := coefficientCover A ⊗ Y)
      (W := Y) (snd A.X Y.obj) (lift a x)
    rw [point_lift_snd s A Y] at h
    exact h.symm.trans (point_lift_snd s A Y _ _).symm

variable (τ : TorsorAction A (toUnit Y.obj))

/-- The actual scheme torsor action commutes with natural fibre evaluation,
for `K2-018#prop:k2018-arithmetic-characters`. This is derived from the
represented action morphism and finite-product naturality. -/
theorem evaluation_torsor_action (γ : FiberAutGroup s) (a : Over.mk s ⟶ A.X)
    (x : Fiber s Y) :
    γ.hom.app Y (τ.act a x) =
      τ.act (γ.hom.app (coefficientCover A) a) (γ.hom.app Y x) := by
  rw [← τ.comp_actionMap]
  have h := evaluation_naturality s γ (Z := coefficientCover A ⊗ Y)
    (W := Y) τ.actionMap (lift a x)
  rw [evaluation_product s A Y] at h
  exact h.trans (τ.comp_actionMap _ _)

/-- Actual unique scheme-point transport on the fibre over the terminal
object, for `K2-018#prop:k2018-arithmetic-characters`. The equality over the
base is derived from the terminal universal property. -/
def transport (x y : Fiber s Y) : Over.mk s ⟶ A.X :=
  Classical.choose (τ.transport x y (toUnit_unique _ _))

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- The transported coefficient point acts to give the requested actual
point, for `K2-018#prop:k2018-arithmetic-characters`. -/
theorem transport_act (x y : Fiber s Y) : τ.act (transport s A Y τ x y) x = y :=
  (Classical.choose_spec (τ.transport x y (toUnit_unique _ _))).1

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Unique scheme-point transport identifies every coefficient point with
the constructed transport, for
`K2-018#prop:k2018-arithmetic-characters`. -/
theorem transport_unique (x y : Fiber s Y) (a : Over.mk s ⟶ A.X)
    (ha : τ.act a x = y) : a = transport s A Y τ x y :=
  (Classical.choose_spec (τ.transport x y (toUnit_unique _ _))).2 a ha

variable {R : Type u} [AddCommGroup R]
  (mark : (Over.mk s ⟶ A.X) ≃* Multiplicative R) (x0 : Fiber s Y)

include mark in
/-- The point marking forces the coefficient type to be finite, for
`K2-018#prop:k2018-arithmetic-characters`; finiteness of R is not an input. -/
theorem finite_coefficient : Finite R := by
  let : Finite (Over.mk s ⟶ A.X) := finiteFiber s (coefficientCover A)
  let : Finite (Multiplicative R) := Finite.of_equiv (Over.mk s ⟶ A.X) mark.toEquiv
  exact Finite.of_injective Multiplicative.ofAdd
    (fun _ _ h => congrArg Multiplicative.toAdd h)

/-- Fibre coordinates constructed from actual unique torsor transport and
the actual coefficient-point marking, for
`K2-018#prop:k2018-arithmetic-characters`. No set-torsor or basis bijection
is supplied independently of the scheme action. -/
def fibreBasis : Fiber s Y ≃ R where
  toFun x := (mark (transport s A Y τ x0 x)).toAdd
  invFun r := τ.act (mark.symm (Multiplicative.ofAdd r)) x0
  left_inv x := by
    change τ.act (mark.symm (mark (transport s A Y τ x0 x))) x0 = x
    rw [mark.symm_apply_apply]
    exact transport_act s A Y τ x0 x
  right_inv r := by
    change (mark (transport s A Y τ x0 (τ.act (mark.symm (Multiplicative.ofAdd r)) x0))).toAdd = r
    rw [← transport_unique s A Y τ x0 _ (mark.symm (Multiplicative.ofAdd r)) rfl,
      mark.apply_symm_apply]
    rfl

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- The inverse coordinate map is the genuine scheme torsor action at the
selected point, for `K2-018#prop:k2018-arithmetic-characters`. -/
@[simp] theorem fibreBasis_symm_apply (r : R) :
    (fibreBasis s A Y τ mark x0).symm r = τ.act (mark.symm (Multiplicative.ofAdd r)) x0 := rfl

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Coordinate evaluation is actual transport from the chosen point,
for `K2-018#prop:k2018-arithmetic-characters`. -/
@[simp] theorem fibreBasis_apply (x : Fiber s Y) :
    fibreBasis s A Y τ mark x0 x = (mark (transport s A Y τ x0 x)).toAdd := rfl

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- The selected actual point is coordinate zero, for
`K2-018#prop:k2018-arithmetic-characters`. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem fibreBasis_basepoint : fibreBasis s A Y τ mark x0 x0 = 0 := by
  change (mark (transport s A Y τ x0 x0)).toAdd = 0
  have ht : transport s A Y τ x0 x0 = 1 :=
    (transport_unique s A Y τ x0 x0 1 (τ.one_act x0)).symm
  rw [ht, map_one]
  rfl

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Coordinate zero is the selected actual point, for
`K2-018#prop:k2018-arithmetic-characters`. -/
-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem fibreBasis_symm_zero : (fibreBasis s A Y τ mark x0).symm 0 = x0 := by
  rw [fibreBasis_symm_apply]
  change τ.act (mark.symm 1) x0 = x0
  rw [map_one, τ.one_act]

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Actual coefficient translation becomes additive translation in the
constructed fibre coordinates, for
`K2-018#prop:k2018-arithmetic-characters`. -/
theorem fibreBasis_action (a : Over.mk s ⟶ A.X) (x : Fiber s Y) :
    fibreBasis s A Y τ mark x0 (τ.act a x) =
      fibreBasis s A Y τ mark x0 x + (mark a).toAdd := by
  have ht : transport s A Y τ x0 (τ.act a x) = a * transport s A Y τ x0 x := by
    apply (transport_unique s A Y τ x0 _ _ ?_).symm
    rw [τ.mul_act, transport_act]
  change (mark (transport s A Y τ x0 (τ.act a x))).toAdd = _
  rw [ht, map_mul]
  exact add_comm _ _

/-- The actual natural automorphism of the finite fibre as a permutation,
for the forward extraction in
`K2-018#prop:k2018-arithmetic-characters`. It is not supplied as input data. -/
def naturalFiberPermutation : FiberAutGroup s →* Equiv.Perm (Fiber s Y) where
  toFun γ := FintypeCat.equivEquivIso.symm (γ.app Y)
  map_one' := by apply Equiv.ext; intro x; rfl
  map_mul' γ δ := by apply Equiv.ext; intro x; rfl

/-- Conjugation of actual natural fibre evaluation into the constructed
torsor coordinates, for `K2-018#prop:k2018-arithmetic-characters`.
This constructs the permutation homomorphism rather than assuming it. -/
def rho : FiberAutGroup s →* Equiv.Perm R where
  toFun γ := (fibreBasis s A Y τ mark x0).symm.trans
    ((naturalFiberPermutation s Y γ).trans (fibreBasis s A Y τ mark x0))
  map_one' := by
    apply Equiv.ext
    intro r
    exact (fibreBasis s A Y τ mark x0).apply_symm_apply r
  map_mul' γ δ := by
    apply Equiv.ext
    intro r
    change fibreBasis s A Y τ mark x0 ((γ * δ).hom.app Y
      ((fibreBasis s A Y τ mark x0).symm r)) =
        fibreBasis s A Y τ mark x0 (γ.hom.app Y ((fibreBasis s A Y τ mark x0).symm
          (fibreBasis s A Y τ mark x0 (δ.hom.app Y ((fibreBasis s A Y τ mark x0).symm r)))))
    rw [Equiv.symm_apply_apply]
    rfl

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- The extracted representation is actual fibre evaluation in torsor
coordinates, for `K2-018#prop:k2018-arithmetic-characters`. -/
@[simp] theorem rho_apply (γ : FiberAutGroup s) (r : R) :
    rho s A Y τ mark x0 γ r = fibreBasis s A Y τ mark x0
      (γ.hom.app Y ((fibreBasis s A Y τ mark x0).symm r)) := rfl

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Formula on actual fibre points for the constructed representation,
for `K2-018#prop:k2018-arithmetic-characters`. -/
theorem rho_fibre (γ : FiberAutGroup s) (x : Fiber s Y) :
    rho s A Y τ mark x0 γ (fibreBasis s A Y τ mark x0 x) =
      fibreBasis s A Y τ mark x0 (γ.hom.app Y x) := by
  rw [rho_apply, Equiv.symm_apply_apply]

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Exact genuine transport formula for the extracted action, for
`K2-018#prop:k2018-arithmetic-characters`. -/
theorem rho_transport (γ : FiberAutGroup s) (r : R) :
    rho s A Y τ mark x0 γ r =
      (mark (transport s A Y τ x0
        (γ.hom.app Y (τ.act (mark.symm (Multiplicative.ofAdd r)) x0)))).toAdd := rfl

variable [TopologicalSpace R] [DiscreteTopology R]

omit [IsFinite A.X.hom] [Etale A.X.hom] in
/-- Joint continuity of the extracted representation, from the canonical
finite-fibre coordinate of Aut(Fx), for
`K2-018#prop:k2018-arithmetic-characters`. No representation-continuity or
Galois-category classification premise is used. -/
theorem rho_continuous_eval :
    Continuous (fun z : FiberAutGroup s × R => rho s A Y τ mark x0 z.1 z.2) := by
  have hcoord : Continuous (fun γ : FiberAutGroup s =>
      PreGaloisCategory.autEmbedding (fiberToFinite s) γ Y) :=
    (continuous_apply Y).comp continuous_induced_dom
  let f : Aut ((fiberToFinite s).obj Y) × R → R := fun z =>
    fibreBasis s A Y τ mark x0 (z.1.hom ((fibreBasis s A Y τ mark x0).symm z.2))
  change Continuous (fun z : FiberAutGroup s × R =>
    f (PreGaloisCategory.autEmbedding (fiberToFinite s) z.1 Y, z.2))
  exact (continuous_of_discreteTopology (f := f)).comp
    ((hcoord.comp continuous_fst).prodMk continuous_snd)

variable {G : Type*} [Group G] [DistribMulAction G R]
  (p : FiberAutGroup s →* G) (q : G →* FiberAutGroup s)
  (hmark : ∀ (γ : FiberAutGroup s) (a : Over.mk s ⟶ A.X),
    mark (γ.hom.app (coefficientCover A) a) =
      Multiplicative.ofAdd ((p γ) • (mark a).toAdd))
  (hx0 : ∀ g : G, (q g).hom.app Y x0 = x0)

omit [TopologicalSpace R] [DiscreteTopology R] in
include hmark in
/-- Affinity is derived from genuine scheme-action naturality and the
given coefficient-point equivariance, for
`K2-018#prop:k2018-arithmetic-characters`. The affine law is not an input. -/
theorem rho_affine (γ : FiberAutGroup s) (a b : R) :
    rho s A Y τ mark x0 γ (a + b) = rho s A Y τ mark x0 γ a + (p γ) • b := by
  let c : Over.mk s ⟶ A.X := mark.symm (Multiplicative.ofAdd b)
  have htrans : (fibreBasis s A Y τ mark x0).symm (a + b) =
      τ.act c ((fibreBasis s A Y τ mark x0).symm a) := by
    apply (fibreBasis s A Y τ mark x0).injective
    rw [Equiv.apply_symm_apply, fibreBasis_action, Equiv.apply_symm_apply]
    simp [c]
  rw [rho_apply, htrans, evaluation_torsor_action, fibreBasis_action, hmark]
  change fibreBasis s A Y τ mark x0 (γ.hom.app Y ((fibreBasis s A Y τ mark x0).symm a)) +
    (p γ) • (mark c).toAdd = _
  simp only [c, mark.apply_symm_apply]
  rfl

omit [TopologicalSpace R] [DiscreteTopology R] [DistribMulAction G R]
  [IsFinite A.X.hom] [Etale A.X.hom] in
include hx0 in
/-- A section-fixed actual point gives section-fixed coordinate zero,
for `K2-018#prop:k2018-arithmetic-characters`. -/
theorem rho_section_zero (g : G) : rho s A Y τ mark x0 (q g) 0 = 0 := by
  rw [rho_apply, fibreBasis_symm_zero, hx0, fibreBasis_basepoint]

include hmark hx0 in
/-- The PointedAffineAction consumer constructed from an actual finite
etale scheme torsor, for `K2-018#prop:k2018-arithmetic-characters`.
Only coefficient/section/point data are input; rho, its continuity and its
affine/pointed laws are derived. No target representation or classification
record is assumed. Continuity of p/q is not needed for this forward extraction. -/
def pointedAffineAction : TopologicalGroup.PointedAffineActions.PointedAffineAction p q R where
  rho := rho s A Y τ mark x0
  continuous_eval := rho_continuous_eval s A Y τ mark x0
  affine := rho_affine s A Y τ mark x0 p hmark
  section_zero := rho_section_zero s A Y τ mark x0 q hx0

include hmark hx0 in
/-- Consumer evaluation is the actual constructed torsor-fibre action,
for `K2-018#prop:k2018-arithmetic-characters`. -/
@[simp] theorem pointedAffineAction_rho (γ : FiberAutGroup s) (r : R) :
    (pointedAffineAction s A Y τ mark x0 p q hmark hx0).rho γ r =
      fibreBasis s A Y τ mark x0
        (γ.hom.app Y ((fibreBasis s A Y τ mark x0).symm r)) := rfl

include hmark hx0 in
/-- Under the intentional splitting identity, section evaluation is exactly
the given coefficient action, for
`K2-018#prop:k2018-arithmetic-characters`. -/
theorem rho_section_apply (hps : ∀ g, p (q g) = g) (g : G) (r : R) :
    rho s A Y τ mark x0 (q g) r = g • r :=
  (pointedAffineAction s A Y τ mark x0 p q hmark hx0).section_apply hps g r

end AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 e28f6fcf227f78aba3c7ca20032809339cacdc2db75ff6ce9aaecded0b8bc276.
Definitions, hypotheses and universes are retained modulo native names. -/

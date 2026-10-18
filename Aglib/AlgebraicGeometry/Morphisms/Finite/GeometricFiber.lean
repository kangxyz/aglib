/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Invariance of finite-scheme geometric fibres under field extension

Generic finite-scheme prerequisite for `K2-018#prop:k2018-arithmetic-characters`
on source basis `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
The consumer is the all-algebraically-closed-field quantifier in
`PointedIsogenies.CyclicCoefficient.geometric_cyclic`.
The finite étale fibre API is `FiniteEtaleCovers.lean`, accepted SHA256
`593e6b847bd845fa2b13de95a7c0b7991a2cf94b70d27a14ca1d24b5833adaa6`.

For an algebraically closed field `k`, any field extension `L/k`, and a finite
scheme over `k`, precomposition with `Spec L ⟶ Spec k` is a bijection on actual
points over `k`. The coordinate-algebra proof uses the finite-dimensional image
of a point's coordinate map: this image is an integral domain integral over `k`,
so its structural map from `k` is bijective. No descent or point-bijection premise
is supplied. Nilpotents cause no restriction, and étaleness is not required.

Pullback gives the corresponding result for a finite scheme over any base and
an algebraically closed point field. For each actual point `s : Spec K ⟶ Spec F`,
the map `Spec.preimage s` supplies the `F`-algebra structure on `K`. An embedding
of `AlgebraicClosure F` into `K` is then constructed and proved compatible with
`s`. Precomposition gives a natural isomorphism of finite étale fibre functors
and a multiplicative equivalence on points of finite group schemes. The embedding
is chosen; independence of that choice is not claimed.

`allClosedGroupMarkings` transports any selected algebraic-closure fibre marking
to every algebraically closed geometric fibre. These arguments work in every
characteristic, hence apply to the required characteristic-zero case without
additional perfection assumptions. This module imports no essay or K-theory code.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricFibres

universe u

/-- The actual spectrum map of a field extension. -/
def fieldPoint (k L : Type u) [Field k] [Field L] [Algebra k L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L))

section Coordinates

variable (k L : Type u) [Field k] [Field L]

/-- Global-section coordinates of an actual point lift. -/
def coordinates (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k))
    (X : Over (Spec (CommRingCat.of k))) (p : Over.mk s ⟶ X) : Γ(X.left, ⊤) →+* L :=
  (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom).hom

theorem coordinates_injective (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k))
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] :
    Function.Injective (coordinates k L s X) := by
  intro p q h
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of L)).hom).mp
  exact CommRingCat.hom_ext h

theorem point_from_coordinates (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k))
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (p : Over.mk s ⟶ X) :
    Spec.map (CommRingCat.ofHom (coordinates k L s X p)) ≫ X.left.isoSpec.inv = p.left := by
  apply (cancel_mono X.left.isoSpec.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map (p.left.appTop ≫ _) = p.left ≫ X.left.isoSpec.hom
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Scheme.isoSpec_hom_naturality]

end Coordinates

section ClosedField

variable (k L : Type u) [Field k] [IsAlgClosed k] [Field L] [Algebra k L]

/-- A homomorphism from a finite algebra to an extension field has all its values in
the algebraically closed base field. -/
theorem finiteAlgebraHom_postcomp_bijective (A : Type u) [CommRing A] [Algebra k A]
    [Module.Finite k A] :
    Function.Bijective (fun φ : A →ₐ[k] k => (Algebra.ofId k L).comp φ) := by
  constructor
  · intro φ ψ h
    apply AlgHom.ext
    intro x
    exact (algebraMap k L).injective (congrArg (fun f : A →ₐ[k] L => f x) h)
  · intro φ
    let S := φ.range
    let : Module.Finite k S :=
      Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
    let e : k ≃ₐ[k] S := AlgEquiv.ofBijective (Algebra.ofId k S)
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨e.symm.toAlgHom.comp φ.rangeRestrict, ?_⟩
    apply AlgHom.ext
    intro x
    exact congrArg (fun y : S => (y : L)) (e.apply_symm_apply (φ.rangeRestrict x))

/-- The extension map as a morphism of actual schemes over the base field. -/
def fieldPointOver : Over.mk (fieldPoint k L) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Over.homMk (fieldPoint k L) (by simp)

/-- Extend a rational point of a scheme over `k` to an `L`-valued point. -/
def extendPoint (X : Over (Spec (CommRingCat.of k)))
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) : Over.mk (fieldPoint k L) ⟶ X :=
  fieldPointOver k L ≫ p

omit [IsAlgClosed k] in
@[simp] theorem extendPoint_left (X : Over (Spec (CommRingCat.of k)))
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    (extendPoint k L X p).left = fieldPoint k L ≫ p.left := rfl

omit [IsAlgClosed k] in
theorem coordinates_extendPoint (X : Over (Spec (CommRingCat.of k)))
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    coordinates k L (fieldPoint k L) X (extendPoint k L X p) =
      (algebraMap k L).comp (coordinates k k (𝟙 _) X p) := by
  change ((Spec.map _ ≫ p.left).appTop ≫ _).hom = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

/-- Finite-scheme point invariance under arbitrary extensions of an algebraically closed field. -/
theorem extendPoint_bijective (X : Over (Spec (CommRingCat.of k))) [IsFinite X.hom] :
    Function.Bijective (extendPoint k L X) := by
  let : IsAffine X.left := isAffine_of_isAffineHom X.hom
  constructor
  · intro p q h
    apply coordinates_injective k k (𝟙 _) X
    apply RingHom.ext
    intro x
    apply (algebraMap k L).injective
    have he := congrArg (fun p => coordinates k L (fieldPoint k L) X p x) h
    simpa only [coordinates_extendPoint, RingHom.comp_apply] using he
  · intro p
    let A := Γ(X.left, ⊤)
    let a : k →+* A := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom
    let : Algebra k A := a.toAlgebra
    have ha : a.Finite := X.hom.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
    let : Module.Finite k A := ha
    let φ : A →ₐ[k] L :=
      { toRingHom := coordinates k L (fieldPoint k L) X p
        commutes' := fun x => by
          have he : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop) ≫
              (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom) =
                CommRingCat.ofHom (algebraMap k L) := by
            rw [Category.assoc, ← Category.assoc X.hom.appTop p.left.appTop,
              ← Scheme.Hom.comp_appTop, Over.w p]
            change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ((Spec.map _).appTop ≫ _) = _
            rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
          exact congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of L => h.hom x) he }
    obtain ⟨ψ, hψ⟩ := (finiteAlgebraHom_postcomp_bijective k L A).surjective φ
    have hstruct : X.left.isoSpec.inv ≫ X.hom = Spec.map (CommRingCat.ofHom a) := by
      rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
      rfl
    let q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X :=
      Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.left.isoSpec.inv) (by
        change (Spec.map _ ≫ X.left.isoSpec.inv) ≫ X.hom = 𝟙 _
        rw [Category.assoc, hstruct, ← Spec.map_comp, Spec.map_eq_id]
        ext x
        exact ψ.commutes x)
    refine ⟨q, ?_⟩
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ (Spec.map _ ≫ X.left.isoSpec.inv) = p.left
    rw [← Category.assoc, ← Spec.map_comp]
    have hψ' : CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom (algebraMap k L) =
        CommRingCat.ofHom (coordinates k L (fieldPoint k L) X p) :=
      CommRingCat.hom_ext (congrArg AlgHom.toRingHom hψ)
    rw [hψ']
    exact point_from_coordinates k L (fieldPoint k L) X p

/-- The actual extension map, bundled as a point-set equivalence. -/
def finitePointEquiv (X : Over (Spec (CommRingCat.of k))) [IsFinite X.hom] :
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) ≃ (Over.mk (fieldPoint k L) ⟶ X) :=
  Equiv.ofBijective (extendPoint k L X) (extendPoint_bijective k L X)

end ClosedField

section ArbitraryBase

variable {B : Scheme.{u}}
variable (k L : Type u) [Field k] [IsAlgClosed k] [Field L] [Algebra k L]

/-- A point of a scheme over `B` is a rational point of its pullback to its field. -/
def rationalPullbackEquiv (s : Spec (CommRingCat.of k) ⟶ B) (X : Over B) :
    (Over.mk s ⟶ X) ≃
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Over.pullback s).obj X) where
  toFun p := Over.homMk (pullback.lift p.left (𝟙 _)
    (by simp)) (by simp)
  invFun q := Over.homMk (q.left ≫ pullback.fst X.hom s) (by
    have hq : q.left ≫ pullback.snd X.hom s = 𝟙 _ := Over.w q
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq]
    simp)
  left_inv p := by
    apply Over.OverMorphism.ext
    simp
  right_inv q := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · simpa using (Over.w q).symm

/-- The actual pullback adjunction identifies point lifts over a composite. -/
def pullbackPointEquiv (s : Spec (CommRingCat.of k) ⟶ B) (X : Over B) :
    (Over.mk (fieldPoint k L ≫ s) ⟶ X) ≃
      (Over.mk (fieldPoint k L) ⟶ (Over.pullback s).obj X) :=
  (Over.mapPullbackAdj s).homEquiv (Over.mk (fieldPoint k L)) X

omit [IsAlgClosed k] in
@[simp] theorem pullbackPointEquiv_left (s : Spec (CommRingCat.of k) ⟶ B) (X : Over B)
    (p : Over.mk (fieldPoint k L ≫ s) ⟶ X) :
    (pullbackPointEquiv k L s X p).left = pullback.lift p.left (fieldPoint k L) (Over.w p) := by
  simp only [pullbackPointEquiv, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Precompose actual point lifts along the extension of their point field. -/
def extendFiber (s : Spec (CommRingCat.of k) ⟶ B) (X : Over B)
    (p : Over.mk s ⟶ X) : Over.mk (fieldPoint k L ≫ s) ⟶ X :=
  (Over.homMk (fieldPoint k L) rfl : Over.mk (fieldPoint k L ≫ s) ⟶ Over.mk s) ≫ p

omit [IsAlgClosed k] in
@[simp] theorem extendFiber_left (s : Spec (CommRingCat.of k) ⟶ B) (X : Over B)
    (p : Over.mk s ⟶ X) : (extendFiber k L s X p).left = fieldPoint k L ≫ p.left := rfl

omit [IsAlgClosed k] in
theorem extendFiber_naturality (s : Spec (CommRingCat.of k) ⟶ B) {X Y : Over B}
    (f : X ⟶ Y) (p : Over.mk s ⟶ X) :
    extendFiber k L s X p ≫ f = extendFiber k L s Y (p ≫ f) := by
  change (Over.homMk (fieldPoint k L) rfl ≫ p) ≫ f =
    (Over.homMk (fieldPoint k L) rfl : Over.mk (fieldPoint k L ≫ s) ⟶ Over.mk s) ≫ (p ≫ f)
  exact Category.assoc _ _ _

omit [IsAlgClosed k] in
theorem extendFiber_pullback (s : Spec (CommRingCat.of k) ⟶ B) (X : Over B)
    (p : Over.mk s ⟶ X) :
    pullbackPointEquiv k L s X (extendFiber k L s X p) =
      extendPoint k L ((Over.pullback s).obj X) (rationalPullbackEquiv k s X p) := by
  apply Over.OverMorphism.ext
  rw [pullbackPointEquiv_left]
  apply pullback.hom_ext
  · simp [extendFiber, extendPoint, fieldPointOver, rationalPullbackEquiv]
  · simp [extendPoint, fieldPointOver, rationalPullbackEquiv]

/-- Every finite-scheme geometric fibre is unchanged by extension of its closed point field. -/
theorem extendFiber_bijective (s : Spec (CommRingCat.of k) ⟶ B) (X : Over B)
    [IsFinite X.hom] : Function.Bijective (extendFiber k L s X) := by
  let Y := (Over.pullback s).obj X
  let : IsFinite Y.hom := inferInstanceAs (IsFinite (pullback.snd X.hom s))
  constructor
  · intro p q h
    apply (rationalPullbackEquiv k s X).injective
    apply (extendPoint_bijective k L Y).injective
    rw [← extendFiber_pullback, ← extendFiber_pullback, h]
  · intro p
    obtain ⟨q, hq⟩ := (extendPoint_bijective k L Y).surjective (pullbackPointEquiv k L s X p)
    refine ⟨(rationalPullbackEquiv k s X).symm q, ?_⟩
    apply (pullbackPointEquiv k L s X).injective
    rw [extendFiber_pullback, Equiv.apply_symm_apply]
    exact hq

/-- A point-preserving scheme arrow induced by the extension gives the same bijection. -/
theorem precompose_bijective {s : Spec (CommRingCat.of k) ⟶ B}
    {t : Spec (CommRingCat.of L) ⟶ B} (g : Over.mk t ⟶ Over.mk s)
    (hg : g.left = fieldPoint k L) (X : Over B) [IsFinite X.hom] :
    Function.Bijective (fun p : Over.mk s ⟶ X => g ≫ p) := by
  have ht := Over.w g
  change g.left ≫ s = t at ht
  rw [hg] at ht
  change (fieldPoint k L ≫ s : Spec (CommRingCat.of L) ⟶ B) = t at ht
  subst t
  have hg' : g = (Over.homMk (fieldPoint k L) rfl :
      Over.mk (fieldPoint k L ≫ s) ⟶ Over.mk s) := by
    apply Over.OverMorphism.ext
    exact hg
  subst g
  exact extendFiber_bijective k L s X

attribute [local instance] Over.cartesianMonoidalCategory

/-- Precomposition is a group equivalence on points of a finite group scheme. -/
def finiteGroupPointEquiv {s : Spec (CommRingCat.of k) ⟶ B}
    {t : Spec (CommRingCat.of L) ⟶ B} (g : Over.mk t ⟶ Over.mk s)
    (hg : g.left = fieldPoint k L) (G : Grp (Over B)) [IsFinite G.X.hom] :
    (Over.mk s ⟶ G.X) ≃* (Over.mk t ⟶ G.X) :=
  { Equiv.ofBijective (fun p => g ≫ p) (precompose_bijective k L g hg G.X) with
    map_mul' := MonObj.comp_mul g }

@[simp] theorem finiteGroupPointEquiv_apply {s : Spec (CommRingCat.of k) ⟶ B}
    {t : Spec (CommRingCat.of L) ⟶ B} (g : Over.mk t ⟶ Over.mk s)
    (hg : g.left = fieldPoint k L) (G : Grp (Over B)) [IsFinite G.X.hom]
    (p : Over.mk s ⟶ G.X) : finiteGroupPointEquiv k L g hg G p = g ≫ p := rfl

end ArbitraryBase

section AllClosedPoints

variable (F K : Type u) [Field F] [Field K] [IsAlgClosed K]

/-- An actual embedding of the chosen algebraic closure, compatible with the given scheme point.
The `F`-algebra structure on `K` is recovered from that point, rather than supplied separately. -/
def closedPointEmbedding (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F)) :
    {e : AlgebraicClosure F →+* K //
      e.comp (algebraMap F (AlgebraicClosure F)) = (Spec.preimage s).hom} := by
  letI : Algebra F K := (Spec.preimage s).hom.toAlgebra
  let e : AlgebraicClosure F →ₐ[F] K := IsAlgClosed.lift
  exact ⟨e.toRingHom, RingHom.ext (fun x => e.commutes x)⟩

/-- The compatible embedding induces an actual arrow between the two geometric points. -/
def closedPointArrow (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F)) :
    Over.mk s ⟶ Over.mk (fieldPoint F (AlgebraicClosure F)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (closedPointEmbedding F K s).val)) (by
    change Spec.map _ ≫ Spec.map _ = s
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((closedPointEmbedding F K s).val.comp (algebraMap F (AlgebraicClosure F)))) = s
    rw [(closedPointEmbedding F K s).property]
    exact Spec.map_preimage s)

/-- Every closed geometric fibre of a finite scheme is obtained bijectively by precomposition
from the selected algebraic-closure fibre. -/
theorem closedPoint_precompose_bijective
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F))
    (X : Over (Spec (CommRingCat.of F))) [IsFinite X.hom] :
    Function.Bijective (fun p : Over.mk (fieldPoint F (AlgebraicClosure F)) ⟶ X =>
      closedPointArrow F K s ≫ p) := by
  let : Algebra (AlgebraicClosure F) K := (closedPointEmbedding F K s).val.toAlgebra
  exact precompose_bijective (AlgebraicClosure F) K (closedPointArrow F K s) rfl X

/-- Comparison with an arbitrary algebraically closed geometric fibre, using a compatible
embedding of the algebraic closure chosen in `closedPointEmbedding`. -/
def closedFiberEquiv (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F))
    (X : Over (Spec (CommRingCat.of F))) [IsFinite X.hom] :
    (Over.mk (fieldPoint F (AlgebraicClosure F)) ⟶ X) ≃ (Over.mk s ⟶ X) :=
  Equiv.ofBijective (fun p => closedPointArrow F K s ≫ p)
    (closedPoint_precompose_bijective F K s X)

@[simp] theorem closedFiberEquiv_apply
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F))
    (X : Over (Spec (CommRingCat.of F))) [IsFinite X.hom]
    (p : Over.mk (fieldPoint F (AlgebraicClosure F)) ⟶ X) :
    closedFiberEquiv F K s X p = closedPointArrow F K s ≫ p := rfl

theorem closedFiberEquiv_naturality
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F))
    {X Y : Over (Spec (CommRingCat.of F))} [IsFinite X.hom] [IsFinite Y.hom]
    (f : X ⟶ Y) (p : Over.mk (fieldPoint F (AlgebraicClosure F)) ⟶ X) :
    closedFiberEquiv F K s X p ≫ f = closedFiberEquiv F K s Y (p ≫ f) :=
  Category.assoc _ _ _

/-- The comparison is a natural isomorphism of the actual finite étale fibre functors. -/
def closedFiberNatIso (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F)) :
    _root_.AlgebraicGeometry.Scheme.FiniteEtale.fiberToFinite (fieldPoint F (AlgebraicClosure F)) ≅
      _root_.AlgebraicGeometry.Scheme.FiniteEtale.fiberToFinite s :=
  NatIso.ofComponents
    (fun Y => FintypeCat.equivEquivIso (closedFiberEquiv F K s Y.obj)) (by
      intro Y Z f
      apply FintypeCat.hom_ext
      intro p
      exact (closedFiberEquiv_naturality F K s f.hom p).symm)

attribute [local instance] Over.cartesianMonoidalCategory

/-- Comparison of geometric fibres preserves the actual group-scheme multiplication. -/
def closedGroupPointsEquiv (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F))
    (G : Grp (Over (Spec (CommRingCat.of F)))) [IsFinite G.X.hom] :
    (Over.mk (fieldPoint F (AlgebraicClosure F)) ⟶ G.X) ≃* (Over.mk s ⟶ G.X) :=
  { closedFiberEquiv F K s G.X with map_mul' := MonObj.comp_mul (closedPointArrow F K s) }

@[simp] theorem closedGroupPointsEquiv_apply
    (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F))
    (G : Grp (Over (Spec (CommRingCat.of F)))) [IsFinite G.X.hom]
    (p : Over.mk (fieldPoint F (AlgebraicClosure F)) ⟶ G.X) :
    closedGroupPointsEquiv F K s G p = closedPointArrow F K s ≫ p := rfl

variable {K} in
/-- A marking on the selected algebraic-closure fibre gives markings on every algebraically
closed geometric fibre. This directly supplies the quantifier required by `geometric_cyclic`,
without importing an essay, cyclic coefficient, or descent interface. -/
theorem allClosedGroupMarkings (G : Grp (Over (Spec (CommRingCat.of F)))) [IsFinite G.X.hom]
    (M : Type*) [Group M]
    (h : Nonempty ((Over.mk (fieldPoint F (AlgebraicClosure F)) ⟶ G.X) ≃* M)) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F)),
      Nonempty ((Over.mk s ⟶ G.X) ≃* M) := by
  intro K _ _ s
  obtain ⟨e⟩ := h
  exact ⟨(closedGroupPointsEquiv F K s G).symm.trans e⟩

end AllClosedPoints

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricFibres

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 152771d51064e0afd765b839243c8a1bc99f10ab888930772ea09660be31fae7.
Definitions, hypotheses and universes are retained modulo native names. -/

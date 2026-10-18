/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Galois.Topology

/-!
# Geometric-fibre automorphism groups and origin sections

Construction prerequisite for `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, with source basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`; the corresponding essay locator is
`eq:pointed-character`. The scheme interfaces have basis
`ac804cb2f648f42380e612235b972786506d0b9f`. The imported finite étale category and
fibre functor are the accepted `FiniteEtaleCovers.lean`, SHA256
`593e6b847bd845fa2b13de95a7c0b7991a2cf94b70d27a14ca1d24b5833adaa6`.

`FiberAutGroup x` is the actual automorphism group of the finite-valued fibre
functor at a field-valued point `x`. For a separably closed field,
`FundamentalGroup x` names its geometric-point specialization. Multiplication
acts by composition of permutations: `(a * b)(q) = a(b(q))`.

A scheme map sends the source fibre automorphism group to the target group.
Its construction uses pullback of finite étale covers and conjugation by the
proved fibre natural isomorphism. Points and their maps are organized in
`Under (Spec K)`, so identity and composition have fixed source and target
groups. Functoriality follows from actual pullback comparison morphisms and
naturality of fibre automorphisms.

For `p : X ⟶ B` and `o : B ⟶ X` satisfying the scheme section identity
`o ≫ p = 𝟙 B`, the resulting group maps satisfy `p_* ∘ o_* = id`.
The rational-point specialization uses a scheme over `Spec F`, its actual
rational section, and the point `Spec K ⟶ Spec F` induced by `algebraMap F K`.
No group or splitting data is supplied independently of these scheme maps.

The canonical evaluation topology is inherited from mathlib's topology on
`Aut (F : C ⥤ FintypeCat)`. Its compact, Hausdorff, totally disconnected,
topological-group instances apply to every such functor, without
Galois-category hypotheses. Continuity of the induced group maps is proved
on these finite evaluation coordinates.

Identification of the field group with `Field.absoluteGaloisGroup`, the
geometric-kernel exact sequence, finite étale Galois classification, and the
étale-cohomology comparison remain separate realization steps.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Functor
open scoped CategoryTheory.PreGaloisCategory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberBaseChangeEquiv_left fiberBaseChangeIso_hom_app_apply fiberToFinite
  fiberToFiniteBaseChangeIso fiberToFinite_map)

namespace AlgebraicGeometry.Scheme.EtaleFundamentalGroups
universe u

/-- Automorphisms of the actual finite étale point fibre functor. -/
abbrev FiberAutGroup {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) := Aut (fiberToFinite x)

/-- The geometric-fibre automorphism group at a separably closed point. -/
-- Keep the original separably closed point hypothesis of the fundamental-group interface.
@[nolint unusedArguments]
abbrev FundamentalGroup {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (x : Spec (CommRingCat.of K) ⟶ X) := FiberAutGroup x

/-- Evaluate a natural fibre automorphism on one finite étale cover. -/
def evaluate {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : Scheme.FiniteEtale X) :
    FiberAutGroup x →* Aut ((fiberToFinite x).obj Y) :=
  ((CategoryTheory.evaluation (Scheme.FiniteEtale X) FintypeCat).obj Y).mapAut (fiberToFinite x)

@[simp] theorem evaluate_apply {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : Scheme.FiniteEtale X) (a : FiberAutGroup x)
    (p : Fiber x Y) : (evaluate x Y a).hom p = a.hom.app Y p := rfl

-- Keep this original canonical-map simp formula alongside its lower evaluation expansion.
@[simp, nolint simpNF] theorem evaluate_mul {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) (Y : Scheme.FiniteEtale X) (a b : FiberAutGroup x)
    (p : Fiber x Y) :
    (evaluate x Y (a * b)).hom p = (evaluate x Y a).hom ((evaluate x Y b).hom p) := rfl

theorem compactSpace_fiberAutGroup {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) : CompactSpace (FiberAutGroup x) := inferInstance

theorem t2Space_fiberAutGroup {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) : T2Space (FiberAutGroup x) := inferInstance

theorem totallyDisconnectedSpace_fiberAutGroup {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) : TotallyDisconnectedSpace (FiberAutGroup x) := inferInstance

theorem isTopologicalGroup_fiberAutGroup {X : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) : IsTopologicalGroup (FiberAutGroup x) := inferInstance

/-- A scheme map induces a group homomorphism in the same direction. -/
def map {S X : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) :
    FiberAutGroup x →* FiberAutGroup (x ≫ f) :=
  (Aut.autMulEquivOfIso (fiberToFiniteBaseChangeIso f x).symm).toMonoidHom.comp
    (((whiskeringLeft (Scheme.FiniteEtale X) (Scheme.FiniteEtale S) FintypeCat).obj
      (baseChange f)).mapAut
      (fiberToFinite x))

@[simp] theorem map_hom_app {S X : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (a : FiberAutGroup x)
    (Y : Scheme.FiniteEtale X) :
    (map f x a).hom.app Y =
      (fiberToFiniteBaseChangeIso f x).hom.app Y ≫
        a.hom.app ((baseChange f).obj Y) ≫ (fiberToFiniteBaseChangeIso f x).inv.app Y := rfl

-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF]
theorem finiteBaseChangeIso_hom_apply {S X : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : Scheme.FiniteEtale X)
    (p : Fiber (x ≫ f) Y) :
    (fiberToFiniteBaseChangeIso f x).hom.app Y p = fiberBaseChangeEquiv f x Y p := by
  change FintypeCat.incl.map ((fiberToFiniteBaseChangeIso f x).hom.app Y) p = _
  rw [fiberToFiniteBaseChangeIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  exact fiberBaseChangeIso_hom_app_apply f x Y p

-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF]
theorem finiteBaseChangeIso_inv_apply {S X : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (Y : Scheme.FiniteEtale X)
    (p : Fiber x ((baseChange f).obj Y)) :
    (fiberToFiniteBaseChangeIso f x).inv.app Y p =
      (fiberBaseChangeEquiv f x Y).symm p := by
  apply (fiberBaseChangeEquiv f x Y).injective
  rw [← finiteBaseChangeIso_hom_apply]
  simpa only [Equiv.apply_symm_apply, FintypeCat.comp_apply, FintypeCat.id_apply] using
    ConcreteCategory.congr_hom ((fiberToFiniteBaseChangeIso f x).inv_hom_id_app Y) p

-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF] theorem map_apply {S X : Scheme.{u}} {K : Type u} [Field K]
    (f : S ⟶ X) (x : Spec (CommRingCat.of K) ⟶ S) (a : FiberAutGroup x)
    (Y : Scheme.FiniteEtale X) (p : Fiber (x ≫ f) Y) :
    (map f x a).hom.app Y p = (fiberBaseChangeEquiv f x Y).symm
      (a.hom.app ((baseChange f).obj Y) (fiberBaseChangeEquiv f x Y p)) := by
  change (fiberToFiniteBaseChangeIso f x).inv.app Y
    (a.hom.app ((baseChange f).obj Y) ((fiberToFiniteBaseChangeIso f x).hom.app Y p)) = _
  rw [finiteBaseChangeIso_hom_apply, finiteBaseChangeIso_inv_apply]

/-- Schemes pointed by the fixed field `K`, with point-preserving scheme maps. -/
abbrev PointedScheme (K : Type u) [Field K] := Under (Spec (CommRingCat.of K))

variable {K : Type u} [Field K]

/-- Fibre compatibility for a map with a specified point-preserving equality. -/
def pointFiberIso {S X : Scheme.{u}} (f : S ⟶ X)
    (s : Spec (CommRingCat.of K) ⟶ S) (x : Spec (CommRingCat.of K) ⟶ X)
    (h : s ≫ f = x) : fiberToFinite x ≅ baseChange f ⋙ fiberToFinite s :=
  eqToIso (congrArg (fun x => fiberToFinite x) h.symm) ≪≫ fiberToFiniteBaseChangeIso f s

/-- The natural isomorphism identifying fibres at `X.hom` with fibres of covers pulled
back along the pointed morphism `f` at `S.hom`. -/
def pointedFiberIso {S X : PointedScheme K} (f : S ⟶ X) :
    fiberToFinite X.hom ≅ baseChange f.right ⋙ fiberToFinite S.hom :=
  pointFiberIso f.right S.hom X.hom (Under.w f)

/-- The induced homomorphism for a morphism of pointed schemes. -/
def pointedMap {S X : PointedScheme K} (f : S ⟶ X) :
    FiberAutGroup S.hom →* FiberAutGroup X.hom :=
  (Aut.autMulEquivOfIso (pointedFiberIso f).symm).toMonoidHom.comp
    (((whiskeringLeft (Scheme.FiniteEtale X.right) (Scheme.FiniteEtale S.right) FintypeCat).obj
      (baseChange f.right)).mapAut (fiberToFinite S.hom))

@[simp] theorem pointedMap_homMk {S X : Scheme.{u}} (f : S ⟶ X)
    (s : Spec (CommRingCat.of K) ⟶ S) :
    pointedMap (Under.homMk f rfl : Under.mk s ⟶ Under.mk (s ≫ f)) = map f s := rfl

/-- The equivalence from the fibre of `Y` at `X.hom` to the fibre of its pullback
along `f.right` at `S.hom`. -/
def pointedFiberEquiv {S X : PointedScheme K} (f : S ⟶ X) (Y : Scheme.FiniteEtale X.right) :
    Fiber X.hom Y ≃ Fiber S.hom ((baseChange f.right).obj Y) :=
  FintypeCat.equivEquivIso.symm ((pointedFiberIso f).app Y)

@[simp] theorem pointedMap_apply {S X : PointedScheme K} (f : S ⟶ X)
    (a : FiberAutGroup S.hom) (Y : Scheme.FiniteEtale X.right) (p : Fiber X.hom Y) :
    (pointedMap f a).hom.app Y p = (pointedFiberEquiv f Y).symm
      (a.hom.app ((baseChange f.right).obj Y) (pointedFiberEquiv f Y p)) := rfl

theorem pointFiberIso_inv_left {S X : Scheme.{u}} (f : S ⟶ X)
    (s : Spec (CommRingCat.of K) ⟶ S) (x : Spec (CommRingCat.of K) ⟶ X)
    (h : s ≫ f = x) (Y : Scheme.FiniteEtale X) (p : Fiber s ((baseChange f).obj Y)) :
    ((pointFiberIso f s x h).inv.app Y p).left = p.left ≫ pullback.fst Y.obj.hom f := by
  subst x
  change ((fiberToFiniteBaseChangeIso f s).inv.app Y p).left = _
  rw [finiteBaseChangeIso_inv_apply]
  rfl

theorem pointFiberIso_hom_left {S X : Scheme.{u}} (f : S ⟶ X)
    (s : Spec (CommRingCat.of K) ⟶ S) (x : Spec (CommRingCat.of K) ⟶ X)
    (h : s ≫ f = x) (Y : Scheme.FiniteEtale X) (p : Fiber x Y) :
    ((pointFiberIso f s x h).hom.app Y p).left =
      pullback.lift p.left s ((Over.w p).trans h.symm) := by
  subst x
  change ((fiberToFiniteBaseChangeIso f s).hom.app Y p).left = _
  rw [finiteBaseChangeIso_hom_apply, fiberBaseChangeEquiv_left]

@[simp] theorem pointedFiberEquiv_symm_left {S X : PointedScheme K} (f : S ⟶ X)
    (Y : Scheme.FiniteEtale X.right) (p : Fiber S.hom ((baseChange f.right).obj Y)) :
    ((pointedFiberEquiv f Y).symm p).left = p.left ≫ pullback.fst Y.obj.hom f.right := by
  exact pointFiberIso_inv_left f.right S.hom X.hom (Under.w f) Y p

@[simp] theorem pointedFiberEquiv_left {S X : PointedScheme K} (f : S ⟶ X)
    (Y : Scheme.FiniteEtale X.right) (p : Fiber X.hom Y) :
    (pointedFiberEquiv f Y p).left = pullback.lift p.left S.hom
      ((Over.w p).trans (Under.w f).symm) := by
  exact pointFiberIso_hom_left f.right S.hom X.hom (Under.w f) Y p

/-- The canonical morphism from pullback along a composite to iterated pullback. -/
def baseChangeComparison {S T X : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ X) (Y : Scheme.FiniteEtale X) :
    (baseChange (f ≫ g)).obj Y ⟶ (baseChange f).obj ((baseChange g).obj Y) :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift (f := pullback.snd Y.obj.hom g) (g := f)
      (pullback.lift (f := Y.obj.hom) (g := g) (pullback.fst Y.obj.hom (f ≫ g))
        (pullback.snd Y.obj.hom (f ≫ g) ≫ f)
        (by simpa only [Category.assoc] using
          (pullback.condition (f := Y.obj.hom) (g := f ≫ g))))
      (pullback.snd Y.obj.hom (f ≫ g)) (by simp)) (by simp))

theorem pointedFiberEquiv_comp {S T X : PointedScheme K} (f : S ⟶ T) (g : T ⟶ X)
    (Y : Scheme.FiniteEtale X.right) (p : Fiber X.hom Y) :
    pointedFiberEquiv f ((baseChange g.right).obj Y) (pointedFiberEquiv g Y p) =
      (fiberToFinite S.hom).map (baseChangeComparison f.right g.right Y)
        (pointedFiberEquiv (f ≫ g) Y p) := by
  apply Over.OverMorphism.ext
  simp only [pointedFiberEquiv_left, fiberToFinite_map, Over.comp_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [baseChangeComparison, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget]
    · simp [baseChangeComparison, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget, Under.w f]
  · simp [baseChangeComparison]

theorem evaluate_naturality {X : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ X)
    (a : FiberAutGroup x) {Y Z : Scheme.FiniteEtale X} (f : Y ⟶ Z) (p : Fiber x Y) :
    (fiberToFinite x).map f (a.hom.app Y p) =
      a.hom.app Z ((fiberToFinite x).map f p) := by
  simpa only [FintypeCat.comp_apply] using
    (ConcreteCategory.congr_hom (a.hom.naturality f) p).symm

/-- Covariant functoriality follows from naturality along the pullback comparison. -/
theorem pointedMap_comp {S T X : PointedScheme K} (f : S ⟶ T) (g : T ⟶ X) :
    pointedMap (f ≫ g) = (pointedMap g).comp (pointedMap f) := by
  apply MonoidHom.ext
  intro a
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro p
  apply (pointedFiberEquiv g Y).injective
  apply (pointedFiberEquiv f ((baseChange g.right).obj Y)).injective
  simp only [MonoidHom.comp_apply, pointedMap_apply, Equiv.apply_symm_apply,
    pointedFiberEquiv_comp]
  exact evaluate_naturality S.hom a (baseChangeComparison f.right g.right Y)
    (pointedFiberEquiv (f ≫ g) Y p)

/-- The first pullback projection from the base change of `Y` along `𝟙 X` to `Y`
as a morphism of finite étale covers over `X`. -/
def baseChangeIdentityProjection (X : Scheme.{u}) (Y : Scheme.FiniteEtale X) :
    (baseChange (𝟙 X)).obj Y ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.fst Y.obj.hom (𝟙 X))
    (by simpa using (pullback.condition (f := Y.obj.hom) (g := 𝟙 X))))

theorem pointedFiberEquiv_id_symm (X : PointedScheme K) (Y : Scheme.FiniteEtale X.right)
    (p : Fiber X.hom ((baseChange (𝟙 X.right)).obj Y)) :
    (pointedFiberEquiv (𝟙 X) Y).symm p =
      (fiberToFinite X.hom).map (baseChangeIdentityProjection X.right Y) p := by
  apply Over.OverMorphism.ext
  exact pointedFiberEquiv_symm_left (𝟙 X) Y p

theorem identityProjection_pointedFiberEquiv (X : PointedScheme K) (Y : Scheme.FiniteEtale X.right)
    (p : Fiber X.hom Y) :
    (fiberToFinite X.hom).map (baseChangeIdentityProjection X.right Y)
      (pointedFiberEquiv (𝟙 X) Y p) = p := by
  rw [← pointedFiberEquiv_id_symm]
  exact Equiv.symm_apply_apply _ p

@[simp] theorem pointedMap_id (X : PointedScheme K) :
    pointedMap (𝟙 X) = MonoidHom.id (FiberAutGroup X.hom) := by
  apply MonoidHom.ext
  intro a
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro p
  rw [pointedMap_apply, pointedFiberEquiv_id_symm]
  exact (evaluate_naturality X.hom a (baseChangeIdentityProjection X.right Y)
    (pointedFiberEquiv (𝟙 X) Y p)).trans
      (congrArg (fun q : Fiber X.hom Y => a.hom.app Y q)
        (identityProjection_pointedFiberEquiv X Y p))

/-- Pointed schemes map covariantly to their fibre automorphism groups. -/
def pointedGroupFunctor (K : Type u) [Field K] : PointedScheme K ⥤ GrpCat where
  obj X := GrpCat.of (FiberAutGroup X.hom)
  map f := GrpCat.ofHom (pointedMap f)
  map_id X := by
    rw [pointedMap_id]
    rfl
  map_comp f g := by
    rw [pointedMap_comp]
    rfl

/-- The pointed morphism induced by `o`, from the point `b` to the point `b ≫ o`. -/
def pointedOrigin {B X : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ B) (o : B ⟶ X) :
    Under.mk b ⟶ Under.mk (b ≫ o) := Under.homMk o rfl

/-- The pointed morphism induced by `p`, from `b ≫ o` to `b`, using the section
equation `h : o ≫ p = 𝟙 B`. -/
def pointedProjection {B X : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ B)
    (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B) :
    Under.mk (b ≫ o) ⟶ Under.mk b :=
  Under.homMk p (by simp [Category.assoc, h])

theorem pointedOriginProjection {B X : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ B)
    (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B) :
    pointedOrigin b o ≫ pointedProjection b p o h = 𝟙 (Under.mk b) := by
  apply Under.UnderMorphism.ext
  exact h

/-- The group homomorphism induced by the scheme section `o`. -/
def originHom {B X : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ B) (o : B ⟶ X) :
    FiberAutGroup b →* FiberAutGroup (b ≫ o) := pointedMap (pointedOrigin b o)

/-- The group homomorphism induced by the scheme projection `p`. -/
def projectionHom {B X : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ B)
    (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B) :
    FiberAutGroup (b ≫ o) →* FiberAutGroup b :=
  pointedMap (pointedProjection b p o h)

/-- The actual scheme section identity implies the group section identity. -/
@[simp] theorem originHom_projectionHom {B X : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B) :
    (projectionHom b p o h).comp (originHom b o) = MonoidHom.id (FiberAutGroup b) := by
  change (pointedMap (pointedProjection b p o h)).comp (pointedMap (pointedOrigin b o)) = _
  rw [← pointedMap_comp, pointedOriginProjection, pointedMap_id]
  rfl

theorem originHom_projectionHom_apply {B X : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B)
    (a : FiberAutGroup b) : projectionHom b p o h (originHom b o a) = a :=
  congrArg (fun f : FiberAutGroup b →* FiberAutGroup b => f a)
    (originHom_projectionHom b p o h)

theorem originHom_injective {B X : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B) :
    Function.Injective (originHom b o) :=
  Function.LeftInverse.injective (originHom_projectionHom_apply b p o h)

theorem projectionHom_surjective {B X : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B) :
    Function.Surjective (projectionHom b p o h) :=
  Function.RightInverse.surjective (originHom_projectionHom_apply b p o h)

/-- The induced group map is continuous for the canonical evaluation topologies. -/
theorem continuous_pointedMap {S X : PointedScheme K} (f : S ⟶ X) :
    Continuous (pointedMap f) := by
  rw [Topology.IsInducing.continuous_iff
    (PreGaloisCategory.autEmbedding_isClosedEmbedding (fiberToFinite X.hom)).isInducing,
    continuous_pi_iff]
  intro Y
  change Continuous (fun a : FiberAutGroup S.hom =>
    Aut.autMulEquivOfIso ((pointedFiberIso f).app Y).symm
      (PreGaloisCategory.autEmbedding (fiberToFinite S.hom) a ((baseChange f.right).obj Y)))
  exact continuous_of_discreteTopology.comp
    ((continuous_apply ((baseChange f.right).obj Y)).comp continuous_induced_dom)

theorem continuous_map {S X : Scheme.{u}} (f : S ⟶ X)
    (s : Spec (CommRingCat.of K) ⟶ S) : Continuous (map f s) :=
  continuous_pointedMap (Under.homMk f rfl : Under.mk s ⟶ Under.mk (s ≫ f))

theorem continuous_originHom {B X : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (o : B ⟶ X) : Continuous (originHom b o) :=
  continuous_pointedMap (pointedOrigin b o)

theorem continuous_projectionHom {B X : Scheme.{u}}
    (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B) (o : B ⟶ X) (h : o ≫ p = 𝟙 B) :
    Continuous (projectionHom b p o h) := continuous_pointedMap (pointedProjection b p o h)

/-- The field extension gives an actual point of `Spec F`. -/
def fieldPoint (F K : Type u) [Field F] [Field K] [Algebra F K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) :=
  Spec.map (CommRingCat.ofHom (algebraMap F K))

/-- The rational section of an actual `F`-scheme induces the origin group map. -/
def rationalPointOriginHom {F : Type u} [Field F] [Algebra F K]
    (X : Over (Spec (CommRingCat.of F)))
    (o : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ X) :
    FiberAutGroup (fieldPoint F K) →* FiberAutGroup (fieldPoint F K ≫ o.left) :=
  originHom (fieldPoint F K) o.left

/-- The structure map of an actual `F`-scheme induces the arithmetic projection. -/
def rationalPointProjectionHom {F : Type u} [Field F] [Algebra F K]
    (X : Over (Spec (CommRingCat.of F)))
    (o : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ X) :
    FiberAutGroup (fieldPoint F K ≫ o.left) →* FiberAutGroup (fieldPoint F K) :=
  projectionHom (fieldPoint F K) X.hom o.left (Over.w o)

/-- The rational origin splits the projection on fibre automorphism groups. -/
@[simp] theorem rationalPoint_split {F : Type u} [Field F] [Algebra F K]
    (X : Over (Spec (CommRingCat.of F)))
    (o : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ X) :
    (rationalPointProjectionHom X o).comp (rationalPointOriginHom X o) =
      MonoidHom.id (FiberAutGroup (fieldPoint F K)) :=
  originHom_projectionHom (fieldPoint F K) X.hom o.left (Over.w o)

theorem continuous_rationalPointOriginHom {F : Type u} [Field F] [Algebra F K]
    (X : Over (Spec (CommRingCat.of F)))
    (o : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ X) :
    Continuous (rationalPointOriginHom (K := K) X o) :=
  continuous_originHom (fieldPoint F K) o.left

theorem continuous_rationalPointProjectionHom {F : Type u} [Field F] [Algebra F K]
    (X : Over (Spec (CommRingCat.of F)))
    (o : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ X) :
    Continuous (rationalPointProjectionHom (K := K) X o) :=
  continuous_projectionHom (fieldPoint F K) X.hom o.left (Over.w o)

end AlgebraicGeometry.Scheme.EtaleFundamentalGroups

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 5e63a4229a77b2ee19e5721e542f32a3d6701306fabc412256f9552c2f219088.
Definitions, hypotheses and universes are retained modulo native names. -/

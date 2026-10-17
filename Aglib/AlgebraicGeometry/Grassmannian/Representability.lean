/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Gluing
public import Aglib.RingTheory.Grassmannian.Gluing

/-!
# The glued Grassmannian represents Mathlib's Grassmannian functor

Let `R : CommRingCat` and `k n : ℕ`. The scheme `schemeOver R k n` over `Spec R`, glued from the
coordinate charts in `Aglib.AlgebraicGeometry.Grassmannian.Gluing`, represents Mathlib's functor
`Module.Grassmannian.functor R (Fin n → R) k`, `A ↦ G(k, A ⊗[R] (Fin n → R); A)`, on
`R`-algebras. This is the representability of the Grassmannian functor by the glued charts
(Nitsure, arXiv:math/0504590v1, §1, "Construction of Grassmannian", pp. 7–8; Stacks, Tag 089T)
for affine test schemes over `Spec R`.

For an `R`-algebra `B`, maps from `Spec B` into a coordinate chart over `Spec R` are algebra maps
out of the chart ring, hence points over `B` lying in the chart (`chartPt`). Two such maps agree
in the glued scheme exactly when they classify the same point (`algSpec_comp_chartι_eq_iff`).

A point `N` over `A` lies in a coordinate chart over the basic opens `D(r)` of a family
generating the unit ideal (`Module.Grassmannian.exists_mem_chart_map`); the maps classifying its
restrictions glue to `pointHom N : Spec A ⟶ Gr`. Conversely, a map `g : Spec A ⟶ Gr` factors
through a coordinate chart near every prime (`exists_chartLocal`), and the classified points glue,
by Zariski gluing for Mathlib's functor (`Module.Grassmannian.exists_map_localization_eq`), to
`homPoint g`. Uniqueness of glued points (`Module.Grassmannian.eq_of_map_localization_eq`) and of
glued maps (`eq_of_chartLocal`) gives the inverse laws.

## Main results

- `AlgebraicGeometry.Grassmannian.chartPt`: the point over `B` classified by an algebra map out of
  a chart ring.
- `AlgebraicGeometry.Grassmannian.algSpec_comp_chartι_eq_iff`.
- `AlgebraicGeometry.Grassmannian.pointHom` and `AlgebraicGeometry.Grassmannian.homPoint`, with
  the naturality `AlgebraicGeometry.Grassmannian.homPoint_comp`.
- `AlgebraicGeometry.Grassmannian.representableEquiv R k n A`:
  `(affineOver A ⟶ schemeOver R k n) ≃ G(k, A ⊗[R] (Fin n → R); A)`.
- `AlgebraicGeometry.Grassmannian.representableIso R k n`:
  `(algSpec R).rightOp ⋙ yoneda.obj (schemeOver R k n) ≅ Module.Grassmannian.functor k`.

The results about points assume the named premise
`Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)`, which the instance in
`Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

variable {R : CommRingCat.{u}} {k n : ℕ}

instance : (algSpec R).Full := algSpec.fullyFaithful.full

instance : (algSpec R).Faithful := algSpec.fullyFaithful.faithful

/-- The affine scheme `Spec B` over `Spec R`, for an `R`-algebra `B`. -/
abbrev affineOver (B : CommAlgCat.{u} R) : Over (Spec R) :=
  (algSpec R).obj (op B)

/-- The counit isomorphism `B ⟶ Γ(Spec B, ⊤)` of `R`-algebras. -/
abbrev gammaCounit (B : CommAlgCat.{u} R) : B ⟶ unop ((algΓ R).obj (affineOver B)) :=
  ((algΓAlgSpecAdjunction R).counit.app (op B)).unop

instance (B : CommAlgCat.{u} R) : IsIso (gammaCounit B) := by
  dsimp only [gammaCounit]
  infer_instance

/-- The chart ring at a coordinate tuple, as an `R`-algebra. -/
abbrev chartAlg (R : CommRingCat.{u}) (I : ULift.{u} (Fin k → Fin n)) : CommAlgCat.{u} R :=
  CommAlgCat.of R (Module.Grassmannian.ChartRing R (Module.Grassmannian.coordinateTuple R I.down))

variable [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- The point of the Grassmannian over `B` classified by an algebra map out of a chart ring. -/
def chartPt (I : ULift.{u} (Fin k → Fin n)) {B : CommAlgCat.{u} R} (ψ : chartAlg R I ⟶ B) :
    (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).obj B :=
  ((Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv ψ).1

theorem chartPt_comp (I : ULift.{u} (Fin k → Fin n)) {B C : CommAlgCat.{u} R}
    (ψ : chartAlg R I ⟶ B) (h : B ⟶ C) :
    chartPt I (ψ ≫ h) =
      (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).map h (chartPt I ψ) :=
  congrArg Subtype.val
    ((Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv_comp h ψ)

/-- The point over `Γ(Spec B, ⊤)` of the map `Spec ψ` into a chart is the image of `chartPt ψ`
under the counit `B ≅ Γ(Spec B, ⊤)`. -/
theorem chartRepresentableBy_homEquiv_algSpec_map (I : ULift.{u} (Fin k → Fin n))
    {B : CommAlgCat.{u} R} (ψ : chartAlg R I ⟶ B) :
    ((chartRepresentableBy R _).homEquiv ((algSpec R).map ψ.op)).1 =
      (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).map (gammaCounit B)
        (chartPt I ψ) := by
  have h := (algΓAlgSpecAdjunction R).counit.naturality ψ.op
  change ((Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv
      (((algΓAlgSpecAdjunction R).homEquiv _ _).symm ((algSpec R).map ψ.op)).unop).1 = _
  rw [Adjunction.homEquiv_counit]
  rw [show (algΓ R).map ((algSpec R).map ψ.op) ≫
      (algΓAlgSpecAdjunction R).counit.app (op (chartAlg R I)) =
      (algΓAlgSpecAdjunction R).counit.app (op B) ≫ ψ.op from h]
  rw [unop_comp, Quiver.Hom.unop_op, Functor.CorepresentableBy.homEquiv_comp]
  rfl

/-- Two maps from `Spec B` into coordinate charts agree in the glued scheme exactly when they
classify the same point of `G(k, B ⊗[R] R^n; B)`. -/
theorem algSpec_comp_chartι_eq_iff (I J : ULift.{u} (Fin k → Fin n)) {B : CommAlgCat.{u} R}
    (ψ : chartAlg R I ⟶ B) (ψ' : chartAlg R J ⟶ B) :
    (algSpec R).map ψ.op ≫ chartι I = (algSpec R).map ψ'.op ≫ chartι J ↔
      chartPt I ψ = chartPt J ψ' := by
  constructor
  · intro h
    have h1 := point_eq_of_comp_chartι_eq I J _ _ h
    rw [chartRepresentableBy_homEquiv_algSpec_map, chartRepresentableBy_homEquiv_algSpec_map] at h1
    exact ((Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).mapIso
      (asIso (gammaCounit B))).toEquiv.injective h1
  · intro h
    apply comp_chartι_eq_of_point_eq
    rw [chartRepresentableBy_homEquiv_algSpec_map, chartRepresentableBy_homEquiv_algSpec_map, h]

/-- The localization map `A ⟶ A_r` as a map of `R`-algebras. -/
abbrev locAway {A : CommAlgCat.{u} R} (r : A) : A ⟶ CommAlgCat.of R (Localization.Away r) :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom R A (Localization.Away r))

theorem algSpec_map_locAway_left {A : CommAlgCat.{u} R} (r : A) :
    ((algSpec R).map (locAway r).op).left =
      Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of A) (Localization.Away r))) :=
  rfl

/-- A family of elements not contained in the corresponding primes generates the unit ideal. -/
theorem span_range_eq_top_of_forall_notMem {A : Type u} [CommRing A] (r : PrimeSpectrum A → A)
    (hr : ∀ p, r p ∉ p.asIdeal) : Ideal.span (Set.range r) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))

/-- Chart factorizations of a map from `Spec A` along `f₁` and `f₂` classify compatible points:
their images agree on any common target of `f₁` and `f₂`. -/
theorem chartPt_eq_of_factor {A : CommAlgCat.{u} R} (g : affineOver A ⟶ schemeOver R k n)
    {I₁ I₂ : ULift.{u} (Fin k → Fin n)} {B₁ B₂ C : CommAlgCat.{u} R} {f₁ : A ⟶ B₁}
    {f₂ : A ⟶ B₂} {ψ₁ : chartAlg R I₁ ⟶ B₁} {ψ₂ : chartAlg R I₂ ⟶ B₂}
    (hψ₁ : (algSpec R).map f₁.op ≫ g = (algSpec R).map ψ₁.op ≫ chartι I₁)
    (hψ₂ : (algSpec R).map f₂.op ≫ g = (algSpec R).map ψ₂.op ≫ chartι I₂)
    (h₁ : B₁ ⟶ C) (h₂ : B₂ ⟶ C) (hf : f₁ ≫ h₁ = f₂ ≫ h₂) :
    (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).map h₁
        (chartPt I₁ ψ₁) =
      (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).map h₂
        (chartPt I₂ ψ₂) := by
  rw [← chartPt_comp, ← chartPt_comp, ← algSpec_comp_chartι_eq_iff, op_comp, op_comp,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← hψ₁, ← hψ₂,
    ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
    ← op_comp, hf]

/-- Two maps from `Spec A` into the Grassmannian are equal if near every prime they factor through
coordinate charts with the same classified point. -/
theorem eq_of_chartLocal {A : CommAlgCat.{u} R} {g g' : affineOver A ⟶ schemeOver R k n}
    (r : PrimeSpectrum A → A) (hr : ∀ p, r p ∉ p.asIdeal)
    (H : ∀ p, ∃ (I I' : ULift.{u} (Fin k → Fin n))
      (ψ : chartAlg R I ⟶ CommAlgCat.of R (Localization.Away (r p)))
      (ψ' : chartAlg R I' ⟶ CommAlgCat.of R (Localization.Away (r p))),
      (algSpec R).map (locAway (r p)).op ≫ g = (algSpec R).map ψ.op ≫ chartι I ∧
      (algSpec R).map (locAway (r p)).op ≫ g' = (algSpec R).map ψ'.op ≫ chartι I' ∧
      chartPt I ψ = chartPt I' ψ') :
    g = g' := by
  have hspan := span_range_eq_top_of_forall_notMem (A := A) r hr
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of A) r hspan).openCover _ _
    fun p ↦ ?_
  obtain ⟨I, I', ψ, ψ', h1, h2, h3⟩ := H p
  have h := (algSpec_comp_chartι_eq_iff I I' ψ ψ').mpr h3
  change ((algSpec R).map (locAway (r p)).op).left ≫ g.left =
    ((algSpec R).map (locAway (r p)).op).left ≫ g'.left
  rw [← Over.comp_left, ← Over.comp_left, h1, h2, h]

set_option backward.isDefEq.respectTransparency.types false in
instance isOpenImmersion_glueData_ι (I : ULift.{u} (Fin k → Fin n)) :
    IsOpenImmersion ((glueData R k n).ι I) :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- Near every prime, a map from `Spec A` into the Grassmannian factors through a coordinate
chart. -/
theorem exists_chartLocal {A : CommAlgCat.{u} R} (g : affineOver A ⟶ schemeOver R k n)
    (p : PrimeSpectrum A) :
    ∃ (r : A) (_ : r ∉ p.asIdeal) (I : ULift.{u} (Fin k → Fin n))
      (ψ : chartAlg R I ⟶ CommAlgCat.of R (Localization.Away r)),
      (algSpec R).map (locAway r).op ≫ g = (algSpec R).map ψ.op ≫ chartι I := by
  obtain ⟨(I : ULift.{u} (Fin k → Fin n)), y, hy⟩ :=
    (glueData R k n).ι_jointly_surjective (g.left p)
  let V := g.left ⁻¹ᵁ ((glueData R k n).ι I).opensRange
  have hV : IsOpen ((V : Set (affineOver A).left) : Set (PrimeSpectrum A)) := V.isOpen
  have hpV : p ∈ ((V : Set (affineOver A).left) : Set (PrimeSpectrum A)) := ⟨y, hy⟩
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open hpV hV
  refine ⟨r, hpr, I, ?_⟩
  have hrange : Set.range (((algSpec R).map (locAway r).op).left ≫ g.left) ⊆
      Set.range ((glueData R k n).ι I) := by
    rintro _ ⟨z, rfl⟩
    have hz : ((algSpec R).map (locAway r).op).left z ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum A)) := by
      have hmem : (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of A)
          (Localization.Away r)))) z ∈ (Spec.map (CommRingCat.ofHom (algebraMap
            (CommRingCat.of A) (Localization.Away r)))).opensRange := ⟨z, rfl⟩
      rw [Scheme.Hom.opensRange_localizationAway] at hmem
      exact hmem
    obtain ⟨y', hy'⟩ := hrV hz
    exact ⟨y', by rw [Scheme.Hom.comp_apply]; exact hy'⟩
  let a := IsOpenImmersion.lift ((glueData R k n).ι I) _ hrange
  let aO : affineOver (CommAlgCat.of R (Localization.Away r)) ⟶
      chartScheme R (Module.Grassmannian.coordinateTuple R I.down) :=
    Over.homMk a (by
      have h1 : a ≫ (glueData R k n).ι I = ((algSpec R).map (locAway r).op).left ≫ g.left :=
        IsOpenImmersion.lift_fac ((glueData R k n).ι I) _ hrange
      have h2 := ι_toBase (R := R) (k := k) (n := n) I
      have h3 : g.left ≫ toBase R k n = (affineOver A).hom := Over.w g
      have h4 : ((algSpec R).map (locAway r).op).left ≫ (affineOver A).hom =
          (affineOver (CommAlgCat.of R (Localization.Away r))).hom := Over.w _
      exact ((congrArg (fun t ↦ a ≫ t) h2.symm).trans (Category.assoc _ _ _).symm).trans
        ((congrArg (fun t ↦ t ≫ toBase R k n) h1).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun t ↦ ((algSpec R).map (locAway r).op).left ≫ t) h3).trans h4))))
  refine ⟨((algSpec R).preimage aO).unop, ?_⟩
  rw [Quiver.Hom.op_unop, Functor.map_preimage]
  apply Over.OverMorphism.ext
  exact (IsOpenImmersion.lift_fac ((glueData R k n).ι I) _ hrange).symm

/-- Naturality of the counit `B ≅ Γ(Spec B, ⊤)`. -/
theorem gammaCounit_naturality {B C : CommAlgCat.{u} R} (φ : B ⟶ C) :
    φ ≫ gammaCounit C = gammaCounit B ≫ ((algΓ R).map ((algSpec R).map φ.op)).unop := by
  have h := (algΓAlgSpecAdjunction R).counit.naturality φ.op
  exact (congrArg Quiver.Hom.unop h).symm

/-- The point over `Γ(T, ⊤)` classified by `t ≫ Spec ψ`, for `t : T ⟶ Spec B`. -/
theorem chartRepresentableBy_homEquiv_comp_algSpec_map (I : ULift.{u} (Fin k → Fin n))
    {T : Over (Spec R)} {B : CommAlgCat.{u} R} (t : T ⟶ affineOver B) (ψ : chartAlg R I ⟶ B) :
    ((chartRepresentableBy R _).homEquiv (t ≫ (algSpec R).map ψ.op)).1 =
      (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).map
        (gammaCounit B ≫ ((algΓ R).map t).unop) (chartPt I ψ) := by
  rw [Functor.RepresentableBy.homEquiv_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    ← chartRepresentableBy_homEquiv_algSpec_map]
  rfl

/-- Moving an algebra map across the counit and global sections. -/
theorem comp_gammaCounit_comp {T : Over (Spec R)} {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (t : T ⟶ affineOver B) :
    f ≫ gammaCounit B ≫ ((algΓ R).map t).unop =
      gammaCounit A ≫ ((algΓ R).map (t ≫ (algSpec R).map f.op)).unop := by
  rw [← Category.assoc, gammaCounit_naturality, Category.assoc, Functor.map_comp, unop_comp]

section Points

variable {A : CommAlgCat.{u} R}
  (N : (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).obj A)

/-- A coordinate chart containing the point `N` near the prime `p`. -/
def pointChartIndex (p : PrimeSpectrum A) : ULift.{u} (Fin k → Fin n) :=
  ⟨(Module.Grassmannian.exists_mem_chart_map N p).choose⟩

/-- An element outside `p` on whose basic open the point `N` lies in `pointChartIndex N p`. -/
def pointChartElem (p : PrimeSpectrum A) : A :=
  (Module.Grassmannian.exists_mem_chart_map N p).choose_spec.choose

theorem pointChartElem_notMem (p : PrimeSpectrum A) : pointChartElem N p ∉ p.asIdeal :=
  (Module.Grassmannian.exists_mem_chart_map N p).choose_spec.choose_spec.1

theorem map_locAway_mem_chart (p : PrimeSpectrum A) :
    (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).map
        (locAway (pointChartElem N p)) N ∈
      (Module.Grassmannian.chartFunctor.{u, u, u} R
        (Module.Grassmannian.coordinateTuple R (pointChartIndex N p).down)).obj
        (CommAlgCat.of R (Localization.Away (pointChartElem N p))) :=
  (Module.Grassmannian.exists_mem_chart_map N p).choose_spec.choose_spec.2 _
    (by
      exact IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (pointChartElem N p)) (pointChartElem N p))

/-- The algebra map out of the chart ring classifying `N` near `p`. -/
def pointChartAlgHom (p : PrimeSpectrum A) :
    chartAlg R (pointChartIndex N p) ⟶ CommAlgCat.of R (Localization.Away (pointChartElem N p)) :=
  (Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv.symm
    ⟨_, map_locAway_mem_chart N p⟩

theorem chartPt_pointChartAlgHom (p : PrimeSpectrum A) :
    chartPt (pointChartIndex N p) (pointChartAlgHom N p) =
      (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).map
        (locAway (pointChartElem N p)) N :=
  congrArg Subtype.val
    ((Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv.apply_symm_apply _)

theorem span_pointChartElem : Ideal.span (Set.range (pointChartElem N)) = ⊤ :=
  span_range_eq_top_of_forall_notMem _ (pointChartElem_notMem N)

/-- The cover of `Spec A` by the basic opens of `pointChartElem N`. -/
abbrev pointCover : (Spec (CommRingCat.of A)).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of A) (pointChartElem N)
    (span_pointChartElem N)).openCover

/-- The local map `Spec A_r ⟶ Gr` classifying `N` near `p`. -/
def pointLocalHom (p : PrimeSpectrum A) :
    affineOver (CommAlgCat.of R (Localization.Away (pointChartElem N p))) ⟶ schemeOver R k n :=
  (algSpec R).map (pointChartAlgHom N p).op ≫ chartι (pointChartIndex N p)

theorem pointLocalHom_compat (p q : PrimeSpectrum A) :
    pullback.fst ((pointCover N).f p) ((pointCover N).f q) ≫ (pointLocalHom N p).left =
      pullback.snd ((pointCover N).f p) ((pointCover N).f q) ≫ (pointLocalHom N q).left := by
  let P : Over (Spec R) := Over.mk (pullback.fst ((pointCover N).f p) ((pointCover N).f q) ≫
    (affineOver (CommAlgCat.of R (Localization.Away (pointChartElem N p)))).hom)
  let fstO : P ⟶ affineOver (CommAlgCat.of R (Localization.Away (pointChartElem N p))) :=
    Over.homMk (pullback.fst _ _) rfl
  let sndO : P ⟶ affineOver (CommAlgCat.of R (Localization.Away (pointChartElem N q))) :=
    Over.homMk (pullback.snd _ _) (by
      have hp := Over.w ((algSpec R).map (locAway (pointChartElem N p)).op)
      have hq := Over.w ((algSpec R).map (locAway (pointChartElem N q)).op)
      exact (congrArg (pullback.snd ((pointCover N).f p) ((pointCover N).f q) ≫ ·) hq.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (affineOver A).hom) pullback.condition.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (pullback.fst ((pointCover N).f p) ((pointCover N).f q) ≫ ·) hp)))))
  have hcond : fstO ≫ (algSpec R).map (locAway (pointChartElem N p)).op =
      sndO ≫ (algSpec R).map (locAway (pointChartElem N q)).op :=
    Over.OverMorphism.ext pullback.condition
  have key : fstO ≫ pointLocalHom N p = sndO ≫ pointLocalHom N q := by
    simp only [pointLocalHom, ← Category.assoc]
    apply comp_chartι_eq_of_point_eq
    rw [chartRepresentableBy_homEquiv_comp_algSpec_map,
      chartRepresentableBy_homEquiv_comp_algSpec_map, chartPt_pointChartAlgHom,
      chartPt_pointChartAlgHom, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp, comp_gammaCounit_comp, comp_gammaCounit_comp, hcond]
  exact congrArg CommaMorphism.left key

/-- The map `Spec A ⟶ Gr` over `Spec R` classifying the point `N`, glued from the local maps. -/
def pointHom : affineOver A ⟶ schemeOver R k n :=
  Over.homMk ((pointCover N).glueMorphisms (fun p ↦ (pointLocalHom N p).left)
    (pointLocalHom_compat N)) (by
      refine Scheme.Cover.hom_ext (pointCover N) _ _ fun (p : PrimeSpectrum A) ↦ ?_
      exact (Scheme.Cover.ι_glueMorphisms_assoc (pointCover N)
        (fun p ↦ (pointLocalHom N p).left) (pointLocalHom_compat N) p _).trans
        ((Over.w (pointLocalHom N p)).trans
          (Over.w ((algSpec R).map (locAway (pointChartElem N p)).op)).symm))

theorem locAway_comp_pointHom (p : PrimeSpectrum A) :
    (algSpec R).map (locAway (pointChartElem N p)).op ≫ pointHom N = pointLocalHom N p := by
  apply Over.OverMorphism.ext
  exact Scheme.Cover.ι_glueMorphisms (pointCover N) _ (pointLocalHom_compat N) p

end Points

set_option hygiene false in
/-- Mathlib's Grassmannian functor `A ↦ G(k, A ⊗[R] (Fin n → R); A)` on `R`-algebras. -/
local notation "𝐆" => Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k

section Morphisms

variable {A : CommAlgCat.{u} R}

/-- The map `A_a ⟶ B_b` induced by `f : A ⟶ B` when `f a` becomes a unit in `B_b`. -/
def awayLift {B : CommAlgCat.{u} R} (f : A ⟶ B) (a : A) (b : B)
    (hu : IsUnit (algebraMap B (Localization.Away b) (f a))) :
    CommAlgCat.of R (Localization.Away a) ⟶ CommAlgCat.of R (Localization.Away b) :=
  CommAlgCat.ofHom (IsLocalization.liftAlgHom (M := Submonoid.powers a)
    (f := (IsScalarTower.toAlgHom R B (Localization.Away b)).comp f.hom) (by
      rintro ⟨_, m, rfl⟩
      simpa using hu.pow m))

theorem locAway_comp_awayLift {B : CommAlgCat.{u} R} (f : A ⟶ B) (a : A) (b : B)
    (hu : IsUnit (algebraMap B (Localization.Away b) (f a))) :
    locAway a ≫ awayLift f a b hu = f ≫ locAway b := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp [awayLift, locAway, IsLocalization.lift_eq]

/-- A chart factorization along `f` restricts along any further algebra map. -/
theorem factor_comp {B C : CommAlgCat.{u} R} {g : affineOver A ⟶ schemeOver R k n} {f : A ⟶ B}
    {I : ULift.{u} (Fin k → Fin n)} {ψ : chartAlg R I ⟶ B}
    (hψ : (algSpec R).map f.op ≫ g = (algSpec R).map ψ.op ≫ chartι I) (h : B ⟶ C) :
    (algSpec R).map (f ≫ h).op ≫ g = (algSpec R).map (ψ ≫ h).op ≫ chartι I := by
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hψ]

theorem span_range_eq_top_of_forall_exists_notMem {ι : Type*} {B : Type u} [CommRing B]
    (r : ι → B) (h : ∀ q : PrimeSpectrum B, ∃ i, r i ∉ q.asIdeal) :
    Ideal.span (Set.range r) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨i, hi⟩ := h ⟨m, hm.isPrime⟩
  exact hi (hle (Ideal.subset_span ⟨i, rfl⟩))

variable (g : affineOver A ⟶ schemeOver R k n)

/-- An element outside `p` on whose basic open `g` factors through a coordinate chart. -/
def homChartElem (p : PrimeSpectrum A) : A :=
  (exists_chartLocal g p).choose

theorem homChartElem_notMem (p : PrimeSpectrum A) : homChartElem g p ∉ p.asIdeal :=
  (exists_chartLocal g p).choose_spec.choose

/-- The coordinate chart through which `g` factors near `p`. -/
def homChartIndex (p : PrimeSpectrum A) : ULift.{u} (Fin k → Fin n) :=
  (exists_chartLocal g p).choose_spec.choose_spec.choose

/-- The algebra map out of the chart ring through which `g` factors near `p`. -/
def homChartAlgHom (p : PrimeSpectrum A) :
    chartAlg R (homChartIndex g p) ⟶ CommAlgCat.of R (Localization.Away (homChartElem g p)) :=
  (exists_chartLocal g p).choose_spec.choose_spec.choose_spec.choose

theorem homChartAlgHom_spec (p : PrimeSpectrum A) :
    (algSpec R).map (locAway (homChartElem g p)).op ≫ g =
      (algSpec R).map (homChartAlgHom g p).op ≫ chartι (homChartIndex g p) :=
  (exists_chartLocal g p).choose_spec.choose_spec.choose_spec.choose_spec

theorem exists_finset_span_homChartElem :
    ∃ F : Finset (PrimeSpectrum A), Ideal.span (Set.range fun i : F ↦ homChartElem g i.1) = ⊤ := by
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun p ↦ (PrimeSpectrum.basicOpen (homChartElem g p) : Set (PrimeSpectrum A)))
    (fun p ↦ PrimeSpectrum.isOpen_basicOpen)
    (fun q _ ↦ Set.mem_iUnion.mpr ⟨q, homChartElem_notMem g q⟩)
  refine ⟨F, span_range_eq_top_of_forall_exists_notMem _ fun q ↦ ?_⟩
  obtain ⟨p, hp, hq⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ q))
  exact ⟨⟨p, hp⟩, hq⟩

/-- A finite family of primes whose chart elements generate the unit ideal. -/
def homFinset : Finset (PrimeSpectrum A) :=
  (exists_finset_span_homChartElem g).choose

/-- The chart elements of `g` on `homFinset g`. -/
abbrev homElem (i : homFinset g) : A :=
  homChartElem g i.1

theorem span_homElem : Ideal.span (Set.range (homElem g)) = ⊤ :=
  (exists_finset_span_homChartElem g).choose_spec

/-- The overlap ring of the localizations at `homElem g i` and `homElem g j`. -/
abbrev homOverlap (i j : homFinset g) : Type u :=
  Localization.Away (algebraMap A (Localization.Away (homElem g j)) (homElem g i))

/-- The map from `A_{s i}` to the overlap ring. -/
def homOverlapMap (i j : homFinset g) :
    Localization.Away (homElem g i) →ₐ[R] homOverlap g i j :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (homElem g i))
    (f := (IsScalarTower.toAlgHom R (Localization.Away (homElem g j)) (homOverlap g i j)).comp
      (IsScalarTower.toAlgHom R A (Localization.Away (homElem g j)))) (by
      rintro ⟨_, m, rfl⟩
      simpa using (IsLocalization.Away.algebraMap_isUnit (S := homOverlap g i j)
        (algebraMap A (Localization.Away (homElem g j)) (homElem g i))).pow m)

theorem homOverlapMap_comp (i j : homFinset g) :
    (homOverlapMap g i j).comp (IsScalarTower.toAlgHom R A (Localization.Away (homElem g i))) =
      (IsScalarTower.toAlgHom R (Localization.Away (homElem g j)) (homOverlap g i j)).comp
        (IsScalarTower.toAlgHom R A (Localization.Away (homElem g j))) := by
  apply AlgHom.ext
  intro a
  simp [homOverlapMap, IsLocalization.lift_eq]

theorem homOverlap_compat (i j : homFinset g) :
    Module.Grassmannian.map (homOverlapMap g i j) (chartPt (homChartIndex g i.1)
        (homChartAlgHom g i.1)) =
      Module.Grassmannian.map
        (IsScalarTower.toAlgHom R (Localization.Away (homElem g j)) (homOverlap g i j))
        (chartPt (homChartIndex g j.1) (homChartAlgHom g j.1)) :=
  chartPt_eq_of_factor g (homChartAlgHom_spec g i.1) (homChartAlgHom_spec g j.1)
    (C := CommAlgCat.of R (homOverlap g i j)) (CommAlgCat.ofHom (homOverlapMap g i j))
    (CommAlgCat.ofHom (IsScalarTower.toAlgHom R _ _))
    (CommAlgCat.hom_ext (homOverlapMap_comp g i j))

theorem exists_homPoint :
    ∃ N₀ : (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).obj A,
      ∀ i : homFinset g, Module.Grassmannian.map
        (IsScalarTower.toAlgHom R A (Localization.Away (homElem g i))) N₀ =
          chartPt (homChartIndex g i.1) (homChartAlgHom g i.1) :=
  Module.Grassmannian.exists_map_localization_eq (homElem g) (span_homElem g)
    (fun i ↦ chartPt (homChartIndex g i.1) (homChartAlgHom g i.1)) (homOverlap g)
    (homOverlapMap g) (homOverlapMap_comp g) (homOverlap_compat g)

/-- The point of the Grassmannian over `A` classified by a map `Spec A ⟶ Gr`. -/
def homPoint : (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).obj A :=
  (exists_homPoint g).choose

theorem homPoint_spec (i : homFinset g) :
    Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away (homElem g i)))
        (homPoint g) = chartPt (homChartIndex g i.1) (homChartAlgHom g i.1) :=
  (exists_homPoint g).choose_spec i

/-- Along any chart factorization of `g`, the point `homPoint g` restricts to the classified
point. -/
theorem map_homPoint_of_factor {B : CommAlgCat.{u} R} {f : A ⟶ B}
    {I : ULift.{u} (Fin k → Fin n)} {ψ : chartAlg R I ⟶ B}
    (hψ : (algSpec R).map f.op ≫ g = (algSpec R).map ψ.op ≫ chartι I) :
    𝐆.map f (homPoint g) = chartPt I ψ := by
  have hspan : Ideal.span (Set.range fun i : homFinset g ↦ f (homElem g i)) = ⊤ := by
    have h := congrArg (Ideal.map f.hom) (span_homElem g)
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  refine Module.Grassmannian.eq_of_map_localization_eq (fun i : homFinset g ↦ f (homElem g i))
    hspan fun i ↦ ?_
  have hu : IsUnit (algebraMap B (Localization.Away (f (homElem g i))) (f (homElem g i))) :=
    IsLocalization.Away.algebraMap_isUnit _
  have key := chartPt_eq_of_factor g (homChartAlgHom_spec g i.1) hψ
    (awayLift f (homElem g i) (f (homElem g i)) hu) (locAway (f (homElem g i)))
    (locAway_comp_awayLift f _ _ hu)
  change 𝐆.map (locAway (f (homElem g i))) (𝐆.map f (homPoint g)) =
    𝐆.map (locAway (f (homElem g i))) (chartPt I ψ)
  rw [← key, ← Functor.map_comp_apply, ← locAway_comp_awayLift f _ _ hu,
    Functor.map_comp_apply]
  exact congrArg (fun x ↦ 𝐆.map (awayLift f (homElem g i) (f (homElem g i)) hu) x)
    (homPoint_spec g i)

/-- Naturality of `homPoint` in the test algebra. -/
theorem homPoint_comp {B : CommAlgCat.{u} R} (h : A ⟶ B) :
    homPoint ((algSpec R).map h.op ≫ g) = 𝐆.map h (homPoint g) := by
  refine Module.Grassmannian.eq_of_map_localization_eq (homElem ((algSpec R).map h.op ≫ g))
    (span_homElem _) fun i ↦ ?_
  have h2 := map_homPoint_of_factor g
    (f := h ≫ locAway (homElem ((algSpec R).map h.op ≫ g) i))
    (I := homChartIndex ((algSpec R).map h.op ≫ g) i.1)
    (ψ := homChartAlgHom ((algSpec R).map h.op ≫ g) i.1) (by
      rw [op_comp, Functor.map_comp, Category.assoc]
      exact homChartAlgHom_spec _ i.1)
  rw [Functor.map_comp_apply] at h2
  exact (homPoint_spec _ i).trans h2.symm

end Morphisms

section Inverse

variable {A : CommAlgCat.{u} R}

/-- The localization map `A_a ⟶ A_r` for `a ∣ r`. -/
def awayDvd {a r : A} (h : a ∣ r) :
    CommAlgCat.of R (Localization.Away a) ⟶ CommAlgCat.of R (Localization.Away r) :=
  awayLift (𝟙 A) a r (by
    simpa using isUnit_of_dvd_unit (map_dvd (algebraMap A (Localization.Away r)) h)
      (IsLocalization.Away.algebraMap_isUnit r))

theorem locAway_comp_awayDvd {a r : A} (h : a ∣ r) : locAway a ≫ awayDvd h = locAway r := by
  rw [awayDvd, locAway_comp_awayLift, Category.id_comp]

theorem homPoint_pointHom (N : 𝐆.obj A) : homPoint (pointHom N) = N := by
  refine Module.Grassmannian.eq_of_map_localization_eq (pointChartElem N) (span_pointChartElem N)
    fun p ↦ ?_
  exact (map_homPoint_of_factor (pointHom N) (I := pointChartIndex N p)
    (ψ := pointChartAlgHom N p) (locAway_comp_pointHom N p)).trans (chartPt_pointChartAlgHom N p)

theorem pointHom_homPoint (g : affineOver A ⟶ schemeOver R k n) : pointHom (homPoint g) = g := by
  refine eq_of_chartLocal (fun p ↦ pointChartElem (homPoint g) p * homChartElem g p)
    (fun p ↦ p.isPrime.mul_notMem (pointChartElem_notMem _ p) (homChartElem_notMem g p))
    fun p ↦ ?_
  have ha := dvd_mul_right (pointChartElem (homPoint g) p) (homChartElem g p)
  have hb := dvd_mul_left (homChartElem g p) (pointChartElem (homPoint g) p)
  have h1 := factor_comp (I := pointChartIndex (homPoint g) p)
    (ψ := pointChartAlgHom (homPoint g) p) (locAway_comp_pointHom (homPoint g) p) (awayDvd ha)
  have h2 := factor_comp (homChartAlgHom_spec g p) (awayDvd hb)
  rw [locAway_comp_awayDvd] at h1 h2
  refine ⟨_, _, _, _, h1, h2, ?_⟩
  rw [chartPt_comp, chartPt_comp, chartPt_pointChartAlgHom,
    ← map_homPoint_of_factor g (homChartAlgHom_spec g p), ← Functor.map_comp_apply,
    ← Functor.map_comp_apply, locAway_comp_awayDvd, locAway_comp_awayDvd]

end Inverse

variable (R k n) in
/-- **Representability on affine test schemes**: maps `Spec A ⟶ Gr` over `Spec R` correspond to
points of Mathlib's Grassmannian `G(k, A ⊗[R] (Fin n → R); A)`, the submodules whose quotient is
finite projective of rank `k`.

Sources: Nitsure, arXiv:math/0504590v1, §1 "Construction of Grassmannian", subsection
"Construction by gluing together affine patches", pp. 7–8; Stacks, Tag 089T (TeX snapshot
`a04446e5`). Encoded subset: the free module `R^n` over an affine base `Spec R`, affine test
schemes `Spec A` with `A : CommAlgCat.{u} R`, and all `k` and `n`. Convention: Mathlib's `k` is
the rank of the quotient, so this is Nitsure's `Grass(n, k)` and Stacks' `G(n - k, n)`, base-changed
to `R`. Premise: the instance argument `Module.Grassmannian.BaseChangeMkQFormula`, supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
def representableEquiv (A : CommAlgCat.{u} R) :
    (affineOver A ⟶ schemeOver R k n) ≃ 𝐆.obj A where
  toFun := homPoint
  invFun := pointHom
  left_inv := pointHom_homPoint
  right_inv := homPoint_pointHom

variable (R k n) in
/-- **The glued Grassmannian represents Mathlib's functor** `Module.Grassmannian.functor` on
`R`-algebras: a natural isomorphism `Hom_{Spec R}(Spec A, Gr) ≅ G(k, A ⊗[R] (Fin n → R); A)`.

Sources: Nitsure, arXiv:math/0504590v1, §1 "Construction of Grassmannian", subsection
"Construction by gluing together affine patches", pp. 7–8; Stacks, Tag 089T (TeX snapshot
`a04446e5`). Encoded subset: the free module `R^n` over an affine base `Spec R`, affine test
schemes `Spec A` with `A : CommAlgCat.{u} R`, and all `k` and `n`. Convention: Mathlib's `k` is
the rank of the quotient, so this is Nitsure's `Grass(n, k)` and Stacks' `G(n - k, n)`, base-changed
to `R`. Premise: the instance argument `Module.Grassmannian.BaseChangeMkQFormula`, supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
def representableIso :
    (algSpec R).rightOp ⋙ yoneda.obj (schemeOver R k n) ≅ 𝐆 :=
  NatIso.ofComponents (fun A ↦ (representableEquiv R k n A).toIso) fun {A B} h ↦ by
    ext g
    exact homPoint_comp g h

end AlgebraicGeometry.Grassmannian

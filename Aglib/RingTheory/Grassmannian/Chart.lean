/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.BaseChange
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Affine charts of the Grassmannian functor

For a `k`-tuple `x : Fin k → M`, the chart `chart R x ⊆ G(k, M; R)` consists of the points `N`
whose composite `R^k → M → M ⧸ N` is bijective. Base change preserves this condition, so the
charts at the tuples `b ↦ 1 ⊗ x b` form the subfunctor `chartFunctor R x` of
`Module.Grassmannian.functor R M k`. These are the chart and chart functor listed as TODO in
Mathlib's `Mathlib/RingTheory/Grassmannian.lean`.

Over an `R`-algebra `A`, a point of the chart at `1 ⊗ x` is the same as an `R`-linear map
`φ : M → A^k` sending `x b` to the `b`-th standard basis vector: the point is the kernel of the
`A`-linear extension of `φ`, and `φ` is the inverse of the chart isomorphism composed with the
quotient map (`chartEquiv`). This is the chart description of the Grassmannian in Stacks,
Tag 089T (representability of the subfunctors `F_i`), and in Nitsure, *Construction of Hilbert
and Quot schemes* (arXiv:math/0504590v1), §1, "Construction of Grassmannian", pp. 7–8, where
the chart `U^I` carries the matrix `X^I` whose `I`-th minor is the identity.

## Main definitions and results

- `Module.Grassmannian.chartMap`: the composite `R^k → M → M ⧸ N`.
- `Module.Grassmannian.chart`: the points at which `chartMap x` is bijective.
- `Module.Grassmannian.map_mem_chart`: base change preserves the chart condition.

Every statement about Mathlib's `map` assumes the named premise `BaseChangeMkQFormula`
(see `Aglib.RingTheory.Grassmannian.BaseChange`).
- `Module.Grassmannian.chartFunctor`: the chart as a subfunctor of the Grassmannian functor.
- `Module.Grassmannian.chartEquiv`: the chart over `A` is in bijection with the `R`-linear maps
  `φ : M → A^k` with `φ (x b) = Pi.single b 1`; `chartEquiv_map` proves naturality in `A`.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

section ChartMap

/-- The composite `R^k → M → M ⧸ N` that sends the `b`-th standard basis vector to the class
of `x b`. -/
def chartMap (x : Fin k → M) (N : Submodule R M) : (Fin k → R) →ₗ[R] M ⧸ N :=
  N.mkQ ∘ₗ Fintype.linearCombination R x

theorem chartMap_eq_linearCombination (x : Fin k → M) (N : Submodule R M) :
    chartMap x N = Fintype.linearCombination R (fun b ↦ N.mkQ (x b)) := by
  ext c
  simp [chartMap, Fintype.linearCombination_apply]

@[simp]
theorem chartMap_single (x : Fin k → M) (N : Submodule R M) (b : Fin k) :
    chartMap x N (Pi.single b 1) = Submodule.Quotient.mk (x b) := by
  simp [chartMap]

end ChartMap

variable (R) in
/-- The chart of `G(k, M; R)` at a tuple `x : Fin k → M`: the points `N` whose composite
`R^k → M → M ⧸ N` is bijective (Stacks, Tag 089T, the subfunctors `F_i`). -/
def chart (x : Fin k → M) : Set G(k, M; R) :=
  {N | Function.Bijective (chartMap x N.toSubmodule)}

theorem mem_chart_iff {x : Fin k → M} {N : G(k, M; R)} :
    N ∈ chart R x ↔ Function.Bijective (chartMap x N.toSubmodule) :=
  Iff.rfl

/-- The tuple `b ↦ 1 ⊗ x b` of `A ⊗[R] M`. -/
abbrev baseChangeTuple (A : Type w) [CommRing A] [Algebra R A] (x : Fin k → M) :
    Fin k → A ⊗[R] M :=
  fun b ↦ (1 : A) ⊗ₜ[R] x b

section BaseChange

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
variable [BaseChangeMkQFormula.{u, v, w} R M]

/-- The image under base change of a point of the chart at `1 ⊗ x` is in the chart at `1 ⊗ x`.
The images of the vectors `1 ⊗ x b` form the base change of the basis of the quotient
(Stacks, Tag 089T: `F_i` is a subfunctor of `F`). -/
theorem map_mem_chart (f : A →ₐ[R] B) (x : Fin k → M) {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) :
    map f N ∈ chart B (baseChangeTuple B x) := by
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  set e := LinearEquiv.ofBijective _ hN
  let bQ : Basis (Fin k) A ((A ⊗[R] M) ⧸ N.toSubmodule) := (Pi.basisFun A (Fin k)).map e
  let bB : Basis (Fin k) B (B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule)) :=
    Algebra.TensorProduct.basis B bQ
  let E := (Submodule.quotEquivOfEq _ _ (map_toSubmodule f N)).trans
    (baseChangeMkQQuotEquiv (B := B) N.toSubmodule)
  have key : E.toLinearMap ∘ₗ chartMap (baseChangeTuple B x) (map f N).toSubmodule =
      bB.equivFun.symm.toLinearMap := by
    refine LinearMap.pi_ext' fun b ↦ LinearMap.ext_ring ?_
    have he : e (Pi.single b 1) = Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] x b) :=
      chartMap_single _ _ b
    simp [bB, bQ, E, Algebra.TensorProduct.basis_apply, he]
  have hcomp : chartMap (baseChangeTuple B x) (map f N).toSubmodule =
      E.symm.toLinearMap ∘ₗ bB.equivFun.symm.toLinearMap := by
    rw [← key]
    ext c
    simp
  rw [mem_chart_iff, hcomp, LinearMap.coe_comp]
  exact E.symm.bijective.comp bB.equivFun.symm.bijective

/-- The chart condition after base change: under the identification of the quotient of
`map f N` with `B ⊗[A] ((A ⊗[R] M) ⧸ N)`, the chart map of `map f N` is the base change of the
chart map of `N`. Hence `map f N` lies in the chart at `1 ⊗ x` exactly when that base change is
bijective. -/
theorem mem_chart_map_iff (f : A →ₐ[R] B) (x : Fin k → M) (N : G(k, A ⊗[R] M; A)) :
    map f N ∈ chart B (baseChangeTuple B x) ↔
      letI : Algebra A B := f.toAlgebra
      Function.Bijective ((chartMap (baseChangeTuple A x) N.toSubmodule).baseChange B) := by
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  let E := (Submodule.quotEquivOfEq _ _ (map_toSubmodule f N)).trans
    (baseChangeMkQQuotEquiv (B := B) N.toSubmodule)
  let P := TensorProduct.piScalarRight A B B (Fin k)
  have key : E.toLinearMap ∘ₗ chartMap (baseChangeTuple B x) (map f N).toSubmodule =
      (chartMap (baseChangeTuple A x) N.toSubmodule).baseChange B ∘ₗ P.symm.toLinearMap := by
    refine LinearMap.pi_ext' fun b ↦ LinearMap.ext_ring ?_
    simp [E, P]
  have hcomp : chartMap (baseChangeTuple B x) (map f N).toSubmodule =
      E.symm.toLinearMap ∘ₗ
        ((chartMap (baseChangeTuple A x) N.toSubmodule).baseChange B ∘ₗ P.symm.toLinearMap) := by
    rw [← key]
    ext c
    simp
  change Function.Bijective (chartMap (baseChangeTuple B x) (map f N).toSubmodule) ↔ _
  rw [hcomp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.Bijective.of_comp_iff' E.symm.bijective, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.Bijective.of_comp_iff _ P.symm.bijective]

/-- `mem_chart_map_iff` for an algebra structure on `B` over `A` whose algebra map is `f`, for
example the given structure on a localization. -/
theorem mem_chart_map_iff_of_algebraMap (f : A →ₐ[R] B) [inst : Algebra A B]
    (hf : ∀ a, algebraMap A B a = f a) (x : Fin k → M) (N : G(k, A ⊗[R] M; A)) :
    map f N ∈ chart B (baseChangeTuple B x) ↔
      Function.Bijective ((chartMap (baseChangeTuple A x) N.toSubmodule).baseChange B) := by
  obtain rfl : inst = f.toAlgebra := Algebra.algebra_ext _ _ hf
  exact mem_chart_map_iff f x N

end BaseChange

variable (R) in
/-- The chart at `x : Fin k → M` as a subfunctor of `Module.Grassmannian.functor R M k`: over
an `R`-algebra `A` it is the chart at the tuple `b ↦ 1 ⊗ x b` of `A ⊗[R] M`. -/
def chartFunctor [BaseChangeMkQFormula.{u, v, w} R M] (x : Fin k → M) :
    Subfunctor (functor.{u, v, w} (R := R) (M := M) k) where
  obj A := chart A (baseChangeTuple A x)
  map f _ hN := map_mem_chart f.hom x hN

@[simp]
theorem mem_chartFunctor_obj_iff [BaseChangeMkQFormula.{u, v, w} R M] (x : Fin k → M)
    (A : CommAlgCat.{w} R)
    (N : (functor.{u, v, w} (R := R) (M := M) k).obj A) :
    N ∈ (chartFunctor.{u, v, w} R x).obj A ↔ N ∈ chart A (baseChangeTuple A x) :=
  Iff.rfl

section Sections

variable (R) (A : Type w) [CommRing A] [Algebra R A]

/-- The linear sections of a chart: `R`-linear maps `φ : M → A^k` sending `x b` to the `b`-th
standard basis vector. -/
def chartSections (x : Fin k → M) : Set (M →ₗ[R] (Fin k → A)) :=
  {φ | ∀ b, φ (x b) = Pi.single b 1}

variable {R A}

theorem liftBaseChange_surjective {x : Fin k → M} {φ : M →ₗ[R] (Fin k → A)}
    (hφ : φ ∈ chartSections R A x) : Function.Surjective (φ.liftBaseChange A) := by
  intro c
  refine ⟨∑ b, c b ⊗ₜ[R] x b, ?_⟩
  have hφ' : ∀ b, φ (x b) = Pi.single b 1 := hφ
  simp only [map_sum, LinearMap.liftBaseChange_tmul, hφ']
  ext a
  simp [Finset.sum_apply, Pi.single_apply]

/-- The point of `G(k, A ⊗[R] M; A)` cut out by a linear section `φ`: the kernel of the
`A`-linear extension `A ⊗[R] M → A^k` of `φ`. Its quotient is identified with `A^k`. -/
def ofChartSection {x : Fin k → M} (φ : M →ₗ[R] (Fin k → A)) (hφ : φ ∈ chartSections R A x) :
    G(k, A ⊗[R] M; A) :=
  let e := (φ.liftBaseChange A).quotKerEquivOfSurjective (liftBaseChange_surjective hφ)
  { toSubmodule := LinearMap.ker (φ.liftBaseChange A)
    finite_quotient := Module.Finite.equiv e.symm
    projective_quotient := Module.Projective.of_equiv e.symm
    rankAtStalk_eq := fun p ↦ by
      have := p.nontrivial
      rw [rankAtStalk_eq_of_equiv e, rankAtStalk_eq_finrank_of_free]
      simp }

theorem ofChartSection_toSubmodule {x : Fin k → M} (φ : M →ₗ[R] (Fin k → A))
    (hφ : φ ∈ chartSections R A x) :
    (ofChartSection φ hφ).toSubmodule = LinearMap.ker (φ.liftBaseChange A) :=
  rfl

/-- The quotient of `ofChartSection φ` is identified with `A^k` by the extension of `φ`. -/
def ofChartSectionQuotientEquiv {x : Fin k → M} (φ : M →ₗ[R] (Fin k → A))
    (hφ : φ ∈ chartSections R A x) :
    ((A ⊗[R] M) ⧸ (ofChartSection φ hφ).toSubmodule) ≃ₗ[A] (Fin k → A) :=
  (φ.liftBaseChange A).quotKerEquivOfSurjective (liftBaseChange_surjective hφ)

@[simp]
theorem ofChartSectionQuotientEquiv_mk {x : Fin k → M} (φ : M →ₗ[R] (Fin k → A))
    (hφ : φ ∈ chartSections R A x) (v : A ⊗[R] M) :
    ofChartSectionQuotientEquiv φ hφ (Submodule.Quotient.mk v) = φ.liftBaseChange A v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ v

theorem ofChartSectionQuotientEquiv_comp_chartMap {x : Fin k → M} (φ : M →ₗ[R] (Fin k → A))
    (hφ : φ ∈ chartSections R A x) :
    (ofChartSectionQuotientEquiv φ hφ).toLinearMap ∘ₗ
      chartMap (baseChangeTuple A x) (ofChartSection φ hφ).toSubmodule = LinearMap.id := by
  have hφ' : ∀ b, φ (x b) = Pi.single b 1 := hφ
  refine LinearMap.pi_ext' fun b ↦ LinearMap.ext_ring ?_
  simp [hφ']

theorem ofChartSection_mem_chart {x : Fin k → M} (φ : M →ₗ[R] (Fin k → A))
    (hφ : φ ∈ chartSections R A x) :
    ofChartSection φ hφ ∈ chart A (baseChangeTuple A x) := by
  have h := ofChartSectionQuotientEquiv_comp_chartMap φ hφ
  have hinj : Function.Injective
      (chartMap (baseChangeTuple A x) (ofChartSection φ hφ).toSubmodule) := by
    intro c d hcd
    have hc : ofChartSectionQuotientEquiv φ hφ
        (chartMap (baseChangeTuple A x) (ofChartSection φ hφ).toSubmodule c) = c :=
      LinearMap.congr_fun h c
    have hd : ofChartSectionQuotientEquiv φ hφ
        (chartMap (baseChangeTuple A x) (ofChartSection φ hφ).toSubmodule d) = d :=
      LinearMap.congr_fun h d
    rw [← hc, ← hd, hcd]
  refine ⟨hinj, fun q ↦ ⟨ofChartSectionQuotientEquiv φ hφ q, ?_⟩⟩
  apply (ofChartSectionQuotientEquiv φ hφ).injective
  exact LinearMap.congr_fun h (ofChartSectionQuotientEquiv φ hφ q)

/-- The chart isomorphism `A^k ≃ (A ⊗[R] M) ⧸ N` at a point `N` of the chart. -/
def chartEquivOfMem {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) :
    (Fin k → A) ≃ₗ[A] (A ⊗[R] M) ⧸ N.toSubmodule :=
  LinearEquiv.ofBijective _ hN

@[simp]
theorem chartEquivOfMem_apply {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) (c : Fin k → A) :
    chartEquivOfMem hN c = chartMap (baseChangeTuple A x) N.toSubmodule c :=
  rfl

/-- The linear section `M → A^k` attached to a point of the chart: the inverse of the chart
isomorphism composed with `m ↦ [1 ⊗ m]`. -/
def toChartSection {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) : M →ₗ[R] (Fin k → A) :=
  (LinearMap.liftBaseChangeEquiv A).symm
    ((chartEquivOfMem hN).symm.toLinearMap ∘ₗ N.toSubmodule.mkQ)

theorem liftBaseChange_toChartSection {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) :
    (toChartSection hN).liftBaseChange A =
      (chartEquivOfMem hN).symm.toLinearMap ∘ₗ N.toSubmodule.mkQ := by
  simp [toChartSection, LinearMap.liftBaseChange]

theorem toChartSection_mem {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) : toChartSection hN ∈ chartSections R A x := by
  intro b
  rw [toChartSection, LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
  simp

theorem ofChartSection_toChartSection {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) :
    ofChartSection (toChartSection hN) (toChartSection_mem hN) = N := by
  ext : 1
  rw [ofChartSection_toSubmodule, liftBaseChange_toChartSection, LinearEquiv.ker_comp,
    Submodule.ker_mkQ]

theorem toChartSection_ofChartSection {x : Fin k → M} (φ : M →ₗ[R] (Fin k → A))
    (hφ : φ ∈ chartSections R A x) :
    toChartSection (ofChartSection_mem_chart φ hφ) = φ := by
  ext m : 1
  rw [toChartSection, LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
  apply (ofChartSectionQuotientEquiv φ hφ).injective
  have h : ofChartSectionQuotientEquiv φ hφ
      (chartMap (baseChangeTuple A x) (ofChartSection φ hφ).toSubmodule (φ m)) = φ m :=
    LinearMap.congr_fun (ofChartSectionQuotientEquiv_comp_chartMap φ hφ) (φ m)
  rw [chartEquivOfMem_apply, h, Submodule.mkQ_apply, ofChartSectionQuotientEquiv_mk,
    LinearMap.liftBaseChange_one_tmul]

variable (A) in
/-- The chart at `1 ⊗ x` over `A` is in bijection with the linear sections `M → A^k`. -/
def chartEquiv (x : Fin k → M) :
    chart A (baseChangeTuple (R := R) A x) ≃ chartSections R A x where
  toFun N := ⟨toChartSection N.2, toChartSection_mem N.2⟩
  invFun φ := ⟨ofChartSection φ.1 φ.2, ofChartSection_mem_chart φ.1 φ.2⟩
  left_inv N := Subtype.ext (ofChartSection_toChartSection N.2)
  right_inv φ := Subtype.ext (toChartSection_ofChartSection φ.1 φ.2)

end Sections

section Naturality

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

theorem compLeft_mem_chartSections (f : A →ₐ[R] B) {x : Fin k → M} {φ : M →ₗ[R] (Fin k → A)}
    (hφ : φ ∈ chartSections R A x) :
    f.toLinearMap.compLeft (Fin k) ∘ₗ φ ∈ chartSections R B x := by
  have hφ' : ∀ b, φ (x b) = Pi.single b 1 := hφ
  intro b
  ext a
  by_cases hab : a = b
  · subst hab
    simp [hφ']
  · simp [hφ', hab]

/-- Base change of the point cut out by a linear section `φ` is the point cut out by the
composite of `φ` with the algebra map. -/
theorem map_ofChartSection [BaseChangeMkQFormula.{u, v, w} R M] (f : A →ₐ[R] B) {x : Fin k → M}
    (φ : M →ₗ[R] (Fin k → A))
    (hφ : φ ∈ chartSections R A x) :
    map f (ofChartSection φ hφ) =
      ofChartSection (f.toLinearMap.compLeft (Fin k) ∘ₗ φ) (compLeft_mem_chartSections f hφ) := by
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  have hf : ∀ a, algebraMap A B a = f a := fun _ ↦ rfl
  set e := ofChartSectionQuotientEquiv φ hφ
  let g : ((A ⊗[R] M) ⧸ (ofChartSection φ hφ).toSubmodule) →ₗ[A] (Fin k → B) :=
    (Algebra.linearMap A B).compLeft (Fin k) ∘ₗ e.toLinearMap
  let G : B ⊗[A] ((A ⊗[R] M) ⧸ (ofChartSection φ hφ).toSubmodule) →ₗ[B] (Fin k → B) :=
    g.liftBaseChange B
  let bB : Basis (Fin k) B (B ⊗[A] ((A ⊗[R] M) ⧸ (ofChartSection φ hφ).toSubmodule)) :=
    Algebra.TensorProduct.basis B ((Pi.basisFun A (Fin k)).map e.symm)
  have hG : G = bB.equivFun.toLinearMap := by
    refine bB.ext fun b ↦ ?_
    ext a
    by_cases hab : a = b
    · subst hab
      simp [G, g, bB, Algebra.TensorProduct.basis_apply]
    · simp [G, g, bB, Algebra.TensorProduct.basis_apply, hab]
  have hcomp : G ∘ₗ baseChangeMkQ B (ofChartSection φ hφ).toSubmodule =
      (f.toLinearMap.compLeft (Fin k) ∘ₗ φ).liftBaseChange B := by
    ext m a
    simp [G, g, e, hf]
  have h1 : (map f (ofChartSection φ hφ)).toSubmodule =
      LinearMap.ker (baseChangeMkQ B (ofChartSection φ hφ).toSubmodule) :=
    map_toSubmodule f _
  ext : 1
  rw [h1, ofChartSection_toSubmodule (f.toLinearMap.compLeft (Fin k) ∘ₗ φ), ← hcomp, hG,
    LinearEquiv.ker_comp]

theorem toChartSection_congr {x : Fin k → M} {N N' : G(k, A ⊗[R] M; A)} (h : N = N')
    (hN : N ∈ chart A (baseChangeTuple A x)) (hN' : N' ∈ chart A (baseChangeTuple A x)) :
    toChartSection hN = toChartSection hN' := by
  subst h
  rfl

/-- Naturality of the linear section in the algebra. -/
theorem toChartSection_map [BaseChangeMkQFormula.{u, v, w} R M] (f : A →ₐ[R] B) {x : Fin k → M}
    {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) :
    toChartSection (map_mem_chart f x hN) =
      f.toLinearMap.compLeft (Fin k) ∘ₗ toChartSection hN := by
  have h := map_ofChartSection f (toChartSection hN) (toChartSection_mem hN)
  rw [ofChartSection_toChartSection hN] at h
  rw [toChartSection_congr h (map_mem_chart f x hN) (ofChartSection_mem_chart _ _),
    toChartSection_ofChartSection]

/-- Naturality of `chartEquiv`: base change corresponds to composition with the algebra map. -/
theorem chartEquiv_map [BaseChangeMkQFormula.{u, v, w} R M] (f : A →ₐ[R] B) (x : Fin k → M)
    (N : chart A (baseChangeTuple (R := R) A x)) :
    ((chartEquiv B x ⟨map f N.1, map_mem_chart f x N.2⟩ : chartSections R B x) :
        M →ₗ[R] (Fin k → B)) =
      f.toLinearMap.compLeft (Fin k) ∘ₗ (chartEquiv A x N : M →ₗ[R] (Fin k → A)) :=
  toChartSection_map f N.2

end Naturality

end Module.Grassmannian

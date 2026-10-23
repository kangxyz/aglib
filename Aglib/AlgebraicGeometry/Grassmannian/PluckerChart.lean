/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.Plucker
public import Aglib.RingTheory.Grassmannian.ChartLocus

/-!
# The Plücker transformation on coordinate charts

Let `S` be a `k`-subset of `Fin n`, with increasing enumeration `pluckerChartIndex S`, and let
`pluckerTargetIndex k S` be the rank-one coordinate tuple of the Plücker coordinate `p_S` of
`R^{n.choose k}`. For a point `N` of `G(k, A ⊗[R] R^n; A)` with quotient `Q`:

* `pluckerQuotientEquiv N`: the quotient of the Plücker point is `⋀[A]^k Q`, and the class of
  `1 ⊗ e_{p_S}` is `[e_{s₁}] ∧ ⋯ ∧ [e_{s_k}]` (`pluckerQuotientEquiv_mk_single`);
* `pluckerFinPoint N`: the Plücker point with values in `G(1, A ⊗[R] R^{n.choose k}; A)`, natural
  in `A` (`pluckerFinPoint_map`);
* `pluckerFin_mem_chart_of_mem_chart`: if `N` lies in the chart at `S`, its Plücker point lies in
  the rank-one chart at `p_S`, and the chart section of the Plücker point is the top coordinate
  of the Plücker map in the chart basis of `Q` (`toChartSection_pluckerFin_apply`);
* `mem_chart_of_pluckerFin_mem_chart`: conversely, if the Plücker point lies in the rank-one chart
  at `p_S`, then `N` lies in the chart at `S`. On a chart at any `I'`, with basis `f` of `Q`,
  `[e_{s₁}] ∧ ⋯ ∧ [e_{s_k}] = det_f(q) · (f₁ ∧ ⋯ ∧ f_k)`, so the determinant is a unit and the
  vectors `[e_{s_c}]` form a basis (`Module.Basis.is_basis_iff_det`); the charts cover the
  Grassmannian locally and chart membership is Zariski local.

General facts on charts used here: `Module.Grassmannian.mem_chart_coordinateTuple_one_iff`
(rank-one charts through any identification of the quotient) and `Module.Grassmannian.chartBasis`
(the basis of the quotient given by a chart). The statements use `pluckerFinPoint N`, the value of
`pluckerFinNatTrans` (`pluckerFinNatTrans_app_eq`), for an arbitrary `R`-algebra `A`.

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, p. 9
("Projective embedding": `σ_I|_{U^J} = P^J_I`, so the Plücker coordinate `p_S` is invertible
exactly on the chart at `S`).
-/

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct
open scoped Module.Grassmannian

universe u v w

namespace Module.Grassmannian

section Chart

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
  {A : Type w} [CommRing A] [Algebra R A]

/-- **Rank-one charts through an identification of the quotient**: a point `P` of
`G(1, A ⊗[R] R^N; A)` lies in the chart at the coordinate `t` exactly when
`c ↦ c • E [1 ⊗ e_t]` is bijective, for any linear isomorphism `E` from the quotient of `P`. -/
theorem mem_chart_coordinateTuple_one_iff {N : ℕ} (P : G(1, A ⊗[R] (Fin N → R); A)) (t : Fin N)
    {L : Type*} [AddCommGroup L] [Module A L] (E : ((A ⊗[R] (Fin N → R)) ⧸ P.toSubmodule) ≃ₗ[A] L) :
    P ∈ chart A (baseChangeTuple A (coordinateTuple R (fun _ : Fin 1 => t))) ↔
      Function.Bijective (fun c : A =>
        c • E (Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] (Pi.single t 1 : Fin N → R)))) := by
  have h : (⇑E ∘ ⇑(chartMap (baseChangeTuple A (coordinateTuple R (fun _ : Fin 1 => t)))
      P.toSubmodule)) =
      (fun c : A => c • E (Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] (Pi.single t 1 : Fin N → R)))) ∘
        (Equiv.funUnique (Fin 1) A) := by
    funext c
    simp [chartMap_eq_linearCombination, Fintype.linearCombination_apply]
  rw [mem_chart_iff, ← Function.Bijective.of_comp_iff' E.bijective, h,
    Function.Bijective.of_comp_iff _ (Equiv.funUnique (Fin 1) A).bijective]

/-- The chart map sends the chart section at `m` to the class of `1 ⊗ m`. -/
theorem chartMap_toChartSection {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) (m : M) :
    chartMap (baseChangeTuple A x) N.toSubmodule (toChartSection hN m) =
      Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] m) := by
  have h := LinearMap.congr_fun (liftBaseChange_toChartSection hN) ((1 : A) ⊗ₜ[R] m)
  rw [LinearMap.liftBaseChange_one_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.mkQ_apply] at h
  rw [h, ← chartEquivOfMem_apply hN, LinearEquiv.apply_symm_apply]

/-- The basis of the quotient of a point of the chart at `1 ⊗ x`: the classes of the `1 ⊗ x b`. -/
def chartBasis {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) :
    Module.Basis (Fin k) A ((A ⊗[R] M) ⧸ N.toSubmodule) :=
  (Pi.basisFun A (Fin k)).map (chartEquivOfMem hN)

theorem chartBasis_apply {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) (b : Fin k) :
    chartBasis hN b = Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] x b) := by
  rw [chartBasis, Module.Basis.map_apply, Pi.basisFun_apply, chartEquivOfMem_apply,
    chartMap_single]

/-- The coordinates in the chart basis are the values of the chart section. -/
theorem chartBasis_repr_mk {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) (m : M) (b : Fin k) :
    (chartBasis hN).repr (Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] m)) b = toChartSection hN m b := by
  rw [chartBasis, Module.Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr,
    toChartSection, LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Submodule.mkQ_apply]

end Chart

end Module.Grassmannian

namespace AlgebraicGeometry.Grassmannian

variable {R : CommRingCat.{u}} {k n : ℕ}

/-- The increasing enumeration of a `k`-subset `S` of `Fin n`: the coordinate tuple of the chart
of `Gr(R^n, k)` at `S`. -/
abbrev pluckerChartIndex (S : Set.powersetCard (Fin n) k) : Fin k → Fin n :=
  Set.powersetCard.ofFinEmbEquiv.symm S

variable (k) in
/-- The rank-one coordinate tuple of the Plücker coordinate `p_S`. -/
abbrev pluckerTargetIndex (S : Set.powersetCard (Fin n) k) : Fin 1 → Fin (n.choose k) :=
  fun _ => pluckerIndexEquiv k n S

variable (R) in
/-- The wedge basis vector `e_S` has Plücker coordinates `e_{p_S}`. -/
theorem exteriorPowerEquivFin_basis (S : Set.powersetCard (Fin n) k) :
    exteriorPowerEquivFin R k n ((Pi.basisFun R (Fin n)).exteriorPower k S) =
      Pi.single (pluckerIndexEquiv k n S) 1 := by
  ext t
  rw [show exteriorPowerEquivFin R k n ((Pi.basisFun R (Fin n)).exteriorPower k S) t =
      ((Pi.basisFun R (Fin n)).exteriorPower k).equivFun
        ((Pi.basisFun R (Fin n)).exteriorPower k S) ((pluckerIndexEquiv k n).symm t) from rfl,
    Module.Basis.equivFun_self, Pi.single_apply]
  by_cases h : t = pluckerIndexEquiv k n S
  · rw [ite_eq_left (by rw [h, Equiv.symm_apply_apply]), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (by rw [h', Equiv.apply_symm_apply])), ite_eq_right h]

variable (R) in
theorem exteriorPowerEquivFin_symm_single (S : Set.powersetCard (Fin n) k) :
    (exteriorPowerEquivFin R k n).symm (Pi.single (pluckerIndexEquiv k n S) 1) =
      exteriorPower.ιMulti R k (fun c => Pi.single (pluckerChartIndex S c) (1 : R)) := by
  rw [LinearEquiv.symm_apply_eq, ← exteriorPowerEquivFin_basis R S, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family]
  congr 2
  funext c
  rw [Function.comp_apply, Pi.basisFun_apply]

section Point

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The Plücker point with values in the rank-one quotients of `R^{n.choose k}`: the transport of
`Module.Grassmannian.plucker N` along `exteriorPowerEquivFin`. -/
def pluckerFinPoint (N : G(k, A ⊗[R] (Fin n → R); A)) :
    G(1, A ⊗[R] (Fin (n.choose k) → R); A) :=
  Module.Grassmannian.ofLinearEquiv ((exteriorPowerEquivFin R k n).baseChange R A _ _)
    (Module.Grassmannian.plucker N)

/-- `pluckerFinNatTrans` is `pluckerFinPoint` on points. -/
theorem pluckerFinNatTrans_app_eq {A : CommAlgCat.{u} R}
    (N : (Module.Grassmannian.functor.{u, u, u} (R := R) (M := Fin n → R) k).obj A) :
    (pluckerFinNatTrans R k n).app A N = pluckerFinPoint (A := A) N :=
  rfl

/-- Naturality of `pluckerFinPoint`. -/
theorem pluckerFinPoint_map {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B)
    (N : G(k, A ⊗[R] (Fin n → R); A)) :
    pluckerFinPoint (Module.Grassmannian.map f N) =
      Module.Grassmannian.map f (pluckerFinPoint N) := by
  rw [pluckerFinPoint, pluckerFinPoint, Module.Grassmannian.map_ofLinearEquiv_baseChange,
    Module.Grassmannian.map_plucker]

theorem pluckerFinPoint_toSubmodule (N : G(k, A ⊗[R] (Fin n → R); A)) :
    (LinearMap.ker (Module.Grassmannian.pluckerMap k N.toSubmodule)).map
        ((exteriorPowerEquivFin R k n).baseChange R A _ _ :
          A ⊗[R] ⋀[R]^k (Fin n → R) →ₗ[A] A ⊗[R] (Fin (n.choose k) → R)) =
      (pluckerFinPoint N).toSubmodule :=
  rfl

/-- **The quotient of the Plücker point is the top exterior power of the quotient.** -/
def pluckerQuotientEquiv (N : G(k, A ⊗[R] (Fin n → R); A)) :
    ((A ⊗[R] (Fin (n.choose k) → R)) ⧸ (pluckerFinPoint N).toSubmodule) ≃ₗ[A]
      ⋀[A]^k ((A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule) :=
  (Submodule.Quotient.equiv (LinearMap.ker (Module.Grassmannian.pluckerMap k N.toSubmodule))
      (pluckerFinPoint N).toSubmodule
      ((exteriorPowerEquivFin R k n).baseChange R A _ _) (pluckerFinPoint_toSubmodule N)).symm ≪≫ₗ
    (Module.Grassmannian.pluckerMap k N.toSubmodule).quotKerEquivOfSurjective
      (Module.Grassmannian.pluckerMap_surjective k N.toSubmodule)

theorem pluckerQuotientEquiv_mk (N : G(k, A ⊗[R] (Fin n → R); A))
    (y : A ⊗[R] ⋀[R]^k (Fin n → R)) :
    pluckerQuotientEquiv N
        (Submodule.Quotient.mk ((exteriorPowerEquivFin R k n).baseChange R A _ _ y)) =
      Module.Grassmannian.pluckerMap k N.toSubmodule y := by
  have h : (Submodule.Quotient.equiv
      (LinearMap.ker (Module.Grassmannian.pluckerMap k N.toSubmodule))
      (pluckerFinPoint N).toSubmodule
      ((exteriorPowerEquivFin R k n).baseChange R A _ _) (pluckerFinPoint_toSubmodule N)).symm
      (Submodule.Quotient.mk ((exteriorPowerEquivFin R k n).baseChange R A _ _ y)) =
      Submodule.Quotient.mk y := by
    rw [LinearEquiv.symm_apply_eq, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
      LinearEquiv.coe_coe]
  rw [pluckerQuotientEquiv, LinearEquiv.trans_apply, h]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ y

theorem pluckerQuotientEquiv_mk_tmul (N : G(k, A ⊗[R] (Fin n → R); A))
    (m : Fin (n.choose k) → R) :
    pluckerQuotientEquiv N (Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] m)) =
      Module.Grassmannian.pluckerMap k N.toSubmodule
        ((1 : A) ⊗ₜ[R] (exteriorPowerEquivFin R k n).symm m) := by
  rw [← pluckerQuotientEquiv_mk, LinearEquiv.baseChange_tmul, LinearEquiv.apply_symm_apply]

/-- The class of `1 ⊗ e_{p_S}` in the quotient of the Plücker point is
`[1 ⊗ e_{s₁}] ∧ ⋯ ∧ [1 ⊗ e_{s_k}]`. -/
theorem pluckerQuotientEquiv_mk_single (N : G(k, A ⊗[R] (Fin n → R); A))
    (S : Set.powersetCard (Fin n) k) :
    pluckerQuotientEquiv N
        (Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] Pi.single (pluckerIndexEquiv k n S) (1 : R))) =
      exteriorPower.ιMulti A k (fun c => N.toSubmodule.mkQ
        ((1 : A) ⊗ₜ[R] Pi.single (pluckerChartIndex S c) (1 : R))) := by
  rw [pluckerQuotientEquiv_mk_tmul, exteriorPowerEquivFin_symm_single,
    Module.Grassmannian.pluckerMap_tmul, one_smul]

/-- On the chart at `S`, the vectors `[1 ⊗ e_{s_c}]` are the chart basis. -/
theorem chartBasis_coordinateTuple {N : G(k, A ⊗[R] (Fin n → R); A)}
    (S : Set.powersetCard (Fin n) k)
    (hN : N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S)))) :
    (fun c => N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] Pi.single (pluckerChartIndex S c) (1 : R))) =
      ⇑(Module.Grassmannian.chartBasis hN) := by
  funext c
  rw [Module.Grassmannian.chartBasis_apply]
  rfl

/-- **On the chart at `S`, the Plücker point lies in the rank-one chart at `p_S`.** -/
theorem pluckerFin_mem_chart_of_mem_chart {N : G(k, A ⊗[R] (Fin n → R); A)}
    (S : Set.powersetCard (Fin n) k)
    (hN : N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S)))) :
    pluckerFinPoint N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S))) := by
  rw [Module.Grassmannian.mem_chart_coordinateTuple_one_iff _ (pluckerIndexEquiv k n S)
    (pluckerQuotientEquiv N), pluckerQuotientEquiv_mk_single, chartBasis_coordinateTuple S hN]
  have h : (fun c : A => c • exteriorPower.ιMulti A k (Module.Grassmannian.chartBasis hN)) =
      ⇑(Module.Grassmannian.chartBasis hN).exteriorPowerTopEquiv.symm := by
    funext c
    rw [Module.Basis.exteriorPowerTopEquiv_symm_apply]
  rw [h]
  exact LinearEquiv.bijective _

/-- **The chart section of the Plücker point** on the chart at `S`: its value at `m` is the top
coordinate, in the chart basis, of the Plücker map at `1 ⊗ m`. -/
theorem toChartSection_pluckerFin_apply {N : G(k, A ⊗[R] (Fin n → R); A)}
    (S : Set.powersetCard (Fin n) k)
    (hN : N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S))))
    (hP : pluckerFinPoint N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S))))
    (m : Fin (n.choose k) → R) :
    Module.Grassmannian.toChartSection hP m 0 =
      (Module.Grassmannian.chartBasis hN).exteriorPowerTopEquiv
        (Module.Grassmannian.pluckerMap k N.toSubmodule
          ((1 : A) ⊗ₜ[R] (exteriorPowerEquivFin R k n).symm m)) := by
  have h2 : Module.Grassmannian.chartMap
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S)))
      (pluckerFinPoint N).toSubmodule (Module.Grassmannian.toChartSection hP m) =
        Module.Grassmannian.toChartSection hP m 0 •
          Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] Pi.single (pluckerIndexEquiv k n S) (1 : R)) := by
    simp [Module.Grassmannian.chartMap_eq_linearCombination, Fintype.linearCombination_apply]
  have h3 := congrArg (pluckerQuotientEquiv N)
    (h2.symm.trans (Module.Grassmannian.chartMap_toChartSection hP m))
  rw [map_smul, pluckerQuotientEquiv_mk_single, pluckerQuotientEquiv_mk_tmul,
    chartBasis_coordinateTuple S hN] at h3
  rw [← h3, map_smul, Module.Basis.exteriorPowerTopEquiv_basis, smul_eq_mul, mul_one]

/-- The converse on a chart: if `N` lies in the chart at some `I'` and its Plücker point lies in the
rank-one chart at `p_S`, then `N` lies in the chart at `S`. -/
theorem mem_chart_of_pluckerFin_mem_chart_of_mem_chart {N : G(k, A ⊗[R] (Fin n → R); A)}
    (S : Set.powersetCard (Fin n) k) {I' : Fin k → Fin n}
    (hN' : N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A (Module.Grassmannian.coordinateTuple R I')))
    (hP : pluckerFinPoint N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S)))) :
    N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S))) := by
  let q : Fin k → (A ⊗[R] (Fin n → R)) ⧸ N.toSubmodule := fun c =>
    N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] Pi.single (pluckerChartIndex S c) (1 : R))
  have hb : Function.Bijective (fun c : A => c • exteriorPower.ιMulti A k q) := by
    have h := (Module.Grassmannian.mem_chart_coordinateTuple_one_iff _ (pluckerIndexEquiv k n S)
      (pluckerQuotientEquiv N)).mp hP
    rwa [pluckerQuotientEquiv_mk_single] at h
  let f := Module.Grassmannian.chartBasis hN'
  obtain ⟨c, hc⟩ := hb.2 (exteriorPower.ιMulti A k f)
  have hc' : c * f.det q = 1 := by
    have h := congrArg f.exteriorPowerTopEquiv hc
    simp only [exteriorPower.ιMulti_eq_det_smul f q, map_smul,
      Module.Basis.exteriorPowerTopEquiv_basis, smul_eq_mul, mul_one] at h
    exact h
  obtain ⟨hli, hsp⟩ := (f.is_basis_iff_det).mpr (IsUnit.of_mul_eq_one_right c hc')
  have key : Module.Grassmannian.chartMap
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S))) N.toSubmodule =
      (Module.Basis.mk hli hsp.ge).equivFun.symm.toLinearMap := by
    ext b
    simp [Module.Basis.equivFun_symm_apply, Pi.single_apply, q]
  rw [Module.Grassmannian.mem_chart_iff, key]
  exact LinearEquiv.bijective _

/-- **The chart at `S` is the preimage of the rank-one chart at `p_S`**: if the Plücker point of
`N` lies in the rank-one chart at `p_S`, then `N` lies in the chart at `S`. The charts cover the
Grassmannian locally (`exists_mem_chart_map`), the Plücker point is natural
(`pluckerFinPoint_map`), and chart membership is Zariski local
(`mem_chart_of_map_localization`). -/
theorem mem_chart_of_pluckerFin_mem_chart (N : G(k, A ⊗[R] (Fin n → R); A))
    (S : Set.powersetCard (Fin n) k)
    (hP : pluckerFinPoint N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S)))) :
    N ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S))) := by
  choose I r hr hI using fun p : PrimeSpectrum A => Module.Grassmannian.exists_mem_chart_map N p
  refine Module.Grassmannian.mem_chart_of_map_localization r
    (span_range_eq_top_of_forall_notMem r hr) _ N fun p => ?_
  have hu : IsUnit (IsScalarTower.toAlgHom R A (Localization.Away (r p)) (r p)) :=
    IsLocalization.Away.algebraMap_isUnit (r p)
  have h1 := hI p (IsScalarTower.toAlgHom R A (Localization.Away (r p))) hu
  have h3 := Module.Grassmannian.map_mem_chart
    (IsScalarTower.toAlgHom R A (Localization.Away (r p))) _ hP
  rw [← pluckerFinPoint_map] at h3
  exact mem_chart_of_pluckerFin_mem_chart_of_mem_chart S h1 h3

end Point

end AlgebraicGeometry.Grassmannian

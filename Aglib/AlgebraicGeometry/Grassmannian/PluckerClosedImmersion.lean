/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.AffinePullback
public import Aglib.AlgebraicGeometry.Grassmannian.PluckerChart
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The Plücker morphism is a closed immersion

For a `k`-subset `S` of `Fin n`, let `U_S` be the coordinate chart of `Gr(R^n, k)` at the increasing
enumeration of `S` and `U'_S` the chart of `Gr(R^N, 1)`, `N = n.choose k`, at the Plücker coordinate
`p_S`.

* `pluckerChartAlgHom S` is the `R`-algebra map of chart rings classifying the Plücker point of the
  universal point of `U_S`, and `pluckerChartHom S : U_S ⟶ U'_S` its spectrum. The square
  `U_S → Gr → Gr(R^N, 1)`, `U_S → U'_S → Gr(R^N, 1)` commutes (`chartι_comp_plucker`) and is a
  pullback (`isPullback_pluckerChart`): on affine points this says that a point lies in the chart at
  `S` exactly when its Plücker point lies in the chart at `p_S`
  (`mem_chart_of_pluckerFin_mem_chart`), and the affine criterion is
  `AlgSpecPoints.isPullback_of_lift`.
* `pluckerChartAlgHom_surjective`: the chart ring map is surjective. Its values on the coordinates
  are the Plücker minors `det_f [Φ_{T₁} ⋯ Φ_{T_k}]`, and the chart coordinate `Φ_{aj}` is the
  minor of `e_{s₁}, …, e_j (at a), …, e_{s_k}` (`Module.Basis.det_update_self`); the Plücker
  functional is linear in the wedge, so no ordering of subsets is needed.
* `isClosedImmersion_plucker`: closed immersions are local on the target, and the charts `U'_S`
  cover `Gr(R^N, 1)`; hence `isClosedImmersion_pluckerProjective` into `P(⋀^k R^n)`.
* Corollaries: `Gr(R^n, k)` is proper, hence separated, over `Spec R` (`isProper_schemeOver_hom`,
  `isSeparated_schemeOver_hom`, also for `toBase`), since projective space with finitely many
  coordinates is proper over `Spec R` (`ProjectiveSpace.isProper_toSpec`).

Sources: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, p. 9
("Projective embedding": the sections `σ_I` with `σ_I|_{U^J} = P^J_I` give an embedding into
`P^m_Z`; there it is a closed embedding by the properness of the Grassmannian, pp. 8–9). Here the
closed immersion is proved through the charts, and properness is deduced from it. Stacks,
Section 27.22 (Tag 089R) has no Plücker morphism; the charts are those of Tag 089T (proof of
Lemma 27.22.1). The named premise `BaseChangeMkQFormula` is supplied by the instance in
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`, imported through the projective-space
comparison.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits
open scoped Module.Grassmannian TensorProduct

namespace Module.Basis

variable {ι A M : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [AddCommGroup M] [Module A M]

/-- The determinant of a basis with one vector replaced is the coordinate of the new vector. -/
theorem det_update_self (f : Basis ι A M) (a : ι) (y : M) :
    f.det (Function.update f a y) = f.repr y a := by
  have h : f.det.toMultilinearMap.toLinearMap f a = f.coord a := by
    refine f.ext fun b => ?_
    rw [MultilinearMap.toLinearMap_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    by_cases hb : b = a
    · rw [hb, ite_eq_left rfl, Function.update_eq_self]
      exact f.det_self
    · rw [ite_eq_right hb]
      exact f.det.map_eq_zero_of_eq _ (i := a) (j := b)
        (by rw [Function.update_self, Function.update_of_ne hb]) (Ne.symm hb)
  exact LinearMap.congr_fun h y

end Module.Basis

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {k n : ℕ}

/-- An algebra map into a chart ring is surjective as soon as its range contains the
coordinates. -/
theorem surjective_of_chartCoordinate_mem {D : Type*} [CommRing D] [Algebra R D]
    {x : Fin k → Fin n → R} (θ : D →ₐ[R] ChartRing R x)
    (h : ∀ a j, chartCoordinate x a j ∈ θ.range) : Function.Surjective θ := by
  intro c
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨algebraMap R D r, by rw [AlgHom.commutes]; rfl⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := (AlgHom.mem_range θ).mp (h i.1 i.2)
    exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]; rfl⟩

end Module.Grassmannian

namespace AlgebraicGeometry.Grassmannian

variable {R : CommRingCat.{u}} {k n : ℕ}

variable (k n) in
/-- The coordinate chart of `Gr(R^n, k)` at a `k`-subset `S`. -/
abbrev pluckerChart (S : Set.powersetCard (Fin n) k) : ULift.{u} (Fin k → Fin n) :=
  ⟨pluckerChartIndex S⟩

variable (k n) in
/-- The rank-one chart of `Gr(R^{n.choose k}, 1)` at the Plücker coordinate `p_S`. -/
abbrev pluckerTargetChart (S : Set.powersetCard (Fin n) k) :
    ULift.{u} (Fin 1 → Fin (n.choose k)) :=
  ⟨pluckerTargetIndex k S⟩

variable (R) in
/-- The universal point of a chart lies in that chart. -/
theorem chartPt_id_mem {k n : ℕ} (I : ULift.{u} (Fin k → Fin n)) :
    chartPt I (𝟙 (chartAlg R I)) ∈ Module.Grassmannian.chart (chartAlg R I)
      (Module.Grassmannian.baseChangeTuple (chartAlg R I)
        (Module.Grassmannian.coordinateTuple R I.down)) :=
  ((Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv (𝟙 _)).2

/-- Points classified by chart ring maps determine the maps. -/
theorem chartPt_injective {k n : ℕ} (I : ULift.{u} (Fin k → Fin n)) {B : CommAlgCat.{u} R} :
    Function.Injective (chartPt (B := B) I) := fun _ _ h =>
  (Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv.injective (Subtype.ext h)

/-- The point of `Spec ψ ≫ chartι I` is the point classified by `ψ`. -/
theorem representableEquiv_algSpec_comp_chartι {k n : ℕ} (I : ULift.{u} (Fin k → Fin n))
    {B : CommAlgCat.{u} R} (ψ : chartAlg R I ⟶ B) :
    representableEquiv R k n B ((algSpec R).map ψ.op ≫ chartι I) = chartPt I ψ := by
  have h := map_homPoint_of_factor ((algSpec R).map ψ.op ≫ chartι I) (f := 𝟙 B) (I := I)
    (ψ := ψ) (by rw [op_id, CategoryTheory.Functor.map_id, Category.id_comp])
  rw [CategoryTheory.Functor.map_id] at h
  exact h

theorem representableEquiv_chartι {k n : ℕ} (I : ULift.{u} (Fin k → Fin n)) :
    representableEquiv R k n (chartAlg R I) (chartι I) = chartPt I (𝟙 _) := by
  rw [← representableEquiv_algSpec_comp_chartι, op_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

variable (R) in
/-- The universal point of the chart at `S`, as a point of the Grassmannian over the chart
ring. -/
def univChartPoint (S : Set.powersetCard (Fin n) k) :
    G(k, chartAlg R (pluckerChart k n S) ⊗[R] (Fin n → R); chartAlg R (pluckerChart k n S)) :=
  chartPt (pluckerChart k n S) (𝟙 _)

theorem univChartPoint_mem (S : Set.powersetCard (Fin n) k) :
    univChartPoint R S ∈ Module.Grassmannian.chart (chartAlg R (pluckerChart k n S))
      (Module.Grassmannian.baseChangeTuple (chartAlg R (pluckerChart k n S))
        (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S))) :=
  chartPt_id_mem R (pluckerChart k n S)

/-- The Plücker point of the universal point of the chart at `S` lies in the chart at `p_S`. -/
theorem pluckerFin_univChartPoint_mem (S : Set.powersetCard (Fin n) k) :
    pluckerFinPoint (univChartPoint R S) ∈ Module.Grassmannian.chart _
      (Module.Grassmannian.baseChangeTuple _
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S))) :=
  pluckerFin_mem_chart_of_mem_chart S (univChartPoint_mem S)

/-- **The Plücker morphism on the chart at `S`, on coordinate rings**: the algebra map
classifying the Plücker point of the universal point of the chart at `S`. -/
def pluckerChartAlgHom (S : Set.powersetCard (Fin n) k) :
    chartAlg R (pluckerTargetChart k n S) ⟶ chartAlg R (pluckerChart k n S) :=
  (Module.Grassmannian.chartFunctorCorepresentableBy R
    (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S))).homEquiv.symm
      ⟨pluckerFinPoint (univChartPoint R S), pluckerFin_univChartPoint_mem S⟩

theorem chartPt_pluckerChartAlgHom (S : Set.powersetCard (Fin n) k) :
    chartPt (pluckerTargetChart k n S) (pluckerChartAlgHom (R := R) S) =
      (pluckerFinNatTrans R k n).app _ (chartPt (pluckerChart k n S) (𝟙 _)) :=
  (congrArg Subtype.val
    ((Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv.apply_symm_apply _)).trans
    (pluckerFinNatTrans_app_eq _).symm

/-- **The Plücker morphism on the chart at `S`**: `U_S ⟶ U'_S`. -/
def pluckerChartHom (S : Set.powersetCard (Fin n) k) :
    chartScheme R (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S)) ⟶
      chartScheme R (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S)) :=
  (algSpec R).map (pluckerChartAlgHom S).op

variable (R) in
/-- The chart at `S` maps into the chart at `p_S` under the Plücker morphism. -/
theorem chartι_comp_plucker (S : Set.powersetCard (Fin n) k) :
    chartι (pluckerChart k n S) ≫ plucker R k n =
      pluckerChartHom S ≫ chartι (pluckerTargetChart k n S) := by
  apply (representableEquiv R 1 (n.choose k) (chartAlg R (pluckerChart k n S))).injective
  rw [representableEquiv_comp_plucker, representableEquiv_chartι, pluckerChartHom,
    representableEquiv_algSpec_comp_chartι, chartPt_pluckerChartAlgHom]

instance (I : ULift.{u} (Fin k → Fin n)) : Mono (chartι (R := R) I) :=
  have : Mono (chartι (R := R) I).left := inferInstanceAs (Mono ((glueData R k n).ι I))
  Over.mono_of_mono_left _

variable (R) in
/-- **The chart at `S` is the preimage of the chart at `p_S`**: the square of charts is a pullback
of schemes. -/
theorem isPullback_pluckerChart (S : Set.powersetCard (Fin n) k) :
    IsPullback (chartι (pluckerChart k n S)).left (pluckerChartHom (R := R) S).left
      (plucker R k n).left (chartι (pluckerTargetChart k n S)).left := by
  refine AlgSpecPoints.isPullback_of_lift _ _ _ _ (chartι_comp_plucker R S)
    fun A a b hab => ?_
  obtain ⟨ψb, rfl⟩ : ∃ ψb : chartAlg R (pluckerTargetChart k n S) ⟶ A,
      (algSpec R).map ψb.op = b :=
    ⟨((algSpec R).preimage b).unop, by rw [Quiver.Hom.op_unop, CategoryTheory.Functor.map_preimage]⟩
  have hP : (pluckerFinNatTrans R k n).app A (representableEquiv R k n A a) =
      chartPt (pluckerTargetChart k n S) ψb := by
    rw [← representableEquiv_comp_plucker, hab, representableEquiv_algSpec_comp_chartι]
  have hb : chartPt (pluckerTargetChart k n S) ψb ∈ Module.Grassmannian.chart A
      (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S))) :=
    ((Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv ψb).2
  rw [← hP] at hb
  have hP' : pluckerFinPoint (A := A) (representableEquiv R k n A a) ∈
      Module.Grassmannian.chart A (Module.Grassmannian.baseChangeTuple A
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S))) := hb
  have hmem := mem_chart_of_pluckerFin_mem_chart (representableEquiv R k n A a) S hP'
  let ψa := (Module.Grassmannian.chartFunctorCorepresentableBy R
    (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S))).homEquiv.symm ⟨_, hmem⟩
  have hψa : chartPt (pluckerChart k n S) ψa = representableEquiv R k n A a :=
    congrArg Subtype.val
      ((Module.Grassmannian.chartFunctorCorepresentableBy R _).homEquiv.apply_symm_apply _)
  refine ⟨(algSpec R).map ψa.op, ?_, ?_⟩
  · apply (representableEquiv R k n A).injective
    rw [representableEquiv_algSpec_comp_chartι, hψa]
  · rw [pluckerChartHom, ← Functor.map_comp, ← op_comp]
    congr 2
    apply chartPt_injective (pluckerTargetChart k n S)
    rw [chartPt_comp, chartPt_pluckerChartAlgHom, ← NatTrans.naturality_apply, ← chartPt_comp,
      Category.id_comp, hψa, hP]

/-- **The Plücker morphism on charts is surjective on coordinate rings.** -/
theorem pluckerChartAlgHom_surjective (S : Set.powersetCard (Fin n) k) :
    Function.Surjective (pluckerChartAlgHom (R := R) S).hom := by
  have hN := univChartPoint_mem (R := R) S
  have hP := pluckerFin_univChartPoint_mem (R := R) S
  let f := Module.Grassmannian.chartBasis hN
  have hθ : ∀ t : Fin (n.choose k), (pluckerChartAlgHom (R := R) S).hom
      (Module.Grassmannian.chartCoordinate
        (Module.Grassmannian.coordinateTuple R (pluckerTargetIndex k S)) 0 t) =
      Module.Grassmannian.toChartSection hP (Pi.single t 1) 0 := fun t =>
    Module.Grassmannian.chartSectionToAlgHom_coordinate (Module.Grassmannian.toChartSection hP)
      (Module.Grassmannian.toChartSection_mem hP) 0 t
  have hrange : ∀ m : Fin (n.choose k) → R,
      Module.Grassmannian.toChartSection hP m 0 ∈ (pluckerChartAlgHom (R := R) S).hom.range := by
    intro m
    rw [Module.Grassmannian.linearMap_apply_eq_sum_single (Module.Grassmannian.toChartSection hP)
      m, Finset.sum_apply]
    refine Subalgebra.sum_mem _ fun t _ => ?_
    rw [Pi.smul_apply, ← hθ t]
    exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) (m t)
  have hsec : Module.Grassmannian.toChartSection hN =
      Module.Grassmannian.algHomToChartSection (chartAlg R (pluckerChart k n S))
        (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S))
        (AlgHom.id R (chartAlg R (pluckerChart k n S))) :=
    Module.Grassmannian.toChartSection_ofChartSection _
      (Module.Grassmannian.algHomToChartSection_mem _ _)
  refine Module.Grassmannian.surjective_of_chartCoordinate_mem _ fun a j => ?_
  let v : Fin k → Fin n → R :=
    Function.update (fun c => Pi.single (pluckerChartIndex S c) 1) a (Pi.single j 1)
  have hv : (fun c => (univChartPoint R S).toSubmodule.mkQ
      ((1 : chartAlg R (pluckerChart k n S)) ⊗ₜ[R] v c)) =
      Function.update ⇑f a (Submodule.Quotient.mk ((1 : chartAlg R (pluckerChart k n S)) ⊗ₜ[R]
        (Pi.single j 1 : Fin n → R))) := by
    funext c
    by_cases hc : c = a
    · rw [hc, Function.update_self]
      simp only [v, Function.update_self, Submodule.mkQ_apply]
    · rw [Function.update_of_ne hc, ← chartBasis_coordinateTuple S hN]
      simp only [v, Function.update_of_ne hc]
  have key : Module.Grassmannian.chartCoordinate
      (Module.Grassmannian.coordinateTuple R (pluckerChartIndex S)) a j =
      Module.Grassmannian.toChartSection hP
        (exteriorPowerEquivFin R k n (exteriorPower.ιMulti R k v)) 0 := by
    rw [toChartSection_pluckerFin_apply S hN hP, LinearEquiv.symm_apply_apply,
      Module.Grassmannian.pluckerMap_tmul, one_smul,
      Module.Basis.exteriorPowerTopEquiv_ιMulti, hv, Module.Basis.det_update_self,
      Module.Grassmannian.chartBasis_repr_mk, hsec,
      Module.Grassmannian.algHomToChartSection_apply]
    simp [Pi.single_apply]
  rw [key]
  exact hrange _

/-- **The Plücker morphism is a closed immersion**: closed immersions are local on the target, and
over the chart at `p_S` the Plücker morphism is the spectrum of the surjection
`pluckerChartAlgHom S` from the chart at `S`. -/
instance isClosedImmersion_plucker : IsClosedImmersion (plucker R k n).left := by
  refine IsZariskiLocalAtTarget.of_openCover (glueData R 1 (n.choose k)).openCover fun J => ?_
  obtain ⟨S, rfl⟩ : ∃ S : Set.powersetCard (Fin n) k, pluckerTargetChart k n S = J := by
    refine ⟨(pluckerIndexEquiv k n).symm (J.down 0), ULift.ext _ _ (funext fun b => ?_)⟩
    change pluckerIndexEquiv k n ((pluckerIndexEquiv k n).symm (J.down 0)) = J.down b
    rw [Equiv.apply_symm_apply, Subsingleton.elim b 0]
  have hpb := isPullback_pluckerChart R S
  have hθ : IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (pluckerChartAlgHom (R := R) S).hom.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (pluckerChartAlgHom (R := R) S).hom.toRingHom)
      (pluckerChartAlgHom_surjective S)
  have : IsClosedImmersion (pluckerChartHom (R := R) S).left := hθ
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk hpb.isoPullback (Iso.refl _)
      (hpb.isoPullback_hom_snd.trans (Category.comp_id _).symm))).mp this

/-- **The Plücker morphism into `P(⋀^k R^n)` is a closed immersion.** -/
instance isClosedImmersion_pluckerProjective :
    IsClosedImmersion (pluckerProjective R k n).left := by
  rw [pluckerProjective, Over.comp_left]
  have : IsIso (ProjectiveSpace.grassmannianOverIso R
      (Equiv.ulift.trans (pluckerIndexEquiv k n))).hom.left :=
    Iso.isIso_hom ((Over.forget _).mapIso (ProjectiveSpace.grassmannianOverIso R _))
  infer_instance

/-- **The Grassmannian is proper over its base**, as a closed subscheme of projective space. -/
instance isProper_schemeOver_hom : IsProper (schemeOver R k n).hom := by
  rw [← Over.w (pluckerProjective R k n)]
  have : IsProper (ProjectiveSpace.schemeOver R (ULift.{u} (Set.powersetCard (Fin n) k))).hom :=
    ProjectiveSpace.isProper_toSpec R _
  infer_instance

/-- **The Grassmannian is separated over its base.** -/
instance isSeparated_schemeOver_hom : IsSeparated (schemeOver R k n).hom :=
  inferInstance

instance isProper_toBase : IsProper (toBase R k n) :=
  inferInstanceAs (IsProper (schemeOver R k n).hom)

instance isSeparated_toBase : IsSeparated (toBase R k n) :=
  inferInstanceAs (IsSeparated (schemeOver R k n).hom)

end AlgebraicGeometry.Grassmannian

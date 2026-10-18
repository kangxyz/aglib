/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Determinant.Twisting
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Trace
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules.Naturality

/-!
# The original projective trace on the top differential residue class

The actual top relative differential sheaf on polynomial projective space has an original
full-tuple Cech residue cycle. On the tuple enumerated by `e.symm`, its component is the
restricted scalar `r` times the product of the original inverse coordinate ratios, multiplied
by the original wedge of their ratio differentials. The ordered determinant comparison is
exactly the previously constructed twisting isomorphism, followed by the explicit cast from
`-(n + 1)` to minus the number of coordinates.

The full chain image is the native single-weight insertion of the original full-support
cycle. Its enumerated Laurent component is the original all-minus-one monomial, with
coefficient `r`. Native Cech naturality therefore identifies the ordinary cohomology class
under the same coefficient map, and the unchanged projective trace evaluates it to `r`.
The cycle is constructed through the original cycles quotient and chain maps; its literal
section formula proves the normalization. Dimension zero and zero coefficient rings are
included, and the coordinate enumeration supplies the only finite-coordinate choice.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Cech Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicTopology MvPolynomial HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.Invertible
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace AlgebraicGeometry.Scheme.Cohomology
variable (R : Type u) [CommRing R] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
local notation "P" => ProjectiveSpace R ι
local notation "Ω" => Scheme.Modules.Differentials.relativeDifferentialSheaf (toSpec R ι)
local notation "K" => moduleExteriorPower P Ω n

private def supportCyclesIso [Fintype ι] (S : Set ι) (hS : S = Set.univ) :
    (RelativeSimplex.complex R S).cycles n ≅ (RelativeSimplex.complex R S).homology n := by
  subst S
  exact RelativeSimplex.fullSupportCyclesIso n (by
    simpa only [Fintype.card_fin] using Fintype.card_congr e)

private theorem supportCyclesIso_hom [Fintype ι] (S : Set ι) (hS : S = Set.univ) :
    (supportCyclesIso R ι n e S hS).hom = (RelativeSimplex.complex R S).homologyπ n := by
  subst S
  exact RelativeSimplex.fullSupportCyclesIso_hom n _

private def residueSupportCycle [Fintype ι] (r : R) :
    (RelativeSimplex.complex R
      (coordinateNegativeSupport (coordinateResidueWeight (ι := ι)).val)).cycles n :=
  (supportCyclesIso R ι n e _ coordinateResidueWeight_fullSupport).inv
    ((RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin (R := R) n e _
      coordinateResidueWeight_fullSupport).symm r)

private theorem residueSupportCycle_enum [Fintype ι] (r : R) :
    (RelativeSimplex.complex R
      (coordinateNegativeSupport (coordinateResidueWeight (ι := ι)).val)).iCycles n
        (residueSupportCycle R ι n e r)
          ⟨e.symm, fun i _ => ⟨e i, e.symm_apply_apply i⟩⟩ = r := by
  rw [← RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin_homologyπ n e _
    coordinateResidueWeight_fullSupport]
  rw [← supportCyclesIso_hom R ι n e _ coordinateResidueWeight_fullSupport]
  unfold residueSupportCycle
  rw [Iso.inv_hom_id_apply, LinearEquiv.apply_symm_apply]

private def laurentResidueCycle [Fintype ι] (r : R) :
    (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).cycles n :=
  cyclesMap (coordinateLaurentWeightComplexMap R _ coordinateResidueWeight) n
    (residueSupportCycle R ι n e r)

private theorem laurentResidueCycle_enum [Fintype ι] (r : R) :
    (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).iCycles n
      (laurentResidueCycle R ι n e r) e.symm =
        coordinateLaurentTupleWeightSingle R _ e.symm coordinateResidueWeight
          (fun i _ => ⟨e i, e.symm_apply_apply i⟩) r := by
  have h := ConcreteCategory.congr_hom
    (cyclesMap_i (coordinateLaurentWeightComplexMap R _ coordinateResidueWeight) n)
      (residueSupportCycle R ι n e r)
  change (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).iCycles n
      (laurentResidueCycle R ι n e r) =
    (coordinateLaurentWeightComplexMap R _ coordinateResidueWeight).f n
      ((RelativeSimplex.complex R
        (coordinateNegativeSupport (coordinateResidueWeight (ι := ι)).val)).iCycles n
          (residueSupportCycle R ι n e r)) at h
  refine (congrFun h e.symm).trans ?_
  change coordinateLaurentTupleWeightInjection R _ coordinateResidueWeight n _ e.symm = _
  have ha : coordinateWeightAllowed e.symm (coordinateResidueWeight (ι := ι)) :=
    fun i _ => ⟨e i, e.symm_apply_apply i⟩
  simp only [coordinateLaurentTupleWeightInjection, LinearMap.coe_mk, AddHom.coe_mk,
    dite_eq_left ha]
  rw [residueSupportCycle_enum]

private theorem laurentResidueCycle_trace [Fintype ι] (r : R) :
    projectiveTrace R ι n e
      (twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) n
        ((coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).homologyπ n
          (laurentResidueCycle R ι n e r))) = r := by
  rw [projectiveTrace_laurent_homologyπ, laurentResidueCycle_enum,
    coordinateLaurentTupleWeightSingle_val]
  simp


/-- The same ordered determinant isomorphism with its explicit old residue-degree cast. -/
def differentialResidueTwistingIso :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    K ≅ twistingSheaf R ι (-(Fintype.card ι : ℤ)) := by
  letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have hc : Fintype.card ι = n + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  let hd : -(n + 1 : ℤ) = -(Fintype.card ι : ℤ) := by
    rw [hc, Nat.cast_add, Nat.cast_one]
  exact differentialDeterminantTwistingIso R ι n e ≪≫
    eqToIso (congrArg (twistingSheaf R ι) hd)

/-- The original full-tuple Cech coefficient map followed by the old Laurent comparison. -/
def differentialResidueCechLaurentIso :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    moduleCechComplex P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      K (coordinateOpen R ι) ≅
        coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ)) := by
  letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact (cechComplexFunctor (coordinateOpen R ι)).mapIso
    ((moduleSectionsPresheafFunctor P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).mapIso
        (differentialResidueTwistingIso R ι n e)) ≪≫
      twistingCechLaurentIso R ι (-(Fintype.card ι : ℤ))

/-- The actual top differential Cech cycle from native full-support cycles and weight insertion. -/
def differentialResidueCechCycle (r : R) :
    (moduleCechComplex P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      K (coordinateOpen R ι)).cycles n := by
  letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let w := coordinateResidueWeight (ι := ι)
  let S := coordinateNegativeSupport w.val
  let q : (RelativeSimplex.complex R S).cycles n ≅
      (RelativeSimplex.complex R S).homology n :=
    (fun (S : Set ι) (hS : S = Set.univ) => show
        (RelativeSimplex.complex R S).cycles n ≅
          (RelativeSimplex.complex R S).homology n from by
      subst S
      exact RelativeSimplex.fullSupportCyclesIso n (by
        simpa only [Fintype.card_fin] using Fintype.card_congr e))
      S coordinateResidueWeight_fullSupport
  let c := q.inv ((RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin
    (R := R) n e S coordinateResidueWeight_fullSupport).symm r)
  exact cyclesMap (differentialResidueCechLaurentIso R ι n e).inv n
    (cyclesMap (coordinateLaurentWeightComplexMap R _ w) n c)

private theorem residueCycle_chain_image (r : R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (differentialResidueCechLaurentIso R ι n e).hom.f n
      ((moduleCechComplex P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K (coordinateOpen R ι)).iCycles n (differentialResidueCechCycle R ι n e r)) =
    (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).iCycles n
      (laurentResidueCycle R ι n e r) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let q := differentialResidueCechLaurentIso R ι n e
  let c := laurentResidueCycle R ι n e r
  have h := ConcreteCategory.congr_hom (cyclesMap_i q.hom n)
    (cyclesMap q.inv n c)
  change _ = q.hom.f n _ at h
  have hc : cyclesMap q.hom n (cyclesMap q.inv n c) = c :=
    Iso.inv_hom_id_apply (cyclesMapIso q n) c
  change q.hom.f n _ = _
  exact h.symm.trans (congrArg ((coordinateLaurentTupleComplex (ι := ι) R
    (-(Fintype.card ι : ℤ))).iCycles n) hc)


private theorem twistLaurent_smul_generator (s : Finset ι) (i : ι) (hi : i ∈ s)
    (d : ℤ) (f : Γ(P, Proj.basicOpen (homogeneousSubmodule ι R)
      (coordinateProduct R ι s))) :
    (twistingSectionsLaurentAddEquiv R ι s i hi d
      (f • twistingGenerator R ι d i (coordinateProductOpen_le_chart R ι s i hi))).val =
        coordinateSectionsToLaurent R ι s ⟨i, hi⟩ f *
          coordinateVariableMonomial R s i hi d := by
  change coordinateSectionsToLaurent R ι s ⟨i, hi⟩
    (twistingSectionsEquiv R ι d i (coordinateProductOpen_le_chart R ι s i hi)
      (f • twistingGenerator R ι d i (coordinateProductOpen_le_chart R ι s i hi))) * _ = _
  rw [(twistingSectionsEquiv R ι d i
    (coordinateProductOpen_le_chart R ι s i hi)).map_smul,
    twistingSectionsEquiv_generator, smul_eq_mul, mul_one]

private theorem unit_ratio_product {G : Type*} [CommGroup G] (u : Fin (n + 1) → G) :
    (∏ j : Fin n, u 0 * (u j.succ)⁻¹) * u 0 ^ (-(n + 1 : ℤ)) =
      (∏ j : Fin (n + 1), u j)⁻¹ := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_inv_distrib, Fin.prod_univ_succ]
  have hp : u 0 ^ n * u 0 ^ (-(n + 1 : ℤ)) = (u 0)⁻¹ := by
    rw [← zpow_natCast, ← zpow_add]
    have h : (n : ℤ) + -(n + 1 : ℤ) = -1 := by omega
    rw [h, zpow_neg_one]
  calc
    _ = (u 0 ^ n * u 0 ^ (-(n + 1 : ℤ))) *
        (∏ j : Fin n, u j.succ)⁻¹ := by ac_rfl
    _ = _ := by rw [hp, mul_inv_rev]; ac_rfl

private theorem enum_set [Fintype ι] : coordinateTupleSet e.symm = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  exact (mem_coordinateTupleSet e.symm i).mpr ⟨e i, e.symm_apply_apply i⟩

private theorem enum_unit_product :
    (∏ j : Fin (n + 1), coordinateVariableUnit R (coordinateTupleSet e.symm)
      (e.symm j) ((mem_coordinateTupleSet e.symm (e.symm j)).mpr ⟨j, rfl⟩)) =
        coordinateProductUnit R (coordinateTupleSet e.symm) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  apply Units.ext
  change (∏ j : Fin (n + 1), coordinateVariableUnit R (coordinateTupleSet e.symm)
    (e.symm j) ((mem_coordinateTupleSet e.symm (e.symm j)).mpr ⟨j, rfl⟩)).val =
      toCoordinateLaurent R (coordinateTupleSet e.symm)
        (∏ i ∈ coordinateTupleSet e.symm, X i)
  simp only [Units.coe_prod, ← toCoordinateLaurent_X, ← map_prod]
  congr 1
  rw [enum_set]
  exact (Fintype.prod_equiv e (fun i => (X i : MvPolynomial ι R))
    (fun j => (X (e.symm j) : MvPolynomial ι R)) (by intro i; simp)).symm


private theorem enum_residueExponent [Fintype ι] :
    coordinateNegativeProductExponent (coordinateTupleSet e.symm) =
      coordinateWeightExponent e.symm coordinateResidueWeight
        (fun i _ => ⟨e i, e.symm_apply_apply i⟩) := by
  apply Subtype.ext
  ext i
  simp [coordinateNegativeProductExponent, coordinateExponentOfNat,
    coordinateProductExponent, coordinateWeightExponent, enum_set]

private theorem enum_transition_product [Fintype ι] :
    let s := coordinateTupleSet e.symm
    let i := e.symm 0
    let hi := (mem_coordinateTupleSet e.symm i).mpr ⟨0, rfl⟩
    (∏ j : Fin n, coordinateSectionsToLaurent R ι s ⟨i, hi⟩
      (coordinateTransitionOn R ι i (e.symm j.succ)
        (coordinateProductOpen_le_chart R ι s i hi)
        (coordinateProductOpen_le_chart R ι s (e.symm j.succ)
          ((mem_coordinateTupleSet e.symm (e.symm j.succ)).mpr ⟨j.succ, rfl⟩))).val) *
      coordinateVariableMonomial R s i hi (-(Fintype.card ι : ℤ)) =
        AddMonoidAlgebra.single (coordinateWeightExponent e.symm coordinateResidueWeight
          (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) (1 : R) := by
  intro s i hi
  have hc : Fintype.card ι = n + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  let u (a : Fin (n + 1)) := coordinateVariableUnit R s (e.symm a)
    ((mem_coordinateTupleSet e.symm (e.symm a)).mpr ⟨a, rfl⟩)
  have ht (j : Fin n) : coordinateSectionsToLaurent R ι s ⟨i, hi⟩
      (coordinateTransitionOn R ι i (e.symm j.succ)
        (coordinateProductOpen_le_chart R ι s i hi)
        (coordinateProductOpen_le_chart R ι s (e.symm j.succ)
          ((mem_coordinateTupleSet e.symm (e.symm j.succ)).mpr ⟨j.succ, rfl⟩))).val =
        (u 0 * (u j.succ)⁻¹).val :=
    congrArg Units.val (coordinateTransitionOn_laurent R ι s i (e.symm j.succ) hi _)
  simp_rw [ht]
  rw [← Units.coe_prod, ← coordinateVariableUnit_zpow_val]
  change ((∏ j : Fin n, u 0 * (u j.succ)⁻¹) * u 0 ^ (-(Fintype.card ι : ℤ))).val = _
  have hN : -(Fintype.card ι : ℤ) = -(n + 1 : ℤ) := by rw [hc]; simp
  conv_lhs => rw [hN, unit_ratio_product, enum_unit_product]
  change AddMonoidAlgebra.single (coordinateNegativeProductExponent s) (1 : R) = _
  rw [enum_residueExponent]


private theorem degreeIso_generator (d d' : ℤ) (h : d = d') (i : ι)
    {T : (P).Opens} (hi : T ≤ coordinateOpen R ι i) :
    (eqToIso (congrArg (twistingSheaf R ι) h)).hom.val.app (op T)
      (twistingGenerator R ι d i hi) = twistingGenerator R ι d' i hi := by
  cases h
  rfl

private theorem differentialResidueTwistingIso_enum_wedge
    {T : (P).Opens} (hi : T ≤ coordinateOpen R ι (e.symm 0)) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    (differentialResidueTwistingIso R ι n e).hom.val.app (op T)
      ((SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app (op T)
        (fun j => (Scheme.Modules.Differentials.relativeDifferentialDerivation
          (toSpec R ι)).d (eulerCoordinateRatio R ι (e.symm 0) (e.symm j.succ) hi))) =
      twistingGenerator R ι (-(Fintype.card ι : ℤ)) (e.symm 0) hi := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have h := differentialDeterminantTwistingIso_mk R ι n e (e.symm 0) hi
    (determinantOmegaSectionsBasis R ι n e (e.symm 0) hi)
  rw [determinantEulerPivotForm_basis] at h
  simp only [e.apply_symm_apply, Fin.val_zero, pow_zero, one_smul] at h
  have hb : (determinantOmegaSectionsBasis R ι n e (e.symm 0) hi :
      Fin n → Γ(Ω, T)) = fun j => (Scheme.Modules.Differentials.relativeDifferentialDerivation
        (toSpec R ι)).d (eulerCoordinateRatio R ι (e.symm 0) (e.symm j.succ) hi) := by
    funext j
    rw [determinantOmegaSectionsBasis_apply]
    simp only [e.apply_symm_apply, Fin.zero_succAbove]
  rw [hb] at h
  have hc : Fintype.card ι = n + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  let hd : -(n + 1 : ℤ) = -(Fintype.card ι : ℤ) := by
    rw [hc, Nat.cast_add, Nat.cast_one]
  let q : twistingSheaf R ι (-(n + 1 : ℤ)) ≅
      twistingSheaf R ι (-(Fintype.card ι : ℤ)) :=
    eqToIso (congrArg (twistingSheaf R ι) hd)
  change q.hom.val.app (op T)
    ((differentialDeterminantTwistingIso R ι n e).hom.val.app (op T) _) = _
  rw [h]
  exact degreeIso_generator R ι _ _ hd (e.symm 0) hi

private def residueForm {T : (P).Opens}
    (h : ∀ a : Fin (n + 1), T ≤ coordinateOpen R ι (e.symm a)) (r : R) : Γ(K, T) :=
  (sectionRestrict P le_top
    (((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r) *
      ∏ j : Fin n, (coordinateTransitionOn R ι (e.symm 0) (e.symm j.succ)
        (h 0) (h j.succ)).val) •
    (SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app (op T)
      (fun j => (Scheme.Modules.Differentials.relativeDifferentialDerivation (toSpec R ι)).d
        (eulerCoordinateRatio R ι (e.symm 0) (e.symm j.succ) (h 0)))

private theorem residueForm_laurent (r : R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let s := coordinateTupleSet e.symm
    let h (a : Fin (n + 1)) := coordinateProductOpen_le_chart R ι s (e.symm a)
      ((mem_coordinateTupleSet e.symm (e.symm a)).mpr ⟨a, rfl⟩)
    (twistingSectionsLaurentAddEquiv R ι s (e.symm 0)
      ((mem_coordinateTupleSet e.symm (e.symm 0)).mpr ⟨0, rfl⟩)
      (-(Fintype.card ι : ℤ))
      ((differentialResidueTwistingIso R ι n e).hom.val.app
        (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)))
        (residueForm R ι n e h r))).val =
    AddMonoidAlgebra.single (coordinateWeightExponent e.symm coordinateResidueWeight
      (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) r := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  intro s h
  unfold residueForm
  rw [((differentialResidueTwistingIso R ι n e).hom.val.app _).hom.map_smul,
    differentialResidueTwistingIso_enum_wedge, ← smul_smul,
    twistingSectionsLaurentAddEquiv_smul]
  change r • (twistingSectionsLaurentAddEquiv R ι s (e.symm 0)
    ((mem_coordinateTupleSet e.symm (e.symm 0)).mpr ⟨0, rfl⟩) _
      ((∏ j : Fin n, (coordinateTransitionOn R ι (e.symm 0) (e.symm j.succ)
        (h 0) (h j.succ)).val) • twistingGenerator R ι _ (e.symm 0) (h 0))).val = _
  rw [twistLaurent_smul_generator, map_prod, enum_transition_product]
  simp


private theorem moduleCechMap_component {A : Type u} [CommRing A]
    (X : Scheme.{u}) (α : A →+* Γ(X, ⊤)) {M N : X.Modules} {I : Type u}
    (U : I → X.Opens) (φ : M ⟶ N) (q : ℕ)
    (x : (moduleCechComplex X α M U).X q) (a : Fin (q + 1) → I) :
    (Pi.π (fun b : Fin (q + 1) → I => (moduleSectionsPresheaf X α N).obj
      (op (tupleOpen U q b))) a) ((moduleCechMap X α U φ).f q x) =
    φ.val.app (op (tupleOpen U q a))
      ((Pi.π (fun b : Fin (q + 1) → I => (moduleSectionsPresheaf X α M).obj
        (op (tupleOpen U q b))) a) x) := by
  have h : (moduleCechMap X α U φ).f q ≫
      Pi.π (fun b : Fin (q + 1) → I => (moduleSectionsPresheaf X α N).obj
        (op (tupleOpen U q b))) a =
    Pi.π (fun b : Fin (q + 1) → I => (moduleSectionsPresheaf X α M).obj
      (op (tupleOpen U q b))) a ≫
        ((moduleSectionsPresheafFunctor X α).map φ).app (op (tupleOpen U q a)) := by
    change (Limits.Pi.map (fun b : Fin (q + 1) → I =>
      ((moduleSectionsPresheafFunctor X α).map φ).app (op (tupleOpen U q b)))) ≫ _ = _
    exact Pi.map_π _ a
  exact ConcreteCategory.congr_hom h x

/-- The original enumerated chain component is the all-minus-one Laurent single,
with its original coefficient `r`. -/
theorem differentialResidueCechCycle_laurent_component (r : R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let T := tupleOpen (coordinateOpen R ι) n e.symm
    let x := Pi.π (fun b : Fin (n + 1) → ι =>
      (moduleSectionsPresheaf P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) K).obj
          (op (tupleOpen (coordinateOpen R ι) n b))) e.symm
      ((moduleCechComplex P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K (coordinateOpen R ι)).iCycles n (differentialResidueCechCycle R ι n e r))
    twistingTupleSectionsLinearEquiv R ι (-(Fintype.card ι : ℤ)) n e.symm
      ((differentialResidueTwistingIso R ι n e).hom.val.app (op T) x) =
        coordinateLaurentTupleWeightSingle R _ e.symm coordinateResidueWeight
          (fun i _ => ⟨e i, e.symm_apply_apply i⟩) r := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  intro T x
  have h := congrFun (residueCycle_chain_image R ι n e r) e.symm
  rw [laurentResidueCycle_enum] at h
  change (twistingCechLaurentTermIso R ι (-(Fintype.card ι : ℤ)) n).hom
    (((cechComplexFunctor (coordinateOpen R ι)).map
      ((moduleSectionsPresheafFunctor P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).map
          (differentialResidueTwistingIso R ι n e).hom)).f n
            ((moduleCechComplex P
              ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
              K (coordinateOpen R ι)).iCycles n
                (differentialResidueCechCycle R ι n e r))) e.symm = _ at h
  rw [twistingCechLaurentTermIso_hom_apply] at h
  erw [moduleCechMap_component] at h
  exact h

private theorem nativeRestriction_id (X : Scheme.{u}) (M : X.Modules) (T : X.Opens)
    (x : Γ(M, T)) : M.val.map (𝟙 (op T)) x = x := by
  rw [PresheafOfModules.map_id]
  rfl

private theorem residueForm_of_laurent {T : (P).Opens}
    (hT : T = Proj.basicOpen (homogeneousSubmodule ι R)
      (coordinateProduct R ι (coordinateTupleSet e.symm)))
    (h : ∀ a : Fin (n + 1), T ≤ coordinateOpen R ι (e.symm a))
    (x : Γ(K, T)) (r : R)
    (hx : letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
      (twistingSectionsLaurentAddEquiv R ι (coordinateTupleSet e.symm) (e.symm 0)
        ((mem_coordinateTupleSet e.symm (e.symm 0)).mpr ⟨0, rfl⟩)
        (-(Fintype.card ι : ℤ))
        ((twistingSheaf R ι (-(Fintype.card ι : ℤ))).val.map
          (eqToIso hT.symm).hom.op
          ((differentialResidueTwistingIso R ι n e).hom.val.app (op T) x))).val =
      AddMonoidAlgebra.single (coordinateWeightExponent e.symm coordinateResidueWeight
        (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) r) :
    x = residueForm R ι n e h r := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  subst T
  change (twistingSectionsLaurentAddEquiv R ι (coordinateTupleSet e.symm) (e.symm 0)
    ((mem_coordinateTupleSet e.symm (e.symm 0)).mpr ⟨0, rfl⟩) _
    ((twistingSheaf R ι (-(Fintype.card ι : ℤ))).val.map (𝟙 _)
      ((differentialResidueTwistingIso R ι n e).hom.val.app _ x))).val = _ at hx
  rw [nativeRestriction_id] at hx
  apply (((SheafOfModules.evaluation (P).ringCatSheaf _).mapIso
    (differentialResidueTwistingIso R ι n e)).toLinearEquiv).injective
  apply (twistingSectionsLaurentAddEquiv R ι (coordinateTupleSet e.symm) (e.symm 0)
    ((mem_coordinateTupleSet e.symm (e.symm 0)).mpr ⟨0, rfl⟩)
    (-(Fintype.card ι : ℤ))).injective
  apply Subtype.ext
  calc
    _ = AddMonoidAlgebra.single (coordinateWeightExponent e.symm coordinateResidueWeight
        (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) r := hx
    _ = _ := (residueForm_laurent R ι n e r).symm

private theorem residueCycle_component (r : R) :
    Pi.π (fun b : Fin (n + 1) → ι =>
      (moduleSectionsPresheaf P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) K).obj
          (op (tupleOpen (coordinateOpen R ι) n b))) e.symm
      ((moduleCechComplex P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K (coordinateOpen R ι)).iCycles n (differentialResidueCechCycle R ι n e r)) =
      residueForm R ι n e (tupleOpen_le (coordinateOpen R ι) n e.symm) r := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  apply residueForm_of_laurent R ι n e (coordinateTupleOpen_eq R ι n e.symm)
    (tupleOpen_le (coordinateOpen R ι) n e.symm) _ r
  have h := congrArg Subtype.val (differentialResidueCechCycle_laurent_component R ι n e r)
  rw [coordinateLaurentTupleWeightSingle_val] at h
  exact h


include e in
private theorem residueOmega_qc : (K).IsQuasicoherent := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  exact (SheafOfModules.isQuasicoherent (P).ringCatSheaf).prop_of_iso
    (differentialResidueTwistingIso R ι n e).symm inferInstance

private theorem coordinateTuple_affine (p : ℕ) (a : Fin (p + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k => coordinateOpen R ι (a k)) := by
  change IsAffineOpen (tupleOpen (coordinateOpen R ι) p a)
  rw [coordinateTupleOpen_eq, basicOpen_coordinateProduct]
  exact isAffineOpen_coordinateIntersection R ι (coordinateTupleSet a)
    ⟨a 0, (mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩⟩

include e in
private def residueOmegaCechComparison :
    let α : R →+* Γ(P, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom P α K n
    (moduleCechComplex P α K (coordinateOpen R ι)).homology n ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf P K) n := by
  letI := residueOmega_qc R ι n e
  exact moduleCechCohomologyLinearEquivAll P
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (coordinateOpen R ι) K (iSup_coordinateOpen_eq_top R ι)
    (coordinateTuple_affine R ι) (injectiveResolution (moduleAddSheaf P K)) n

private theorem actualCechToTwist_naturality (M : (P).Modules) [M.IsQuasicoherent]
    (d : ℤ) (φ : M ⟶ twistingSheaf R ι d) (q : ℕ)
    (x : (moduleCechComplex P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      M (coordinateOpen R ι)).homology q) :
    twistingCechCohomologyLinearEquivAll R ι d q
      (homologyMap (moduleCechMap P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) φ) q x) =
    Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map φ) q
      (moduleCechCohomologyLinearEquivAll P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) M (iSup_coordinateOpen_eq_top R ι)
        (coordinateTuple_affine R ι) (injectiveResolution (moduleAddSheaf P M)) q x) := by
  cases q with
  | zero =>
    exact moduleCechCohomologyLinearEquivZero_naturality P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) φ x
  | succ q =>
    exact moduleCechCohomologyLinearEquiv_naturality P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) (coordinateTuple_affine R ι)
      (injectiveResolution (moduleAddSheaf P M))
      (injectiveResolution (moduleAddSheaf P (twistingSheaf R ι d))) φ q x

private theorem residueOmegaCechComparison_naturality
    (x : (moduleCechComplex P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      K (coordinateOpen R ι)).homology n) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    twistingCechCohomologyLinearEquivAll R ι (-(Fintype.card ι : ℤ)) n
      (homologyMap (moduleCechMap P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) (differentialResidueTwistingIso R ι n e).hom) n x) =
    Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
      (differentialResidueTwistingIso R ι n e).hom) n
        (residueOmegaCechComparison R ι n e x) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := residueOmega_qc R ι n e
  exact actualCechToTwist_naturality R ι K _
    (differentialResidueTwistingIso R ι n e).hom n x

private theorem differentialResidueCechCycle_homology_image (r : R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
      (differentialResidueTwistingIso R ι n e).hom) n
      (residueOmegaCechComparison R ι n e
        ((moduleCechComplex P
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          K (coordinateOpen R ι)).homologyπ n (differentialResidueCechCycle R ι n e r))) =
    twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) n
      ((coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).homologyπ n
        (laurentResidueCycle R ι n e r)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  rw [← residueOmegaCechComparison_naturality]
  let q := differentialResidueCechLaurentIso R ι n e
  let c := laurentResidueCycle R ι n e r
  have hπ := ConcreteCategory.congr_hom (homologyπ_naturality q.inv n) c
  change homologyMap q.inv n
      ((coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).homologyπ n c) =
    (moduleCechComplex P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      K (coordinateOpen R ι)).homologyπ n (differentialResidueCechCycle R ι n e r) at hπ
  rw [← hπ]
  change twistingCechCohomologyLinearEquivAll R ι _ n
      (homologyMap (moduleCechMap P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (coordinateOpen R ι) (differentialResidueTwistingIso R ι n e).hom) n
          (homologyMap q.inv n _)) =
    twistingCechCohomologyLinearEquivAll R ι _ n
      (homologyMap (twistingCechLaurentIso R ι _).inv n _)
  congr 1
  have hq : q.inv ≫ moduleCechMap P
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (coordinateOpen R ι) (differentialResidueTwistingIso R ι n e).hom =
        (twistingCechLaurentIso R ι (-(Fintype.card ι : ℤ))).inv := by
    simp [q, differentialResidueCechLaurentIso, moduleCechMap, Category.assoc,
      ← Functor.map_comp]
  have hh := congrArg (fun f => homologyMap f n) hq
  rw [homologyMap_comp] at hh
  exact ConcreteCategory.congr_hom hh _

private theorem differentialResidueCechCycle_trace (r : R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveTrace R ι n e
      (Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
        (differentialResidueTwistingIso R ι n e).hom) n
        (residueOmegaCechComparison R ι n e
          ((moduleCechComplex P
            ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
            K (coordinateOpen R ι)).homologyπ n
              (differentialResidueCechCycle R ι n e r)))) = r := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  rw [differentialResidueCechCycle_homology_image]
  exact laurentResidueCycle_trace R ι n e r


/-- The whole original chain image is the native residue-weight insertion of the original
full-support cycle, retaining all tuples and the positive enumerated evaluation. -/
theorem differentialResidueCechCycle_chain_image (r : R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let w := coordinateResidueWeight (ι := ι)
    let S := coordinateNegativeSupport w.val
    let q : (RelativeSimplex.complex R S).cycles n ≅
        (RelativeSimplex.complex R S).homology n :=
      (fun (S : Set ι) (hS : S = Set.univ) => show
          (RelativeSimplex.complex R S).cycles n ≅
            (RelativeSimplex.complex R S).homology n from by
        subst S
        exact RelativeSimplex.fullSupportCyclesIso n (by
          simpa only [Fintype.card_fin] using Fintype.card_congr e))
        S coordinateResidueWeight_fullSupport
    let c := q.inv ((RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin
      (R := R) n e S coordinateResidueWeight_fullSupport).symm r)
    (differentialResidueCechLaurentIso R ι n e).hom.f n
      ((moduleCechComplex P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K (coordinateOpen R ι)).iCycles n (differentialResidueCechCycle R ι n e r)) =
      (coordinateLaurentWeightComplexMap R _ w).f n
        ((RelativeSimplex.complex R S).iCycles n c) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  intro w S q c
  refine (residueCycle_chain_image R ι n e r).trans ?_
  have h := ConcreteCategory.congr_hom
    (cyclesMap_i (coordinateLaurentWeightComplexMap R _ w) n) c
  exact h

/-- The actual enumerated Cech component is the product of original inverse ratios times
the original ratio-differential wedge, with its original restricted structural scalar. -/
theorem differentialResidueCechCycle_component (r : R) :
    let T := tupleOpen (coordinateOpen R ι) n e.symm
    let h := tupleOpen_le (coordinateOpen R ι) n e.symm
    Pi.π (fun b : Fin (n + 1) → ι =>
      (moduleSectionsPresheaf P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) K).obj
          (op (tupleOpen (coordinateOpen R ι) n b))) e.symm
      ((moduleCechComplex P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K (coordinateOpen R ι)).iCycles n (differentialResidueCechCycle R ι n e r)) =
      (sectionRestrict P (show T ≤ ⊤ from le_top)
        (((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r) *
          ∏ j : Fin n, (coordinateTransitionOn R ι (e.symm 0) (e.symm j.succ)
            (h 0) (h j.succ)).val) •
        (SheafOfModulesOfCommRing.exteriorPowerMk (P).sheaf Ω n).app (op T)
          (fun j => (Scheme.Modules.Differentials.relativeDifferentialDerivation
            (toSpec R ι)).d (eulerCoordinateRatio R ι (e.symm 0) (e.symm j.succ) (h 0))) :=
  residueCycle_component R ι n e r

/-- The ordinary cohomology class of the actual residue cycle under the native Cech comparison. -/
def differentialResidueCohomologyClass (e : ι ≃ Fin (n + 1)) (r : R) :
    Sheaf.H.{u + 1} (moduleAddSheaf P K) n := by
  letI : (K).IsQuasicoherent := by exact residueOmega_qc R ι n e
  exact moduleCechCohomologyLinearEquivAll P
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    (coordinateOpen R ι) K (iSup_coordinateOpen_eq_top R ι)
    (by exact coordinateTuple_affine R ι) (injectiveResolution (moduleAddSheaf P K)) n
      ((moduleCechComplex P
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        K (coordinateOpen R ι)).homologyπ n (differentialResidueCechCycle R ι n e r))

/-- The unchanged projective trace of the actual differential residue class, transported
through the same original determinant comparison, is its original coefficient. -/
theorem differentialResidueCohomologyClass_trace (r : R) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    projectiveTrace R ι n e
      (Sheaf.H.map ((SheafOfModules.toSheaf (P).ringCatSheaf).map
        (differentialResidueTwistingIso R ι n e).hom) n
          (differentialResidueCohomologyClass R ι n e r)) = r :=
  differentialResidueCechCycle_trace R ι n e r

end AlgebraicGeometry.Scheme.Cohomology

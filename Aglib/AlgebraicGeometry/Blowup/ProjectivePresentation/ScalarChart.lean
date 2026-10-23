/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.ChartMap
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.AffineEmbedding
public import Aglib.AlgebraicGeometry.Blowup.IdealFrames

/-!
# Actual scalar-extended saturated blowup charts

The full tensor saturated chart is compared with the original scalar Rees Away
chart by an actual ring equivalence. The original coefficient maps, numerators,
projection equations and denominator cover are proved without flatness or an
image-ideal blowup comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TensorProduct HomogeneousLocalization
open MvPolynomial Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates

/-- The original composition equation retained with its actual three scheme morphisms. -/
structure ChartTriangleEq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) : Prop where
  eq : f ≫ g = h

private theorem chart_projection_paste {U Q P Z Y A : Scheme.{u}}
    (t : U ⟶ Q) (e : Q ⟶ P) (p : P ⟶ Y) (s : Q ⟶ Z) (r : Z ⟶ Y)
    (v : U ⟶ A) (a : A ⟶ Z) (b : A ⟶ Y)
    (he : ChartTriangleEq e p (s ≫ r)) (ht : ChartTriangleEq t s (v ≫ a))
    (ha : ChartTriangleEq a r b) : ChartTriangleEq (t ≫ e) p (v ≫ b) := by
  refine ⟨?_⟩
  calc
    _ = t ≫ (s ≫ r) := by rw [Category.assoc, he.eq]
    _ = (t ≫ s) ≫ r := (Category.assoc _ _ _).symm
    _ = (v ≫ a) ≫ r := congrArg (fun z => z ≫ r) ht.eq
    _ = _ := by rw [Category.assoc, ha.eq]

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The original saturated chart equivalence with the actual generic degree-zero coefficient
action. -/
def originalAwayEquiv (a : I) :
    letI := Away.scalarAlgebra R (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
    reesAlgebra.homogeneousAway I a ≃ₐ[R] affineBlowupAlgebra R I a := by
  let := Away.scalarAlgebra R (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
  refine { (reesAlgebra.awayEquiv I a).toRingEquiv with commutes' := ?_ }
  intro r
  change reesAlgebra.awayEquiv I a
      (fromZeroRingHom (reesAlgebra.grading I) (Submonoid.powers (reesAlgebra.degreeOne I a))
        (algebraMap R (reesAlgebra.grading I 0) r)) = _
  have h : algebraMap R (reesAlgebra.grading I 0) r = (reesAlgebra.degreeZeroEquiv I).symm r := by
    apply Subtype.ext
    exact (reesAlgebra.degreeZeroEquiv_symm_coe I r).symm
  exact (congrArg (fun z => reesAlgebra.awayEquiv I a
    (fromZeroRingHom (reesAlgebra.grading I) (Submonoid.powers (reesAlgebra.degreeOne I a)) z))
      h).trans (reesAlgebra.awayEquiv_base I a r)

/-- The original degree-one homogeneous fraction retains its literal saturated ratio. -/
theorem originalAwayEquiv_ratio (a b : I) :
    letI := Away.scalarAlgebra R (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
    originalAwayEquiv I a
      (Away.mk (reesAlgebra.grading I) (reesAlgebra.degreeOne_mem I a) 1
        (reesAlgebra.degreeOne I b)
        (by simpa only [one_smul] using reesAlgebra.degreeOne_mem I b)) =
      ratio R I a b := by
  let := Away.scalarAlgebra R (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
  apply Subtype.ext
  exact reesAlgebra.awayEquiv_ratio I a b

/-- The original ideal element mapped to its ratio in the original saturated denominator chart. -/
def ratioLinearMap (a : I) : I →ₗ[R] affineBlowupAlgebra R I a where
  toFun := ratio R I a
  map_add' b c := by
    apply Subtype.ext
    change algebraMap R (Localization.Away (a : R)) ((b : R) + c) *
        IsLocalization.Away.invSelf (a : R) =
      algebraMap R (Localization.Away (a : R)) b * IsLocalization.Away.invSelf (a : R) +
        algebraMap R (Localization.Away (a : R)) c * IsLocalization.Away.invSelf (a : R)
    rw [map_add, add_mul]
  map_smul' r b := by
    apply Subtype.ext
    simp only [RingHom.id_apply, Algebra.smul_def]
    change algebraMap R (Localization.Away (a : R)) (r * (b : R)) *
        IsLocalization.Away.invSelf (a : R) =
      algebraMap R (Localization.Away (a : R)) r *
        (algebraMap R (Localization.Away (a : R)) b * IsLocalization.Away.invSelf (a : R))
    rw [map_mul, mul_assoc]

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The scalar extension of the original ratio map on the full tensor ideal. -/
def scalarRatioLinearMap (a : I) :
    S ⊗[R] I →ₗ[S] S ⊗[R] affineBlowupAlgebra R I a :=
  (ratioLinearMap I a).baseChange S

theorem scalarRatioLinearMap_tmul (a b : I) (s : S) :
    scalarRatioLinearMap I S a (s ⊗ₜ[R] b) = s ⊗ₜ[R] ratio R I a b :=
  LinearMap.baseChange_tmul (ratioLinearMap I a) s b

/-- Transport the actual tensor chart through its original chart equivalence and scalar
extension ring equivalence. Coefficient compatibility is retained separately. -/
def tensorChartRingComparison
    {R S D E H : Type u} [CommRing R] [CommRing S] [CommRing D] [CommRing E] [CommRing H]
    [Algebra R S] [Algebra R D] [Algebra R E]
    (e : D ≃ₐ[R] E) (k : S ⊗[R] D ≃+* H) : S ⊗[R] E ≃+* H :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e.symm).toRingEquiv.trans k

private theorem tensorChartRingComparison_tmul
    {R S D E H : Type u} [CommRing R] [CommRing S] [CommRing D] [CommRing E] [CommRing H]
    [Algebra R S] [Algebra R D] [Algebra R E]
    (e : D ≃ₐ[R] E) (k : S ⊗[R] D ≃+* H) (s : S) (x : E) :
    tensorChartRingComparison e k (s ⊗ₜ[R] x) = k (s ⊗ₜ[R] e.symm x) := by
  change k ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e.symm)
    (s ⊗ₜ[R] x)) = _
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl]
  rfl

private theorem tensorChartRingComparison_base
    {R S D E H : Type u} [CommRing R] [CommRing S] [CommRing D] [CommRing E] [CommRing H]
    [Algebra R S] [Algebra R D] [Algebra R E]
    (e : D ≃ₐ[R] E) (k : S ⊗[R] D ≃+* H) (s : S) :
    tensorChartRingComparison e k (algebraMap S (S ⊗[R] E) s) =
      k (algebraMap S (S ⊗[R] D) s) := by
  change tensorChartRingComparison e k (s ⊗ₜ[R] 1) = k (s ⊗ₜ[R] 1)
  rw [tensorChartRingComparison_tmul]
  exact congrArg (fun x => k (s ⊗ₜ[R] x)) e.symm.toRingHom.map_one

/-- Construct the actual scalar ring comparison, native chart arrow and original triangle
together, before specializing the graded algebra or its original affine chart. -/
def gradedChartArrowWithEquation
    (R : Type u) [CommRing R] {D : Type u} [dRing : CommRing D] [aD : Algebra R D]
    (H : ℕ → Submodule R D) [hG : GradedAlgebra H]
    (S : Type u) [CommRing S] [Algebra R S] {f : D} (hf : f ∈ H 1)
    {A : Type u} [CommRing A] [Algebra R A]
    (e : letI := Away.scalarAlgebra R H f; Away H f ≃ₐ[R] A)
    (oldChart : Spec (.of A) ⟶ Proj H)
    (ho : ChartTriangleEq (Spec.map (CommRingCat.ofHom e.toRingHom))
      (Proj.awayι H f hf Nat.zero_lt_one) oldChart) :
    letI := Away.scalarAlgebra R H f
    letI := Away.scalarAlgebra S (Away.scalarGrading R H S) ((1 : S) ⊗ₜ[R] f)
    {t : Spec (.of (S ⊗[R] A)) ⟶ Proj (Away.scalarGrading R H S) //
      t = ringChartMap (Away.scalarGrading R H S) ((1 : S) ⊗ₜ[R] f)
          (Away.scalarDenominator_mem R H S hf)
          (tensorChartRingComparison e (Away.scalarExtensionEquiv R H S hf).toRingEquiv) ∧
        ChartTriangleEq t (Proj.DegreeOneBaseChange.scalarMap R H S)
          (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫
              oldChart)} := by
  let := Away.scalarAlgebra R H f
  let := Away.scalarAlgebra S (Away.scalarGrading R H S) ((1 : S) ⊗ₜ[R] f)
  let k := (Away.scalarExtensionEquiv R H S hf).toRingEquiv
  let E := tensorChartRingComparison e k
  let ε := (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
  let κ := CommRingCat.ofHom E.symm.toRingHom
  let μ := CommRingCat.ofHom (Away.map (Away.scalarGradedMap R H S) f)
  let ν := CommRingCat.ofHom e.toRingHom
  have hE (x : Away H f) :
      E ((1 : S) ⊗ₜ[R] e x) = Away.map (Away.scalarGradedMap R H S) f x := by
    change k ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e.symm)
      ((1 : S) ⊗ₜ[R] e x)) = _
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, e.symm_apply_apply]
    exact Away.scalarExtensionEquiv_one_tmul R H S hf x
  have hcat : μ ≫ κ = ν ≫ CommRingCat.ofHom ε := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change E.symm (Away.map (Away.scalarGradedMap R H S) f x) = (1 : S) ⊗ₜ[R] e x
    apply E.injective
    exact (E.apply_symm_apply _).trans (hE x).symm
  refine ⟨ringChartMap (Away.scalarGrading R H S) ((1 : S) ⊗ₜ[R] f)
    (Away.scalarDenominator_mem R H S hf) E, rfl, ⟨?_⟩⟩
  exact (spec_square_paste κ μ (CommRingCat.ofHom ε) ν
    (Proj.awayι (Away.scalarGrading R H S) ((1 : S) ⊗ₜ[R] f)
      (Away.scalarDenominator_mem R H S hf) Nat.zero_lt_one)
    (Proj.DegreeOneBaseChange.scalarMap R H S) (Proj.awayι H f hf Nat.zero_lt_one)
    (Proj.DegreeOneBaseChange.scalarChart_awayι_isPullback R H S hf).w.symm hcat).trans
      (congrArg (fun z => Spec.map (CommRingCat.ofHom ε) ≫ z) ho.eq)

/-- The actual ring comparison is composed before specifying the scalar action on its target. -/
def scalarChartRingEquiv (a : I) :
    S ⊗[R] affineBlowupAlgebra R I a ≃+*
      Away (Away.scalarGrading R (reesAlgebra.grading I) S)
        ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a) := by
  let := Away.scalarAlgebra R (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
  let := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
    ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
  exact tensorChartRingComparison (R := R) (S := S) (originalAwayEquiv I a)
    (Away.scalarExtensionEquiv R (reesAlgebra.grading I) S
      (reesAlgebra.degreeOne_mem I a)).toRingEquiv

/-- The original scalar coefficient map is preserved by the actual ring comparison. -/
theorem scalarChartRingEquiv_base (a : I) (s : S) :
    letI := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
      ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
    scalarChartRingEquiv I S a (algebraMap S (S ⊗[R] affineBlowupAlgebra R I a) s) =
      algebraMap S (Away (Away.scalarGrading R (reesAlgebra.grading I) S)
        ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)) s := by
  let := Away.scalarAlgebra R (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
  let := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
    ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
  rw [scalarChartRingEquiv, tensorChartRingComparison_base]
  exact (Away.scalarExtensionEquiv R (reesAlgebra.grading I) S
    (reesAlgebra.degreeOne_mem I a)).commutes s

/-- The inverse ring comparison retains the same original S coefficient map. -/
theorem scalarChartRingEquiv_symm_base (a : I) (s : S) :
    letI := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
      ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
    (scalarChartRingEquiv I S a).symm
        (algebraMap S (Away (Away.scalarGrading R (reesAlgebra.grading I) S)
          ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)) s) =
      algebraMap S (S ⊗[R] affineBlowupAlgebra R I a) s := by
  let := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
    ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
  apply (scalarChartRingEquiv I S a).injective
  rw [RingEquiv.apply_symm_apply, scalarChartRingEquiv_base]

/-- The actual tensor chart isomorphism retains each original coefficient and ratio numerator. -/
theorem scalarChartRingEquiv_tmul_ratio (a b : I) (s : S) :
    letI := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
      ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
    scalarChartRingEquiv I S a (s ⊗ₜ[R] ratio R I a b) =
      Away.mk (Away.scalarGrading R (reesAlgebra.grading I) S)
        (Away.scalarDenominator_mem R (reesAlgebra.grading I) S (reesAlgebra.degreeOne_mem I a))
        1 (s ⊗ₜ[R] reesAlgebra.degreeOne I b)
        (by simpa only [one_smul] using
          Submodule.tmul_mem_baseChange_of_mem s (reesAlgebra.degreeOne_mem I b)) := by
  let := Away.scalarAlgebra R (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
  let := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
    ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
  have hr : (originalAwayEquiv I a).symm (ratio R I a b) =
      Away.mk (reesAlgebra.grading I) (reesAlgebra.degreeOne_mem I a) 1
        (reesAlgebra.degreeOne I b)
        (by simpa only [one_smul] using reesAlgebra.degreeOne_mem I b) := by
    apply (originalAwayEquiv I a).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (originalAwayEquiv_ratio I a b).symm
  rw [scalarChartRingEquiv, tensorChartRingComparison_tmul, hr]
  exact Away.scalarExtensionEquiv_tmul_mk R (reesAlgebra.grading I) S
    (reesAlgebra.degreeOne_mem I a) 1 (reesAlgebra.degreeOne I b)
    (reesAlgebra.degreeOne_mem I b) s

/-- Every full tensor-ideal element has its original dehomogenized Rees numerator. -/
theorem scalarRatio_numerator (a : I) (v : S ⊗[R] I) :
    letI := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
      ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
    scalarChartRingEquiv I S a (scalarRatioLinearMap I S a v) =
      Away.dehomogenize (Away.scalarGrading R (reesAlgebra.grading I) S)
        (Away.scalarDenominator_mem R (reesAlgebra.grading I) S (reesAlgebra.degreeOne_mem I a))
        (reesAlgebra.scalarDegreeOneMap I S v) := by
  let := Away.scalarAlgebra S (Away.scalarGrading R (reesAlgebra.grading I) S)
    ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
  induction v using TensorProduct.inductionOn with
  | tmul s b =>
    rw [scalarRatioLinearMap_tmul]
    exact (scalarChartRingEquiv_tmul_ratio I S a b s).trans
      (Away.dehomogenize_homogeneous (Away.scalarGrading R (reesAlgebra.grading I) S)
        (Away.scalarDenominator_mem R (reesAlgebra.grading I) S (reesAlgebra.degreeOne_mem I a))
        (s ⊗ₜ[R] reesAlgebra.degreeOne I b)
        (Submodule.tmul_mem_baseChange_of_mem s (reesAlgebra.degreeOne_mem I b))).symm
  | add v w hv hw => simp only [map_add, hv, hw]

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates


namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates

variable {R : Type u} [CommRing R] (I : Ideal R)
  (S : Type u) [CommRing S] [Algebra R S] (a : I)

local notation "G" => Away.scalarGrading R (reesAlgebra.grading I) S
local notation "α" => ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
local notation "C" => affineBlowupAlgebra R I a
local notation "T" => S ⊗[R] C
local notation "hα" => Away.scalarDenominator_mem R (reesAlgebra.grading I) S
  (reesAlgebra.degreeOne_mem I a)

theorem scalarChartRingEquiv_one_tmul_awayEquiv (x : reesAlgebra.homogeneousAway I a) :
    letI := Away.scalarAlgebra S G α
    scalarChartRingEquiv I S a ((1 : S) ⊗ₜ[R] reesAlgebra.awayEquiv I a x) =
      Away.map (Away.scalarGradedMap R (reesAlgebra.grading I) S)
        (reesAlgebra.degreeOne I a) x := by
  let := Away.scalarAlgebra R (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
  let := Away.scalarAlgebra S G α
  have hr : (originalAwayEquiv I a).symm (reesAlgebra.awayEquiv I a x) = x := by
    exact (originalAwayEquiv I a).symm_apply_apply x
  rw [scalarChartRingEquiv, tensorChartRingComparison_tmul, hr]
  exact Away.scalarExtensionEquiv_one_tmul R (reesAlgebra.grading I) S
    (reesAlgebra.degreeOne_mem I a) x

theorem scalarChartRingEquiv_symm_originalMap :
    letI := Away.scalarAlgebra S G α
    (scalarChartRingEquiv I S a).symm.toRingHom.comp
        (Away.map (Away.scalarGradedMap R (reesAlgebra.grading I) S)
          (reesAlgebra.degreeOne I a)) =
      (Algebra.TensorProduct.includeRight : C →ₐ[R] T).toRingHom.comp
        (reesAlgebra.awayEquiv I a).toRingHom := by
  let := Away.scalarAlgebra S G α
  apply RingHom.ext
  intro x
  apply (scalarChartRingEquiv I S a).injective
  exact ((scalarChartRingEquiv I S a).apply_symm_apply _).trans
    (scalarChartRingEquiv_one_tmul_awayEquiv I S a x).symm

/-- The original scalar chart map and its original triangle are projected from one witness. -/
def scalarChartToProjData :=
  gradedChartArrowWithEquation R (D := reesAlgebra I)
    (dRing := inferInstanceAs (CommRing (reesAlgebra I)))
    (aD := inferInstanceAs (Algebra R (reesAlgebra I))) (reesAlgebra.grading I)
    (hG := inferInstanceAs (GradedAlgebra (reesAlgebra.grading I))) S
    (reesAlgebra.degreeOne_mem I a) (A := C)
    (originalAwayEquiv I a) (affineProjChart I a) ⟨rfl⟩

/-- The original saturated tensor chart mapped to Proj of the full scalar Rees algebra. -/
def scalarChartToProj : Spec (CommRingCat.of T) ⟶ Proj G :=
  (scalarChartToProjData I S a).val

/-- The witness value is the same original transported native homogeneous chart. -/
theorem scalarChartToProj_eq :
    scalarChartToProj I S a = ringChartMap G α hα (scalarChartRingEquiv I S a) :=
  (scalarChartToProjData I S a).property.1

theorem scalarChartToProj_toSpec :
    scalarChartToProj I S a ≫ Proj.DegreeOneEmbedding.structureMap G =
      Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
  let := Away.scalarAlgebra S G α
  have he : CommRingCat.ofHom (Proj.DegreeOneBaseChange.coefficientMap S G α) ≫
      CommRingCat.ofHom (scalarChartRingEquiv I S a).symm.toRingHom =
        CommRingCat.ofHom (algebraMap S T) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (scalarChartRingEquiv_symm_base I S a)
  rw [scalarChartToProj_eq]
  change (Spec.map (CommRingCat.ofHom (scalarChartRingEquiv I S a).symm.toRingHom) ≫
    Proj.awayι G α hα Nat.zero_lt_one) ≫ _ = _
  rw [Category.assoc, Proj.DegreeOneBaseChange.chart_toSpec S G,
    ← Spec.map_comp, he]

theorem scalarChartToProj_scalarMap :
    ChartTriangleEq (scalarChartToProj I S a)
      (Proj.DegreeOneBaseChange.scalarMap R (reesAlgebra.grading I) S)
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[R] T).toRingHom) ≫ affineProjChart I a) :=
  (scalarChartToProjData I S a).property.2

variable (B : BlowupDatum (affineCenter R I))

/-- The original scalar chart transported to the literal pullback of the specified blowup. -/
def scalarChartToPullback :
    Spec (CommRingCat.of T) ⟶
      pullback B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  scalarChartToProj I S a ≫ (AffineEmbedding.scalarReesIso B S).hom

@[reassoc]
theorem scalarChartToPullback_snd :
    scalarChartToPullback I S a B ≫
      pullback.snd B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
        Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
  rw [scalarChartToPullback, Category.assoc, AffineEmbedding.scalarReesIso_hom_snd]
  exact scalarChartToProj_toSpec I S a

theorem scalarChartToPullback_fst :
    ChartTriangleEq (scalarChartToPullback I S a B)
      (pullback.fst B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[R] T).toRingHom) ≫
          IdealFrames.chartMap B a) := by
  have he : ChartTriangleEq (AffineEmbedding.scalarReesIso B S).hom
      (pullback.fst B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Proj.DegreeOneBaseChange.scalarMap R (reesAlgebra.grading I) S ≫
        ((affineProjBlowupDatum I).comparisonIso B).hom) :=
    ⟨AffineEmbedding.scalarReesIso_hom_fst B S⟩
  have ha : ChartTriangleEq (affineProjChart I a)
      ((affineProjBlowupDatum I).comparisonIso B).hom (IdealFrames.chartMap B a) := ⟨rfl⟩
  exact chart_projection_paste (scalarChartToProj I S a) (AffineEmbedding.scalarReesIso B S).hom
    (pullback.fst B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (Proj.DegreeOneBaseChange.scalarMap R (reesAlgebra.grading I) S)
    ((affineProjBlowupDatum I).comparisonIso B).hom
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[R] T).toRingHom))
    (affineProjChart I a) (IdealFrames.chartMap B a) he (scalarChartToProj_scalarMap I S a) ha

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates


namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates

variable {R : Type u} [CommRing R] (I : Ideal R)
  (S : Type u) [CommRing S] [Algebra R S]

theorem scalarRatio_denominator (a : I) :
    scalarRatioLinearMap I S a ((1 : S) ⊗ₜ[R] a) = 1 := by
  have ha : ratio R I a a = 1 := by
    apply Subtype.ext
    exact Localization.Away.fraction_self (a : R)
  change (1 : S) ⊗ₜ[R] ratio R I a a = 1
  rw [ha]
  rfl

theorem exists_denominator_combination {κ : Type u} (v : κ → S ⊗[R] I)
    (hv : Submodule.span S (Set.range v) = ⊤) (a : I) :
    ∃ u : κ →₀ S, Finsupp.linearCombination S v u = (1 : S) ⊗ₜ[R] a ∧
      u.sum (fun i r => algebraMap S (S ⊗[R] affineBlowupAlgebra R I a) r *
        scalarRatioLinearMap I S a (v i)) = 1 := by
  have ha : (1 : S) ⊗ₜ[R] a ∈ LinearMap.range (Finsupp.linearCombination S v) := by
    rw [Finsupp.range_linearCombination, hv]
    exact Submodule.mem_top
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ha
  refine ⟨u, hu, ?_⟩
  have h := congrArg (scalarRatioLinearMap I S a) hu
  rw [Finsupp.apply_linearCombination, scalarRatio_denominator] at h
  change u.sum (fun i r => r • scalarRatioLinearMap I S a (v i)) = 1 at h
  calc
    _ = u.sum (fun i r => r • scalarRatioLinearMap I S a (v i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Algebra.smul_def (u i) (scalarRatioLinearMap I S a (v i))).symm
    _ = 1 := h

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates


namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

private theorem scalar_irrelevant_le_original_denominators :
    (HomogeneousIdeal.irrelevant (Away.scalarGrading R (reesAlgebra.grading I) S)).toIdeal ≤
      Ideal.span (Set.range (fun a : I => (1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)) := by
  have h := Proj.DegreeOneBaseChange.scalar_irrelevant_le_map R (reesAlgebra.grading I) S
  change (HomogeneousIdeal.irrelevant (Away.scalarGrading R (reesAlgebra.grading I) S)).toIdeal ≤
      Ideal.map (Away.scalarGradedMap R (reesAlgebra.grading I) S).toRingHom
        (HomogeneousIdeal.irrelevant (reesAlgebra.grading I)).toIdeal at h
  rw [reesAlgebra.irrelevant_eq_span_degreeOne, Ideal.map_span] at h
  have he : (Away.scalarGradedMap R (reesAlgebra.grading I) S).toRingHom ''
      Set.range (reesAlgebra.degreeOne I) =
        Set.range (fun a : I => (1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a) := by
    ext z
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨reesAlgebra.degreeOne I a, ⟨a, rfl⟩, rfl⟩
  rw [he] at h
  exact h

variable (B : BlowupDatum (affineCenter R I))

/-- Equality on the actual original saturated charts determines a morphism from the full
scalar-extended blowup. The chart cover is derived from the original Rees irrelevant ideal. -/
theorem scalarChart_hom_ext {Z : Scheme.{u}}
    (v w : pullback B.map (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⟶ Z)
    (h : ∀ a : I, scalarChartToPullback I S a B ≫ v =
      scalarChartToPullback I S a B ≫ w) : v = w := by
  let G := Away.scalarGrading R (reesAlgebra.grading I) S
  let C := Proj.affineOpenCoverOfIrrelevantLESpan G
    (fun a : I => (1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
    (fun a => Away.scalarDenominator_mem R (reesAlgebra.grading I) S
      (reesAlgebra.degreeOne_mem I a))
    (fun _ => Nat.zero_lt_one) (scalar_irrelevant_le_original_denominators I)
  apply (cancel_epi (AffineEmbedding.scalarReesIso B S).hom).mp
  apply C.openCover.hom_ext
  intro a
  let := Away.scalarAlgebra S G ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
  let E := scalarChartRingEquiv I S a
  have hC : C.openCover.f a = Proj.awayι G
      ((1 : S) ⊗ₜ[R] reesAlgebra.degreeOne I a)
      (Away.scalarDenominator_mem R (reesAlgebra.grading I) S
        (reesAlgebra.degreeOne_mem I a)) Nat.zero_lt_one := rfl
  rw [hC]
  let : IsIso (Spec.map (CommRingCat.ofHom E.symm.toRingHom)) := by
    change IsIso (Scheme.Spec.mapIso E.symm.toCommRingCatIso.op).hom
    infer_instance
  apply (cancel_epi (Spec.map (CommRingCat.ofHom E.symm.toRingHom))).mp
  simpa only [scalarChartToPullback, scalarChartToProj_eq, ringChartMap, E, Category.assoc]
    using h a

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.ScalarChartCoordinates

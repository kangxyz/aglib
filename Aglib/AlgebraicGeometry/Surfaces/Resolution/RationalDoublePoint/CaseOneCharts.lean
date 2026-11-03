/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Arc
public import Aglib.AlgebraicGeometry.Stalk.LocalBaseIdeal
public import Aglib.RingTheory.Blowup.CaseOne

/-!
# The original Case-I chart as an actual ordinary-blowup stalk

The chart ring is definitionally the original saturated affine blowup algebra.
The chart immersion and stalk comparison come from the existing native atlas.
The coefficient equation identifies the original structural map, not merely
an abstract isomorphic child ring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open IsLocalRing Localization.Away
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseOneChart

variable {A : Type u} [CommRing A] [IsLocalRing A]
    (B : BlowupDatum (affineCenter A (maximalIdeal A)))

/-- The literal original saturated chart in the actual ordinary blowup. -/
def chart (t : maximalIdeal A) : Spec (.of (CaseOne.Chart A t)) ⟶ B.Y :=
  (Blowup.Arc.atlasChartWitness (maximalIdeal A) B t).val

instance chart_isOpenImmersion (t : maximalIdeal A) : IsOpenImmersion (chart B t) :=
  (Blowup.Arc.atlasChartWitness (maximalIdeal A) B t).property.1

@[reassoc]
theorem chart_map (t : maximalIdeal A) :
    chart B t ≫ B.map = Spec.map (CommRingCat.ofHom (algebraMap A (CaseOne.Chart A t))) :=
  (Blowup.Arc.atlasChartWitness (maximalIdeal A) B t).property.2

variable {t : maximalIdeal A} {g : Fin 2 → maximalIdeal A} {Q : CaseOne.Plane A}
    (D : CaseOne.Presentation A t g Q) (M : Ideal (CaseOne.Plane A)) [M.IsMaximal]
    (hQM : Q ∈ M)

private theorem exists_plane_maximalIdeal
    (p : Ideal (CaseOne.Chart A t)) [p.IsMaximal]
    (hp : CaseOne.exceptionalIdeal A t ≤ p) :
    ∃ (N : Ideal (CaseOne.Plane A)) (hN : N.IsMaximal) (hQN : Q ∈ N),
      letI := hN
      D.prime N hQN = p := by
  let I := CaseOne.exceptionalIdeal A t
  let qI := Ideal.Quotient.mk I
  let qQ := Ideal.Quotient.mk (Ideal.span {Q})
  let P := p.map qI
  let N := P.comap D.equiv.symm.toRingHom
  let M := N.comap qQ
  let : P.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa only [qI, Ideal.mk_ker] using hp)
  let : N.IsMaximal := Ideal.comap_isMaximal_of_surjective
    D.equiv.symm.toRingHom D.equiv.symm.surjective
  let : M.IsMaximal := Ideal.comap_isMaximal_of_surjective qQ Ideal.Quotient.mk_surjective
  have hQM : Q ∈ M := by
    change D.equiv.symm (Ideal.Quotient.mk (Ideal.span {Q}) Q) ∈ P
    have hQ : Q ∈ Ideal.span ({Q} : Set (CaseOne.Plane A)) :=
      Ideal.mem_span_singleton_self Q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hQ, map_zero]
    exact P.zero_mem
  refine ⟨M, inferInstance, hQM, ?_⟩
  rw [D.prime_eq_comap M hQM]
  have hM : M.map qQ = N := Ideal.map_comap_of_surjective qQ Ideal.Quotient.mk_surjective N
  rw [hM]
  ext a
  change D.equiv.symm (D.equiv (qI a)) ∈ P ↔ a ∈ p
  rw [D.equiv.symm_apply_apply]
  change a ∈ (p.map qI).comap qI ↔ a ∈ p
  rw [CaseOne.quotient_prime_comap I p hp]

/-- The actual scheme point determined by the original plane-quotient point. -/
def point : B.Y := chart B t ⟨D.prime M hQM, inferInstance⟩

/-- The actual blowup stalk is the same original prime localization used by
Case I, through the native open-immersion and spectrum-stalk maps. -/
def stalkIso : B.Y.presheaf.stalk (point B D M hQM) ≅
    CommRingCat.of (D.LocalRing M hQM) :=
  (Blowup.Arc.openChartStalkWitness (chart B t)
    ⟨D.prime M hQM, inferInstance⟩ _
    (Blowup.Arc.spectrumStalkIso (.of (CaseOne.Chart A t))
      ⟨D.prime M hQM, inferInstance⟩)).val

theorem stalkIso_hom : (stalkIso B D M hQM).hom =
    (chart B t).stalkMap ⟨D.prime M hQM, inferInstance⟩ ≫
      (Blowup.Arc.spectrumStalkIso (.of (CaseOne.Chart A t))
        ⟨D.prime M hQM, inferInstance⟩).hom :=
  (Blowup.Arc.openChartStalkWitness (chart B t)
    ⟨D.prime M hQM, inferInstance⟩ _
    (Blowup.Arc.spectrumStalkIso (.of (CaseOne.Chart A t))
      ⟨D.prime M hQM, inferInstance⟩)).property

/-- The coefficient map is the original structural stalk map followed by
the original chart comparison. -/
theorem stalkIso_stalkScalar :
    (stalkIso B D M hQM).hom.hom.comp (B.map.stalkScalar (point B D M hQM)) =
      D.localMap M hQM := by
  let q : Spec (.of (CaseOne.Chart A t)) := ⟨D.prime M hQM, inferInstance⟩
  let E := Blowup.Arc.spectrumStalkIso (.of (CaseOne.Chart A t)) q
  let J := (chart B t).stalkMap q
  have hg := Blowup.Arc.germ_stalkMap_top (chart B t) q
  have he := Blowup.Arc.germ_localizationBase (.of (CaseOne.Chart A t)) q
  have hb : (Scheme.ΓSpecIso (.of A)).inv ≫ B.map.appTop ≫ (chart B t).appTop ≫
      (Scheme.ΓSpecIso (.of (CaseOne.Chart A t))).hom =
        CommRingCat.ofHom (algebraMap A (CaseOne.Chart A t)) := by
    rw [← Scheme.Hom.comp_appTop_assoc, chart_map, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  have h := Blowup.Arc.coefficient_paste (Scheme.ΓSpecIso (.of A)).inv B.map.appTop
    (B.Y.presheaf.germ ⊤ (point B D M hQM) trivial) J E.hom
    (chart B t).appTop ((Spec (.of (CaseOne.Chart A t))).presheaf.germ ⊤ q trivial)
    (Scheme.ΓSpecIso (.of (CaseOne.Chart A t))).hom
    (Blowup.Arc.localizationBase (.of (CaseOne.Chart A t)) q)
    (CommRingCat.ofHom (algebraMap A (CaseOne.Chart A t))) hg he hb
  have hs : CommRingCat.ofHom (B.map.stalkScalar (point B D M hQM)) ≫
      (stalkIso B D M hQM).hom = CommRingCat.ofHom (D.localMap M hQM) := by
    rw [stalkIso_hom]
    exact h
  exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of (D.LocalRing M hQM) => f.hom) hs

/-- The point lies over the original closed point, with no residue-field
identification hypothesis. -/
theorem map_point : B.map (point B D M hQM) = closedPoint A := by
  change (chart B t ≫ B.map) ⟨D.prime M hQM, inferInstance⟩ = closedPoint A
  rw [chart_map]
  apply PrimeSpectrum.ext
  exact D.prime_comap_base M hQM

instance stalkScalar_isLocal : IsLocalHom (B.map.stalkScalar (point B D M hQM)) :=
  B.map.stalkScalar_isLocalHom_of_closedPoint (point B D M hQM) (map_point B D M hQM)

/-- Regularity is transferred along the actual open-chart stalk comparison. -/
theorem isRegular_iff :
    IsRegularLocalRing (B.Y.presheaf.stalk (point B D M hQM)) ↔
      IsRegularLocalRing (D.LocalRing M hQM) := by
  constructor
  · intro h
    let := h
    exact IsRegularLocalRing.of_ringEquiv (stalkIso B D M hQM).commRingCatIsoToRingEquiv
  · intro h
    let := h
    exact IsRegularLocalRing.of_ringEquiv
      (stalkIso B D M hQM).symm.commRingCatIsoToRingEquiv

/-- The extended original maximal ideal is generated by the same original
exceptional element in the actual scheme stalk. -/
theorem maximalIdeal_map_stalkScalar :
    (maximalIdeal A).map (B.map.stalkScalar (point B D M hQM)) =
      Ideal.span {B.map.stalkScalar (point B D M hQM) (t : A)} := by
  let E := (stalkIso B D M hQM).commRingCatIsoToRingEquiv
  have hc : E.symm.toRingHom.comp (D.localMap M hQM) =
      B.map.stalkScalar (point B D M hQM) := by
    ext a
    apply E.injective
    exact (E.apply_symm_apply (D.localMap M hQM a)).trans
      (RingHom.congr_fun (stalkIso_stalkScalar B D M hQM) a).symm
  have h := congrArg (Ideal.map E.symm.toRingHom) (D.centre M hQM)
  rw [Ideal.map_map, hc, Ideal.map_span, Set.image_singleton] at h
  have ht : E.symm.toRingHom (D.parameter M hQM) =
      B.map.stalkScalar (point B D M hQM) (t : A) := RingHom.congr_fun hc (t : A)
  rw [ht] at h
  exact h

/-- In a singular actual child the unchanged original exceptional element
remains a minimal parameter. -/
theorem parameter_not_mem_sq_of_singular_stalk [IsNoetherianRing A] [IsDomain A]
    (ht : (t : A) ≠ 0) (hQ : Q ≠ 0)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk (point B D M hQM))) :
    B.map.stalkScalar (point B D M hQM) (t : A) ∉
      maximalIdeal (B.Y.presheaf.stalk (point B D M hQM)) ^ 2 := by
  intro h
  let E := (stalkIso B D M hQM).commRingCatIsoToRingEquiv
  have he := Ideal.mem_map_of_mem E h
  rw [Ideal.map_pow, map_ringEquiv_maximalIdeal] at he
  have hv : E (B.map.stalkScalar (point B D M hQM) (t : A)) = D.parameter M hQM :=
    RingHom.congr_fun (stalkIso_stalkScalar B D M hQM) (t : A)
  rw [hv] at he
  exact D.parameter_not_mem_sq M hQM ht hQ
    (fun h => hsing ((isRegular_iff B D M hQM).mpr h)) he

/-- The actual scheme stalk has dimension two, proved from the original
nonzero exceptional equation and parameter. -/
theorem stalk_dimension [IsNoetherianRing A] [IsDomain A]
    (ht : (t : A) ≠ 0) (hQ : Q ≠ 0) :
    ringKrullDim (B.Y.presheaf.stalk (point B D M hQM)) = 2 :=
  (ringKrullDim_eq_of_ringEquiv (stalkIso B D M hQM).commRingCatIsoToRingEquiv).trans
    (D.local_dimension M hQM ht hQ)

/-- Singularity of the actual blowup stalk forces square membership in the
same original plane-point ideal used to construct it. -/
theorem equation_mem_sq_of_singular_stalk [IsNoetherianRing A] [IsDomain A]
    (ht : (t : A) ≠ 0)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk (point B D M hQM))) :
    Q ∈ M ^ 2 :=
  D.equation_mem_sq_of_not_regular M hQM ht
    (fun h => hsing ((isRegular_iff B D M hQM).mpr h))

/-- The original structural residue map commutes with the actual stalk
comparison. This retains its value on every original coefficient class. -/
theorem residue_comparison (a : ResidueField A) :
    ResidueField.mapEquiv (stalkIso B D M hQM).commRingCatIsoToRingEquiv
      (ResidueField.map (B.map.stalkScalar (point B D M hQM)) a) =
      (letI := D.localMap_isLocal M hQM
       ResidueField.map (D.localMap M hQM) a) := by
  let : IsLocalHom (D.localMap M hQM) := D.localMap_isLocal M hQM
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  change IsLocalRing.residue (D.LocalRing M hQM)
    ((stalkIso B D M hQM).hom.hom (B.map.stalkScalar (point B D M hQM) a)) =
      IsLocalRing.residue (D.LocalRing M hQM) (D.localMap M hQM a)
  exact congrArg (IsLocalRing.residue (D.LocalRing M hQM))
    (RingHom.congr_fun (stalkIso_stalkScalar B D M hQM) a)

/-- Case I makes the original structural residue map bijective at the
actual singular blowup stalk. No equality of residue fields is assumed. -/
theorem residue_map_bijective_of_singular_stalk [IsNoetherianRing A] [IsDomain A]
    (ht : (t : A) ≠ 0) (hQ : Q ≠ 0) (hdeg : Q.totalDegree ≤ 2)
    (hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ l : CaseOne.Plane A,
      l.totalDegree ≤ 1 ∧ Q = MvPolynomial.C c * l ^ 2)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk (point B D M hQM))) :
    Function.Bijective (ResidueField.map (B.map.stalkScalar (point B D M hQM))) := by
  let : IsLocalHom (D.localMap M hQM) := D.localMap_isLocal M hQM
  let E := ResidueField.mapEquiv (stalkIso B D M hQM).commRingCatIsoToRingEquiv
  have h := D.residue_map_bijective M hQM ht hQ hdeg hcase
    (fun h => hsing ((isRegular_iff B D M hQM).mpr h))
  refine ⟨(ResidueField.map (B.map.stalkScalar (point B D M hQM))).injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := h.surjective (E z)
  refine ⟨a, E.injective ?_⟩
  exact (residue_comparison B D M hQM a).trans ha

/-- Every actual closed point of this chart above the original closed point
is obtained from its original plane maximal ideal. The point is not replaced
by an abstractly isomorphic residue-field point. -/
theorem exists_plane_point (x : B.Y) (hx : IsClosed ({x} : Set B.Y))
    (hbase : B.map x = closedPoint A) (hchart : x ∈ Set.range (chart B t)) :
    ∃ (N : Ideal (CaseOne.Plane A)) (hN : N.IsMaximal) (hQN : Q ∈ N),
      letI := hN
      point B D N hQN = x := by
  obtain ⟨q, rfl⟩ := hchart
  have hclosed : IsClosed ({q} : Set (Spec (.of (CaseOne.Chart A t)))) := by
    have h := hx.preimage (chart B t).continuous
    convert h using 1
    ext z
    exact (chart B t).isOpenEmbedding.injective.eq_iff.symm
  let : q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hclosed
  have hqbase : q.asIdeal.comap (algebraMap A (CaseOne.Chart A t)) = maximalIdeal A := by
    change (chart B t ≫ B.map) q = closedPoint A at hbase
    rw [chart_map] at hbase
    exact congrArg PrimeSpectrum.asIdeal hbase
  have hp : CaseOne.exceptionalIdeal A t ≤ q.asIdeal := by
    apply q.asIdeal.span_singleton_le_iff_mem.mpr
    change (t : A) ∈ q.asIdeal.comap (algebraMap A (CaseOne.Chart A t))
    rw [hqbase]
    exact t.property
  obtain ⟨N, hN, hQN, hprime⟩ := exists_plane_maximalIdeal D q.asIdeal hp
  let := hN
  refine ⟨N, hN, hQN, ?_⟩
  exact congrArg (chart B t) (PrimeSpectrum.ext hprime)

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseOneChart

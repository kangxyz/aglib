/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.IntermediateFieldModel
public import Aglib.AlgebraicGeometry.Morphisms.Finite.CompletedLocalDegree
public import Aglib.AlgebraicGeometry.Stalk.CompleteSurface
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ClosedSingularPoints

/-!
# Actual completed branches of the intermediate-field model

The existing normalized Cover of a supplied regular intermediate model has
actual finite affine charts. These supply Nagata and dimension bounds on its
original stalks. At a singular point the original complete base, original
scalar map and original finite residue action prove normal-domain completion.
The same full finite local algebra then supplies the canonical completed maps
and the strict degree bound in the original native fraction-field tower.

No resolution of the upper ring, completion-domain hypothesis, smaller-degree
premise or finite selected-stalk hypothesis is used. This leaf does not invoke
induction or construct a finite normalized point chain.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing
open AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover
open AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra

namespace AlgebraicGeometry.Scheme.IntermediateFieldModel

universe u

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]

attribute [local instance] FractionRing.liftAlgebra
  integralClosure.completeIntermediate_fieldFinite

variable (L : IntermediateField (FractionRing R) (FractionRing A))

/-- The supplied intermediate model is eligible for a strictly lower original degree. -/
theorem intermediate_induction_degree_lt (htop : L < ⊤) :
    Module.finrank (FractionRing R) L <
      Module.finrank (FractionRing R) (FractionRing A) := by
  have h : Module.finrank (FractionRing R) L <
      Module.finrank (FractionRing R)
        (⊤ : IntermediateField (FractionRing R) (FractionRing A)) := by
    apply lt_of_le_of_ne (IntermediateField.finrank_le_of_le_right htop.le)
    intro he
    exact htop.ne (IntermediateField.eq_of_le_of_finrank_eq htop.le he)
  simpa only [IntermediateField.finrank_top'] using h

/-- Strictness of the remaining extension is proved from the genuine lower inclusion. -/
theorem remaining_extension_degree_lt (hbot : ⊥ < L) :
    Module.finrank L (FractionRing A) <
      Module.finrank (FractionRing R) (FractionRing A) := by
  simpa only [IntermediateField.finrank_bot'] using IntermediateField.finrank_lt_of_gt hbot

variable [IsIntegrallyClosed A] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R] [Ring.KrullDimLE 2 R]
  {Y : Scheme.{u}} [IsIntegral Y]
  (a : Y ⟶ Spec (.of (integralClosure R L))) [IsDominant a] [IsProper a]
  (ha : IsIso (CommRingCat.ofHom (functionFieldMap a)))

attribute [local instance] pi_isFinite normalization_isLocallyNoetherian

local notation "N" => Cover.normalization a ha (baseMap R A L)
local notation "π" => Cover.pi a ha (baseMap R A L)
local notation "b" => Cover.b a ha (baseMap R A L)

/-- The same finite inverse-image chart is Nagata and has dimension at most two. -/
theorem finiteChart_nagata_and_dimension (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsNagataRing.{u, 0} Γ(N, π ⁻¹ᵁ U) ∧ ringKrullDim Γ(N, π ⁻¹ᵁ U) ≤ 2 := by
  let : Algebra Γ(Y, U) Γ(N, π ⁻¹ᵁ U) := chartAlgebra π U
  let : Module.Finite Γ(Y, U) Γ(N, π ⁻¹ᵁ U) := chart_finite π U hU
  let : Algebra.IsIntegral Γ(Y, U) Γ(N, π ⁻¹ᵁ U) :=
    Algebra.IsIntegral.of_finite Γ(Y, U) Γ(N, π ⁻¹ᵁ U)
  have hc := affineChart_nagata_and_dimension R A L a ha U hU
  refine ⟨hc.1.of_finite, ?_⟩
  have hd : ringKrullDim Γ(N, π ⁻¹ᵁ U) ≤ ringKrullDim Γ(Y, U) := by
    apply Order.krullDim_le_of_strictMono
      (PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(N, π ⁻¹ᵁ U)))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under (R := Γ(Y, U)) hpq
  exact hd.trans hc.2

/-- Nagata and dimension bounds hold on each literal source stalk, before any
closed-point or branch selection. -/
theorem sourceStalk_nagata_and_dimension
    (x : Cover.normalization a ha (baseMap R A L)) :
    IsNagataRing.{u, 0} ((N).presheaf.stalk x) ∧ ringKrullDim ((N).presheaf.stalk x) ≤ 2 := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show π x ∈ (⊤ : Y.Opens) from trivial)
  let : Nonempty U := ⟨⟨π x, hxU⟩⟩
  have hc := finiteChart_nagata_and_dimension R A L a ha U hU
  let V := π ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage π
  have hxV : x ∈ V := hxU
  let p := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let : p.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  let : Algebra Γ(N, V) ((N).presheaf.stalk x) := (N).presheaf.algebra_section_stalk ⟨x, hxV⟩
  let : IsLocalization.AtPrime ((N).presheaf.stalk x) p := hV.isLocalization_stalk ⟨x, hxV⟩
  refine ⟨IsNagataRing.of_isLocalization p.primeCompl hc.1, ?_⟩
  have hl : ringKrullDim ((N).presheaf.stalk x) ≤ ringKrullDim Γ(N, V) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p ((N).presheaf.stalk x)]
    exact p.height_le_ringKrullDim_of_isPrime
  exact hl.trans hc.2

/-- The actual source dimension bound follows from its actual stalks. -/
theorem source_dimension_le_two : topologicalKrullDim N ≤ 2 := by
  rw [topologicalKrullDim_eq_iSup_stalk]
  exact iSup_le fun x => (sourceStalk_nagata_and_dimension R A L a ha x).2

/-- A singular original source point is genuinely closed, with dimension-two stalk. -/
theorem singular_point_closed_dimension
    (x : Cover.normalization a ha (baseMap R A L))
    (hx : ¬ IsRegularLocalRing ((N).presheaf.stalk x)) :
    IsClosed ({x} : Set N) ∧ ringKrullDim ((N).presheaf.stalk x) = 2 := by
  have hn := normalization_normalStalks R A L a ha
  have hd := source_dimension_le_two R A L a ha
  exact ⟨isClosed_singleton_of_singular_of_normal_dimension_le_two N hn hd x hx,
    stalk_dimension_eq_two_of_singular_of_normal_dimension_le_two N hn hd x hx⟩

/-- The literal singular-stalk completion is a normal domain. Completeness of
original A and finiteness of its original residue action are derived here. -/
theorem singular_completion_normalDomain (hdA : ringKrullDim A = 2)
    (x : Cover.normalization a ha (baseMap R A L))
    (hx : ¬ IsRegularLocalRing ((N).presheaf.stalk x)) :
    IsDomain (AdicCompletion (maximalIdeal ((N).presheaf.stalk x)) ((N).presheaf.stalk x)) ∧
      IsIntegrallyClosed
        (AdicCompletion (maximalIdeal ((N).presheaf.stalk x)) ((N).presheaf.stalk x)) := by
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  let : IsLocalRing A := IsDiscreteValuationRing.CompleteExtension.isLocalRing_of_finite R A
  let : IsLocalHom (algebraMap R A) :=
    (algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite R A)).isLocalHom
      (FaithfulSMul.algebraMap_injective R A)
  let : IsAdicComplete (maximalIdeal A) A :=
    IsAdicComplete.maximalIdeal_of_finite_local R A
  let : IsProper b := (b_proper_birational R A L a ha).1
  have hp := singular_point_closed_dimension R A L a ha x hx
  exact (b).normalDomain_completion_stalk_of_complete_surface hdA x hp.1
    (normalization_normalStalks R A L a ha x).2 hp.2
    (sourceStalk_nagata_and_dimension R A L a ha x).1

variable (U : Y.Opens) (hU : IsAffineOpen U) (y : U) [Nonempty U]
  (q : MaximalSpectrum
    (Hom.LocalNormAlgebra.Ring (Cover.pi a ha (baseMap R A L)) U hU y))

local notation "O" => Y.presheaf.stalk y.val
local notation "S" => Hom.LocalNormAlgebra.Ring π U hU y
local notation "Ohat" => AdicCompletion (maximalIdeal O) O

attribute [local instance] stalkAlgebra branchStalkAlgebra
  AdicCompletion.FiniteSemilocal.baseCompletion_domain
  completedStalkAlgebraAt completedFractionAlgebraAt completedStalkMapAt_isLocalHom

/-- The actual regular target stalk is dimension two at a singular branch.
Only the whole finite algebra, not the selected stalk, is finite over it. -/
theorem singular_branch_target_dimension
    (hx : ¬ IsRegularLocalRing ((N).presheaf.stalk (branchPoint π U hU y q))) :
    ringKrullDim O = 2 := by
  let T := (N).presheaf.stalk (branchPoint π U hU y q)
  let : q.asIdeal.IsPrime := q.isMaximal.isPrime
  have hdT := (singular_point_closed_dimension R A L a ha (branchPoint π U hU y q) hx).2
  have hTS : ringKrullDim T ≤ ringKrullDim S := by
    rw [← (branchStalkEquiv π U hU y q).toRingEquiv.ringKrullDim,
      IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)]
    exact q.asIdeal.height_le_ringKrullDim_of_isPrime
  let : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
  have hSO : ringKrullDim S ≤ ringKrullDim O := by
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap O S))
    intro p v hpv
    exact Ideal.IsIntegral.under_lt_under (R := O) hpv
  have hO : ringKrullDim O ≤ 2 := by
    let p := (hU.primeIdealOf y).asIdeal
    let : p.IsPrime := (hU.primeIdealOf y).isPrime
    let : Algebra Γ(Y, U) O := Y.presheaf.algebra_section_stalk y
    let : IsLocalization.AtPrime O p := hU.isLocalization_stalk y
    have hl : ringKrullDim O ≤ ringKrullDim Γ(Y, U) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p O]
      exact p.height_le_ringKrullDim_of_isPrime
    exact hl.trans (affineChart_nagata_and_dimension R A L a ha U hU).2
  exact le_antisymm hO (hdT.symm.le.trans (hTS.trans hSO))

/-- All completed-ring and degree properties are on the literal original stalks
and the accepted canonical completed maps, with no completion-domain premise. -/
theorem singular_branch_completed_properties (hdA : ringKrullDim A = 2)
    (hreg : ∀ z : Y, IsRegularLocalRing (Y.presheaf.stalk z))
    (hbot : ⊥ < L) (htop : L < ⊤)
    (hx : ¬ IsRegularLocalRing ((N).presheaf.stalk (branchPoint π U hU y q))) :
    let T := (N).presheaf.stalk (branchPoint π U hU y q)
    let That := AdicCompletion (maximalIdeal T) T
    let := hreg y.val
    let := (singular_completion_normalDomain R A L a ha hdA
      (branchPoint π U hU y q) hx).1
    IsDomain That ∧ IsIntegrallyClosed That ∧ IsRegularLocalRing Ohat ∧
      ringKrullDim Ohat = 2 ∧ ringKrullDim That = 2 ∧
      Module.Finite Ohat That ∧ Function.Injective (completedStalkMapAt π U hU y q) ∧
      FiniteDimensional (FractionRing Ohat) (FractionRing That) ∧
      Module.finrank (FractionRing Ohat) (FractionRing That) ≤
        Module.finrank L (FractionRing A) ∧
      Module.finrank (FractionRing Ohat) (FractionRing That) <
        Module.finrank (FractionRing R) (FractionRing A) ∧
      Module.finrank (FractionRing R) L <
        Module.finrank (FractionRing R) (FractionRing A) := by
  let T := (N).presheaf.stalk (branchPoint π U hU y q)
  let That := AdicCompletion (maximalIdeal T) T
  let := hreg y.val
  have hn := singular_completion_normalDomain R A L a ha hdA (branchPoint π U hU y q) hx
  let := hn.1
  have hdegree : Module.finrank (FractionRing Ohat) (FractionRing That) ≤
      Module.finrank L (FractionRing A) := by
    let := functionFieldMapAlgebra π
    calc
      _ ≤ Module.finrank Y.functionField (N).functionField :=
        completedFraction_finrank_le π U hU y q
      _ = _ := pi_field_finrank R A L a ha
  exact ⟨hn.1, hn.2, (AdicCompletion.isRegularLocalRing_iff_maximalCompletion O).mp inferInstance,
    (AdicCompletion.ringKrullDim_maximalIdeal_eq O).trans
      (singular_branch_target_dimension R A L a ha U hU y q hx),
    (AdicCompletion.ringKrullDim_maximalIdeal_eq T).trans
      (singular_point_closed_dimension R A L a ha (branchPoint π U hU y q) hx).2,
    completedStalk_finite π U hU y q, completedStalkMapAt_injective π U hU y q,
    completedFraction_finite π U hU y q, hdegree,
    hdegree.trans_lt (remaining_extension_degree_lt R A L hbot),
    intermediate_induction_degree_lt R A L htop⟩

/-- Every finite quotient and both original field/residue squares use the same
accepted completed maps on the same actual branch, not maps chosen afterward. -/
theorem singular_branch_completed_compatibility (hdA : ringKrullDim A = 2)
    (hreg : ∀ z : Y, IsRegularLocalRing (Y.presheaf.stalk z))
    (hx : ¬ IsRegularLocalRing ((N).presheaf.stalk (branchPoint π U hU y q))) :
    let T := (N).presheaf.stalk (branchPoint π U hU y q)
    let That := AdicCompletion (maximalIdeal T) T
    let := hreg y.val
    let := (singular_completion_normalDomain R A L a ha hdA
      (branchPoint π U hU y q) hx).1
    (∀ (n : ℕ) (z : Ohat),
      AdicCompletion.evalₐ (maximalIdeal T) n (completedStalkMapAt π U hU y q z) =
        Ideal.quotientMap (maximalIdeal T ^ n)
          (stalkMapAt π (branchPoint π U hU y q) y.val (branchPoint_map π U hU y q))
          (by
            apply Ideal.map_le_iff_le_comap.mp
            rw [Ideal.map_pow]
            exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) n)
          (AdicCompletion.evalₐ (maximalIdeal O) n z)) ∧
      (∀ z : Ohat,
        completedFractionMapAt π U hU y q (algebraMap Ohat (FractionRing Ohat) z) =
          algebraMap That (FractionRing That) (completedStalkMapAt π U hU y q z)) ∧
      (AdicCompletion.FiniteSemilocal.originalBaseFractionMap T (N).functionField).comp
          (functionFieldMap π) =
        (completedFractionMapAt π U hU y q).comp
          (AdicCompletion.FiniteSemilocal.originalBaseFractionMap O Y.functionField) ∧
      (ResidueField.map (completedStalkMapAt π U hU y q)).comp
          (ResidueField.map (algebraMap O Ohat)) =
        (ResidueField.map (algebraMap T That)).comp
          (ResidueField.map
            (stalkMapAt π (branchPoint π U hU y q) y.val (branchPoint_map π U hU y q))) := by
  let T := (N).presheaf.stalk (branchPoint π U hU y q)
  let That := AdicCompletion (maximalIdeal T) T
  let := hreg y.val
  let := (singular_completion_normalDomain R A L a ha hdA
    (branchPoint π U hU y q) hx).1
  exact ⟨completedStalkMapAt_eval π U hU y q,
    completedFractionMapAt_algebraMap π U hU y q,
    completedFraction_original_field_square π U hU y q,
    completedStalkMapAt_residue_square π U hU y q⟩

/-- Every actual singular point is one of the genuine full-algebra branches,
with the strictly smaller completed degree for its original completed maps. -/
theorem exists_singular_completed_branch (hdA : ringKrullDim A = 2)
    (hreg : ∀ z : Y, IsRegularLocalRing (Y.presheaf.stalk z))
    (hbot : ⊥ < L) (htop : L < ⊤)
    (x : Cover.normalization a ha (baseMap R A L))
    (hx : ¬ IsRegularLocalRing ((N).presheaf.stalk x)) (hxy : π x = y.val) :
    ∃ (q : MaximalSpectrum S) (hqx : branchPoint π U hU y q = x),
      let T := (N).presheaf.stalk (branchPoint π U hU y q)
      let That := AdicCompletion (maximalIdeal T) T
      let hxq : ¬ IsRegularLocalRing T :=
        (congrArg (fun z : N => ¬ IsRegularLocalRing ((N).presheaf.stalk z)) hqx).mpr hx
      let := hreg y.val
      let := (singular_completion_normalDomain R A L a ha hdA
        (branchPoint π U hU y q) hxq).1
      FiniteDimensional (FractionRing Ohat) (FractionRing That) ∧
        Module.finrank (FractionRing Ohat) (FractionRing That) ≤
          Module.finrank L (FractionRing A) ∧
        Module.finrank (FractionRing Ohat) (FractionRing That) <
          Module.finrank (FractionRing R) (FractionRing A) ∧
        Module.finrank (FractionRing R) L <
          Module.finrank (FractionRing R) (FractionRing A) := by
  have hclosed : IsClosed ({x} : Set N) :=
    (singular_point_closed_dimension R A L a ha x hx).1
  have hex : ∃ q : MaximalSpectrum S, branchPoint π U hU y q = x :=
    exists_branch (X := N) (Y := Y) π U hU y x hclosed hxy
  obtain ⟨q, rfl⟩ := hex
  refine ⟨q, rfl, ?_⟩
  let T := (N).presheaf.stalk (branchPoint π U hU y q)
  let That := AdicCompletion (maximalIdeal T) T
  let := hreg y.val
  let := (singular_completion_normalDomain R A L a ha hdA
    (branchPoint π U hU y q) hx).1
  rcases singular_branch_completed_properties R A L a ha U hU y q hdA hreg hbot htop hx with
    ⟨_, _, _, _, _, _, _, hfinite, hle, hlt, hind⟩
  exact ⟨hfinite, hle, hlt, hind⟩

end AlgebraicGeometry.Scheme.IntermediateFieldModel

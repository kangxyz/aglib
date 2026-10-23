/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.LocalCoordinates
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections

/-!
# The original binary-form product morphism

The original local coefficients generate on every original source chart.
Their actual basic opens provide frames normalized by the selected original
coefficient. Native section-frame gluing then constructs the map to the
original `n+1`-coordinate projective space over the original base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The original coefficient-line frame restricted to any smaller original open. -/
def coefficientFrameOn (a : Chart.{u} n) (U : (source R n).Opens)
    (hU : U ≤ sourceOpen R n a) :
    (coefficientCocycle R n).sheaf.over U ≅
      SheafOfModules.unit ((source R n).ringCatSheaf.over U) :=
  (SheafOfModules.fullyFaithfulForget ((source R n).ringCatSheaf.over U)).preimageIso <|
    PresheafOfModules.isoMk
      (fun V => ((coefficientCocycle R n).localSectionsEquiv a
        ((leOfHom V.unop.hom).trans hU)).toModuleIso) (by
          intro V W f
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro s
          exact (coefficientCocycle R n).localSectionsEquiv_restrict a
            (leOfHom f.unop.left) ((leOfHom V.unop.hom).trans hU) s)

/-- Restricting the original frame retains the original polynomial coefficient. -/
theorem coefficientSection_frameOn (a : Chart.{u} n) (U : (source R n).Opens)
    (hU : U ≤ sourceOpen R n a) (V : (source R n).Opens) (hV : V ≤ U)
    (k : ULift.{u} (Fin (n + 1))) :
    chartSectionEquiv (source R n) (coefficientCocycle R n).sheaf U
      (coefficientFrameOn R n a U hU) V hV ((coefficientSection R n k).val (op V)) =
        localCoefficient R n a V (hV.trans hU) k.down := by
  change sectionRestrict (source R n) (le_inf le_rfl (hV.trans hU))
    (localCoefficient R n a (V ⊓ sourceOpen R n a) inf_le_right k.down) = _
  exact localCoefficient_restrict R n a (le_inf le_rfl (hV.trans hU))
    inf_le_right k.down

/-- On each actual source chart, each original normalized factor pair generates one. -/
theorem localRatio_pair_span (a : Chart.{u} n) (V : (source R n).Opens)
    (hV : V ≤ sourceOpen R n a) (i : Fin n) :
    Ideal.span ({localRatio R n a i (ULift.up 0) V hV,
      localRatio R n a i (ULift.up 1) V hV} : Set Γ(source R n, V)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hmem : ∀ j : Fin 2, localRatio R n a i (ULift.up j) V hV ∈
      Ideal.span ({localRatio R n a i (ULift.up 0) V hV,
        localRatio R n a i (ULift.up 1) V hV} : Set Γ(source R n, V)) :=
    Fin.forall_fin_two.mpr ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩
  simpa only [ULift.up_down, localRatio_selected] using hmem (a i).down

/-- The `n+1` actual local coefficients generate the original local section ring. -/
theorem span_localCoefficients_eq_top (a : Chart.{u} n) (V : (source R n).Opens)
    (hV : V ≤ sourceOpen R n a) :
    Ideal.span (Set.range (localCoefficient R n a V hV)) = ⊤ :=
  span_coefficients_eq_top
    (fun i => localRatio R n a i (ULift.up 0) V hV)
    (fun i => localRatio R n a i (ULift.up 1) V hV)
    (fun i => localRatio_pair_span R n a V hV i)

/-- The actual nonvanishing open of the selected original coefficient in a source chart. -/
def refinedOpen (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) : (source R n).Opens :=
  (source R n).basicOpen (localCoefficient R n z.1 (sourceOpen R n z.1) le_rfl z.2.down)

theorem refinedOpen_le (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) :
    refinedOpen R n z ≤ sourceOpen R n z.1 :=
  (source R n).basicOpen_le _

/-- The actual coefficient basic opens cover every original factor-coordinate chart. -/
theorem iSup_refinedOpen_eq_top : (⨆ z, refinedOpen R n z) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ a, sourceOpen R n a by rw [iSup_sourceOpen_eq_top]; trivial)
  have hcov : (⨆ k : Fin (n + 1), (source R n).basicOpen
      (localCoefficient R n a (sourceOpen R n a) le_rfl k)) = sourceOpen R n a := by
    simpa only [iSup_range] using iSup_basicOpen_of_span_eq_top
      (sourceOpen R n a) (Set.range (localCoefficient R n a (sourceOpen R n a) le_rfl))
      (span_localCoefficients_eq_top R n a (sourceOpen R n a) le_rfl)
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hcov.symm ▸ ha)
  exact Opens.mem_iSup.mpr ⟨(a, ULift.up k), hk⟩

/-- The selected coefficient is a unit in its original basic-open section ring. -/
theorem selectedCoefficient_isUnit (z : Chart.{u} n × ULift.{u} (Fin (n + 1))) :
    IsUnit (chartSectionEquiv (source R n) (coefficientCocycle R n).sheaf
      (refinedOpen R n z) (coefficientFrameOn R n z.1 (refinedOpen R n z)
        (refinedOpen_le R n z)) (refinedOpen R n z) le_rfl
          ((coefficientSection R n z.2).val (op (refinedOpen R n z)))) := by
  rw [coefficientSection_frameOn]
  rw [← localCoefficient_restrict R n z.1 (refinedOpen_le R n z) le_rfl z.2.down]
  exact (source R n).toRingedSpace.isUnit_res_basicOpen
    (localCoefficient R n z.1 (sourceOpen R n z.1) le_rfl z.2.down)

/-- Actual frames normalized by the original nonvanishing coefficient, on an
actual cover of the original native product. -/
def sectionFrames : FromSections.SectionFrames (coefficientCocycle R n).sheaf
    (coefficientSection R n) where
  K := Chart.{u} n × ULift.{u} (Fin (n + 1))
  U := refinedOpen R n
  covers := iSup_refinedOpen_eq_top R n
  coordinate := Prod.snd
  frame z := FromSections.normalizedFrame (coefficientCocycle R n).sheaf
    (refinedOpen R n z)
    (coefficientFrameOn R n z.1 (refinedOpen R n z) (refinedOpen_le R n z))
    (coefficientSection R n z.2) (selectedCoefficient_isUnit R n z)
  selected z := FromSections.normalizedFrame_coefficient (coefficientCocycle R n).sheaf
    (refinedOpen R n z)
    (coefficientFrameOn R n z.1 (refinedOpen R n z) (refinedOpen_le R n z))
    (coefficientSection R n z.2) (selectedCoefficient_isUnit R n z)

/-- The actual binary-form product morphism, with the original `n+1` output coefficients. -/
def multiplication : source R n ⟶ target R n :=
  (sectionFrames R n).map (structureMap R n)

/-- The actual multiplication morphism retains the original base structure map. -/
@[reassoc (attr := simp)]
theorem multiplication_over :
    multiplication R n ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) =
      structureMap R n :=
  (sectionFrames R n).map_toSpec (structureMap R n)

/-- The coefficient construction is proper over every commutative base ring. -/
instance multiplication_isProper : IsProper (multiplication R n) := by
  have : IsProper (multiplication R n ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1)))) := by
    rw [multiplication_over]
    infer_instance
  exact IsProper.of_comp (multiplication R n)
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))))

/-- The uniform coefficient construction agrees with the original zero-factor isomorphism. -/
@[simp]
theorem multiplication_zero : multiplication R 0 = zeroMap R := by
  apply (cancel_mono (ProjectiveSpace.toSpec R (ULift.{u} (Fin 1)))).mp
  rw [multiplication_over, zeroMap_over]

instance multiplication_zero_isFinite : IsFinite (multiplication R 0) := by
  rw [multiplication_zero]
  infer_instance

instance multiplication_zero_surjective : Surjective (multiplication R 0) := by
  rw [multiplication_zero]
  infer_instance

/-- On the actual selected coefficient open, the native coordinate ratio is
the original product coefficient divided by the selected original coefficient. -/
theorem multiplication_coordinateRatio
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1)))
    (V : (source R n).Opens) (hV : V ≤ refinedOpen R n z)
    (j : ULift.{u} (Fin (n + 1))) :
    ((multiplication R n).appLE
      (ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin (n + 1))) z.2) V
      ((sectionFrames R n).le_map_preimage_selected (structureMap R n) z hV)).hom
        (ProjectiveSpace.coordinateRatioSection R (ULift.{u} (Fin (n + 1))) z.2 j) =
      localCoefficient R n z.1 V (hV.trans (refinedOpen_le R n z)) j.down *
        sectionRestrict (source R n) hV
          (↑(selectedCoefficient_isUnit R n z).unit⁻¹) := by
  refine ((sectionFrames R n).map_coordinateRatioSection (structureMap R n) z hV j).trans ?_
  change chartSectionEquiv (source R n) (coefficientCocycle R n).sheaf
      (refinedOpen R n z)
      (coefficientFrameOn R n z.1 (refinedOpen R n z) (refinedOpen_le R n z)) V hV
        ((coefficientSection R n j).val (op V)) * _ = _
  rw [coefficientSection_frameOn]
  rfl

/-- The same original coordinate formula without an inverse in the conclusion.
It is preserved directly by every original source section-ring homomorphism. -/
theorem multiplication_coefficient_mul_ratio
    (z : Chart.{u} n × ULift.{u} (Fin (n + 1)))
    (V : (source R n).Opens) (hV : V ≤ refinedOpen R n z)
    (j : ULift.{u} (Fin (n + 1))) :
    localCoefficient R n z.1 V (hV.trans (refinedOpen_le R n z)) z.2.down *
      ratioOn (multiplication R n) z.2 j V
        ((sectionFrames R n).le_map_preimage_selected (structureMap R n) z hV) =
      localCoefficient R n z.1 V (hV.trans (refinedOpen_le R n z)) j.down := by
  let u := (selectedCoefficient_isUnit R n z).unit
  have hu : (u : Γ(source R n, refinedOpen R n z)) =
      localCoefficient R n z.1 (refinedOpen R n z) (refinedOpen_le R n z) z.2.down :=
    (selectedCoefficient_isUnit R n z).unit_spec.trans
      (coefficientSection_frameOn R n z.1 (refinedOpen R n z)
        (refinedOpen_le R n z) (refinedOpen R n z) le_rfl z.2)
  have huv : sectionRestrict (source R n) hV (u : Γ(source R n, refinedOpen R n z)) =
      localCoefficient R n z.1 V (hV.trans (refinedOpen_le R n z)) z.2.down := by
    rw [hu, localCoefficient_restrict]
  have hr : ratioOn (multiplication R n) z.2 j V
      ((sectionFrames R n).le_map_preimage_selected (structureMap R n) z hV) =
        localCoefficient R n z.1 V (hV.trans (refinedOpen_le R n z)) j.down *
          sectionRestrict (source R n) hV (↑(u⁻¹)) :=
    multiplication_coordinateRatio R n z V hV j
  calc
    _ = sectionRestrict (source R n) hV (u : Γ(source R n, refinedOpen R n z)) *
        (localCoefficient R n z.1 V (hV.trans (refinedOpen_le R n z)) j.down *
          sectionRestrict (source R n) hV (↑(u⁻¹))) := congrArg₂ (· * ·) huv.symm hr
    _ = _ := by
      rw [mul_left_comm, ← map_mul, Units.mul_inv, map_one, mul_one]

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

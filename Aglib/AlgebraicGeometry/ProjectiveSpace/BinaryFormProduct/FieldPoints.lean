/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FieldCoordinates
public import Aglib.AlgebraicGeometry.ProjectiveSpace.PulledCoordinates

/-!
# Actual relative field points from their original vectors

The base coefficient map remains explicit. Every actual relative field point
is recovered from its original chart values, and multiplying its full vector
by one nonzero field scalar preserves the same scheme morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field

universe u

variable {R K I : Type u} [CommRing R] [Field K] [Finite I]

/-- The actual relative field point of the original nonzero coordinate vector. -/
def point (β : R →+* K) (v : I → K) (j₀ : I) (hj : v j₀ ≠ 0) :
    Spec (.of K) ⟶ ProjectiveSpace R I :=
  letI := FromSections.FieldSpan.family_epi_of_nonzero v j₀ hj
  FromSections.mapOfFiniteFamily (Spec.map (CommRingCat.ofHom β))
    (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)
    (FromSections.FieldSpan.unit_rankOne (Spec (.of K)))
    (FromSections.FieldSpan.family v)

@[reassoc (attr := simp)]
theorem point_over (β : R →+* K) (v : I → K) (j₀ : I) (hj : v j₀ ≠ 0) :
    point β v j₀ hj ≫ toSpec R I = Spec.map (CommRingCat.ofHom β) := by
  let := FromSections.FieldSpan.family_epi_of_nonzero v j₀ hj
  exact FromSections.mapOfFiniteFamily_toSpec _ _ _ _

/-- Original native chart values recover the same original projective morphism. -/
theorem point_eq_chart_of_values (β : R →+* K) (v : I → K) (j₀ : I)
    (hj : v j₀ ≠ 0) (φ : coordinateRing R I j₀ →+* K)
    (hβ : ∀ r, φ (coordinateRingCoefficient R I j₀ r) = β r)
    (hv : ∀ j, v j = φ (coordinateRatio R I j₀ j)) :
    point β v j₀ hj = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X j₀)
        (MvPolynomial.isHomogeneous_X R j₀) Nat.zero_lt_one :=
  FromSections.FieldSpan.mapOfFiniteFamily_eq_chart_of_values β v j₀ φ hβ hv

/-- Every actual relative field point retains a normalized original vector
with the exact same coefficient map and the exact same scheme morphism. -/
theorem exists_point (β : R →+* K) (g : Spec (.of K) ⟶ ProjectiveSpace R I)
    (hg : g ≫ toSpec R I = Spec.map (CommRingCat.ofHom β)) :
    ∃ (v : I → K) (j₀ : I) (hj : v j₀ ≠ 0), point β v j₀ hj = g := by
  obtain ⟨j₀, φ, hφ⟩ := exists_coordinateChart_factorization g
  let v := chartHomCoordinates j₀ φ
  have hv : v j₀ = 1 := chartHomCoordinates_self j₀ φ
  have hj : v j₀ ≠ 0 := by rw [hv]; exact one_ne_zero
  refine ⟨v, j₀, hj, (point_eq_chart_of_values β v j₀ hj φ ?_ (fun _ => rfl)).trans hφ⟩
  have hβ : CommRingCat.ofHom (coordinateRingCoefficient R I j₀) ≫
      CommRingCat.ofHom φ = CommRingCat.ofHom β := by
    apply Spec.map_injective
    have ht : Proj.awayι (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X j₀)
        (MvPolynomial.isHomogeneous_X R j₀) Nat.zero_lt_one ≫ toSpec R I =
          Spec.map (CommRingCat.ofHom (coordinateRingCoefficient R I j₀)) :=
      coordinateChart_toSpec R I j₀
    rw [Spec.map_comp, ← ht, ← Category.assoc, hφ, hg]
  exact fun r => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hβ) r

/-- A nonzero scalar rescaling preserves the actual original relative point. -/
theorem point_eq_of_scale (β : R →+* K) (v w : I → K)
    (i₀ j₀ : I) (hi : v i₀ ≠ 0) (hj : w j₀ ≠ 0)
    (c : K) (hc : c ≠ 0) (hvw : ∀ j, w j = c * v j) :
    point β v i₀ hi = point β w j₀ hj := by
  let := FromSections.FieldSpan.family_epi_of_nonzero v i₀ hi
  let := FromSections.FieldSpan.family_epi_of_nonzero w j₀ hj
  let e := unitMulIso (Spec (.of K))
    (Units.map (Scheme.ΓSpecIso (.of K)).inv.hom.toMonoidHom (Units.mk0 c hc))
  apply FromSections.mapOfFiniteFamily_iso _ _ _ _ _ _ _ e
  intro j
  change unitMul (Spec (.of K)) ((Scheme.ΓSpecIso (.of K)).inv.hom (v j)) ≫
      unitMul (Spec (.of K)) ((Scheme.ΓSpecIso (.of K)).inv.hom c) =
    unitMul (Spec (.of K)) ((Scheme.ΓSpecIso (.of K)).inv.hom (w j))
  rw [← unitMul_mul, ← map_mul]
  exact congrArg (fun a : K => unitMul (Spec (.of K))
    ((Scheme.ΓSpecIso (.of K)).inv.hom a)) ((mul_comm (v j) c).trans (hvw j).symm)

private theorem restrict_self (U : (Spec (.of K)).Opens) (r : Γ(Spec (.of K), U)) :
    sectionRestrict (Spec (.of K)) (show U ≤ U from le_rfl) r = r := by
  change ((Spec (.of K)).presheaf.map (𝟙 (op U))).hom r = r
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The structure-module frame normalized by the same nonzero coordinate. -/
def vectorFrame (v : I → K) (j₀ : I) (hj : v j₀ ≠ 0) :
    (SheafOfModules.unit (Spec (.of K)).ringCatSheaf).over ⊤ ≅
      SheafOfModules.unit ((Spec (.of K)).ringCatSheaf.over ⊤) :=
  FromSections.unitScaleOnIso ⊤
    (Units.map (Scheme.ΓSpecIso (.of K)).inv.hom.toMonoidHom (Units.mk0 (v j₀) hj))⁻¹

omit [Finite I] in
theorem vectorFrame_coefficient (v : I → K) (j₀ : I) (hj : v j₀ ≠ 0) (j : I) :
    chartSectionEquiv (Spec (.of K)) _ ⊤ (vectorFrame v j₀ hj) ⊤ le_rfl
      (((SheafOfModules.unit (Spec (.of K)).ringCatSheaf).unitHomEquiv
        (FromSections.FieldSpan.family v j)).val (op ⊤)) =
      (Scheme.ΓSpecIso (.of K)).inv.hom (v j * (v j₀)⁻¹) := by
  change (show Γ(Spec (.of K), ⊤) from
    ((SheafOfModules.unit (Spec (.of K)).ringCatSheaf).unitHomEquiv
      (FromSections.FieldSpan.family v j)).val (op ⊤)) *
        sectionRestrict (Spec (.of K)) (show ⊤ ≤ ⊤ from le_rfl) _ = _
  rw [FromSections.FieldSpan.family_section, restrict_self]
  change (Scheme.ΓSpecIso (.of K)).inv.hom (v j) *
    (Scheme.ΓSpecIso (.of K)).inv.hom ((v j₀)⁻¹) = _
  exact ((Scheme.ΓSpecIso (.of K)).inv.hom.map_mul _ _).symm

/-- A single original frame over the whole actual field scheme. -/
def vectorFrames (v : I → K) (j₀ : I) (hj : v j₀ ≠ 0) :
    FromSections.SectionFrames (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)
      (fun j => (SheafOfModules.unit (Spec (.of K)).ringCatSheaf).unitHomEquiv
        (FromSections.FieldSpan.family v j)) where
  K := PUnit.{u + 1}
  U _ := ⊤
  covers := by simp
  coordinate _ := j₀
  frame _ := vectorFrame v j₀ hj
  selected _ := by
    change chartSectionEquiv (Spec (.of K)) _ ⊤ (vectorFrame v j₀ hj) ⊤ le_rfl
      (((SheafOfModules.unit (Spec (.of K)).ringCatSheaf).unitHomEquiv
        (FromSections.FieldSpan.family v j₀)).val (op ⊤)) = 1
    rw [vectorFrame_coefficient, mul_inv_cancel₀ hj, map_one]

theorem point_eq_vectorFrames_map (β : R →+* K) (v : I → K)
    (j₀ : I) (hj : v j₀ ≠ 0) :
    point β v j₀ hj = (vectorFrames v j₀ hj).map (Spec.map (CommRingCat.ofHom β)) := by
  unfold point
  apply FromSections.SectionFrames.map_eq_of_iso _ _ _ (Iso.refl _)
  intro j O
  simp only [FromSections.generatingSectionsOfFamily_section]
  rfl

theorem point_preimage_selected (β : R →+* K) (v : I → K)
    (j₀ : I) (hj : v j₀ ≠ 0) :
    ⊤ ≤ point β v j₀ hj ⁻¹ᵁ coordinateOpen R I j₀ := by
  rw [point_eq_vectorFrames_map]
  exact (vectorFrames v j₀ hj).le_map_preimage_selected
    (Spec.map (CommRingCat.ofHom β)) PUnit.unit le_rfl

/-- The actual pulled coordinate ratio is the original ratio of field coordinates. -/
theorem point_ratio (β : R →+* K) (v : I → K)
    (j₀ : I) (hj : v j₀ ≠ 0) (j : I) :
    ratioOn (point β v j₀ hj) j₀ j ⊤ (point_preimage_selected β v j₀ hj) =
      (Scheme.ΓSpecIso (.of K)).inv.hom (v j * (v j₀)⁻¹) := by
  have h := (vectorFrames v j₀ hj).map_coordinateRatioSection
    (Spec.map (CommRingCat.ofHom β)) PUnit.unit (O := ⊤) le_rfl j
  have he := point_eq_vectorFrames_map β v j₀ hj
  change ratioOn ((vectorFrames v j₀ hj).map (Spec.map (CommRingCat.ofHom β)))
    j₀ j ⊤ _ = _ at h
  simpa only [he] using h.trans (vectorFrame_coefficient v j₀ hj j)

/-- A zero original coordinate has empty original coordinate-chart preimage. -/
theorem point_preimage_zero (β : R →+* K) (v : I → K)
    (j₀ : I) (hj : v j₀ ≠ 0) (j : I) (hz : v j = 0) :
    point β v j₀ hj ⁻¹ᵁ coordinateOpen R I j = ⊥ := by
  have h := basicOpen_ratioOn (point β v j₀ hj) j₀ j ⊤
    (point_preimage_selected β v j₀ hj)
  rw [point_ratio, hz, zero_mul, map_zero, Scheme.basicOpen_zero, top_inf_eq] at h
  exact h.symm

/-- Equality of actual relative projective field points gives one nonzero
scalar relating their full original vectors. -/
theorem exists_scale_of_point_eq (β : R →+* K) (v w : I → K)
    (i₀ j₀ : I) (hi : v i₀ ≠ 0) (hj : w j₀ ≠ 0)
    (he : point β v i₀ hi = point β w j₀ hj) :
    ∃ c : K, c ≠ 0 ∧ ∀ j, w j = c * v j := by
  have hw : w i₀ ≠ 0 := by
    intro hz
    have hm : (default : Spec (.of K)) ∈
        point β v i₀ hi ⁻¹ᵁ coordinateOpen R I i₀ :=
      point_preimage_selected β v i₀ hi trivial
    rw [he, point_preimage_zero β w j₀ hj i₀ hz] at hm
    exact hm
  have hew : point β w i₀ hw = point β w j₀ hj :=
    point_eq_of_scale β w w i₀ j₀ hw hj 1 one_ne_zero (fun _ => (one_mul _).symm)
  have he' : point β v i₀ hi = point β w i₀ hw := he.trans hew.symm
  have hratio (j : I) : v j / v i₀ = w j / w i₀ := by
    have hv := point_ratio β v i₀ hi j
    have hw' := point_ratio β w i₀ hw j
    simp only [he'] at hv
    have h := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.injective
      (hv.symm.trans hw')
    simpa only [div_eq_mul_inv] using h
  refine ⟨w i₀ / v i₀, div_ne_zero hw hi, fun j => ?_⟩
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hi).mpr
    (((div_eq_div_iff hi hw).mp (hratio j)).symm.trans (mul_comm (v j) (w i₀)))

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field

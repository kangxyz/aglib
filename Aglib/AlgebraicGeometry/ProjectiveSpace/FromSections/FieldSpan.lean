/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Closed projective field points from the full original coefficient span

The literal original unit-section family defines the same native projective map.
A chosen nonzero original coefficient normalizes an actual global frame. Full
coefficient span makes its chart-ring map surjective and the structural map
finite. Properness then closes the resulting preimmersion.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan

variable {A κ I : Type u} [CommRing A] [Field κ]

/-- The literal original unit-multiplication family over the field point. -/
def family (a : I → κ) :
    I → (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of κ)).ringCatSheaf) :=
  fun j => unitMul (Spec (.of κ)) ((Scheme.ΓSpecIso (.of κ)).inv.hom (a j))

/-- The actual structure module has rank one, independently of the chosen family. -/
theorem unit_rankOne (Y : Scheme.{u}) :
    IsLocallyRankOne Y (SheafOfModules.unit Y.ringCatSheaf) :=
  isLocallyRankOne_of_iso Y
    (coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit Y.ringCatSheaf))
    (trivialLineBundle Y).property

private theorem restrict_self (Y : Scheme.{u}) (U : Y.Opens) (r : Γ(Y, U)) :
    sectionRestrict Y (show U ≤ U from le_rfl) r = r := by
  change (Y.presheaf.map (𝟙 (op U))).hom r = r
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem family_section (a : I → κ) (j : I) :
    ((SheafOfModules.unit (Spec (.of κ)).ringCatSheaf).unitHomEquiv (family a j)).val
        (op ⊤) = (Scheme.ΓSpecIso (.of κ)).inv.hom (a j) := by
  rw [family, unitMul, Equiv.apply_symm_apply]
  exact restrict_self (Spec (.of κ)) ⊤ _

/-- Any nonzero original coefficient makes the actual original free map epimorphic. -/
theorem family_epi_of_nonzero (a : I → κ) (j : I) (hj : a j ≠ 0) :
    Epi (Sigma.desc (family a)) := by
  let v := Units.map (Scheme.ΓSpecIso (.of κ)).inv.hom.toMonoidHom (Units.mk0 (a j) hj)
  have hs : family a j = (unitMulIso (Spec (.of κ)) v).hom := rfl
  have : IsIso (family a j) := by rw [hs]; infer_instance
  have : Epi (Sigma.ι (fun _ : I => SheafOfModules.unit (Spec (.of κ)).ringCatSheaf) j ≫
      Sigma.desc (family a)) := by
    simpa only [Sigma.ι_comp_desc] using (inferInstance : Epi (family a j))
  exact epi_of_epi (Sigma.ι _ j) (Sigma.desc (family a))

variable (β : A →+* κ)

/-- Full original span supplies a nonzero original coordinate. -/
theorem exists_nonzero (a : I → κ) (ha : letI : Module A κ := Module.compHom κ β
      Submodule.span A (Set.range a) = ⊤) :
    ∃ j, a j ≠ 0 := by
  let : Module A κ := Module.compHom κ β
  by_contra h
  have hz : ∀ j, a j = 0 := by simpa only [not_exists, not_not] using h
  have hle : Submodule.span A (Set.range a) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change a j = 0
    exact hz j
  have hone : (1 : κ) ∈ (⊥ : Submodule A κ) := hle (by rw [ha]; trivial)
  exact one_ne_zero hone

/-- Generation is derived from full span with the same original index and maps. -/
theorem family_epi_of_span (a : I → κ) (ha : letI : Module A κ := Module.compHom κ β
      Submodule.span A (Set.range a) = ⊤) :
    Epi (Sigma.desc (family a)) := by
  let : Module A κ := Module.compHom κ β
  obtain ⟨j, hj⟩ := exists_nonzero β a ha
  exact family_epi_of_nonzero a j hj

/-- The full finite original span makes the original coefficient ring map finite. -/
theorem coefficient_finite [Finite I] (a : I → κ)
    (ha : letI : Module A κ := Module.compHom κ β
      Submodule.span A (Set.range a) = ⊤) : β.Finite := by
  let : Module A κ := Module.compHom κ β
  change @Module.Finite A κ _ _ (Module.compHom κ β)
  apply Module.Finite.of_fg_top
  rw [← ha]
  exact Submodule.fg_span (Set.finite_range a)

/-- A ring-map image containing the base and a unit multiple of the full span is the field. -/
theorem surjective_of_scaled_span {C : Type u} [CommRing C] (φ : C →+* κ)
    (a : I → κ) (ha : letI : Module A κ := Module.compHom κ β
      Submodule.span A (Set.range a) = ⊤) (c : κˣ)
    (hbase : ∀ r : A, ∃ x, φ x = β r)
    (hcoord : ∀ j, ∃ x, φ x = (c : κ) * a j) : Function.Surjective φ := by
  let : Module A κ := Module.compHom κ β
  let N : Submodule A κ := {
    carrier := Set.range φ
    zero_mem' := ⟨0, map_zero φ⟩
    add_mem' := by
      rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      exact ⟨x + y, map_add φ x y⟩
    smul_mem' := by
      intro r y hy
      obtain ⟨x, rfl⟩ := hy
      obtain ⟨z, hz⟩ := hbase r
      refine ⟨z * x, ?_⟩
      change φ (z * x) = β r * φ x
      rw [map_mul, hz] }
  have hscale : ∀ x, x ∈ Submodule.span A (Set.range a) → (c : κ) * x ∈ N := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hcoord j
    | zero => simpa only [mul_zero] using N.zero_mem
    | add x y hx hy hx' hy' => simpa only [mul_add] using N.add_mem hx' hy'
    | smul r x hx hx' =>
      have h := N.smul_mem r hx'
      change β r * ((c : κ) * x) ∈ N at h
      change (c : κ) * (β r * x) ∈ N
      simpa only [mul_left_comm] using h
  intro y
  have h := hscale ((↑(c⁻¹) : κ) * y) (by rw [ha]; trivial)
  change y ∈ N
  simpa only [← mul_assoc, Units.mul_inv, one_mul] using h

private def fieldFrame (a : I → κ) (j₀ : I) (hj : a j₀ ≠ 0) :
    (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf).over ⊤ ≅
      SheafOfModules.unit ((Spec (.of κ)).ringCatSheaf.over ⊤) :=
  unitScaleOnIso ⊤
    (Units.map (Scheme.ΓSpecIso (.of κ)).inv.hom.toMonoidHom (Units.mk0 (a j₀) hj))⁻¹

private theorem fieldFrame_coefficient (a : I → κ) (j₀ : I) (hj : a j₀ ≠ 0) (j : I) :
    chartSectionEquiv (Spec (.of κ)) _ ⊤ (fieldFrame a j₀ hj) ⊤ le_rfl
        (((SheafOfModules.unit (Spec (.of κ)).ringCatSheaf).unitHomEquiv (family a j)).val
          (op ⊤)) =
      (Scheme.ΓSpecIso (.of κ)).inv.hom (a j * (a j₀)⁻¹) := by
  change (show Γ(Spec (.of κ), ⊤) from
    ((SheafOfModules.unit (Spec (.of κ)).ringCatSheaf).unitHomEquiv
      (family a j)).val (op ⊤)) *
        sectionRestrict (Spec (.of κ)) (show ⊤ ≤ ⊤ from le_rfl) _ = _
  rw [family_section, restrict_self]
  change (Scheme.ΓSpecIso (.of κ)).inv.hom (a j) *
    (Scheme.ΓSpecIso (.of κ)).inv.hom ((a j₀)⁻¹) = _
  exact ((Scheme.ΓSpecIso (.of κ)).inv.hom.map_mul _ _).symm

private def oneFrame (a : I → κ) (j₀ : I) (hj : a j₀ ≠ 0) :
    SectionFrames (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf)
      (fun j => (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf).unitHomEquiv (family a j)) where
  K := PUnit.{u + 1}
  U _ := ⊤
  covers := by simp
  coordinate _ := j₀
  frame _ := fieldFrame a j₀ hj
  selected _ := by
    change chartSectionEquiv (Spec (.of κ)) _ ⊤ (fieldFrame a j₀ hj) ⊤ le_rfl
      (((SheafOfModules.unit (Spec (.of κ)).ringCatSheaf).unitHomEquiv (family a j₀)).val
        (op ⊤)) = 1
    rw [fieldFrame_coefficient, mul_inv_cancel₀ hj, map_one]

private def chartHom (a : I → κ) (j₀ : I) (hj : a j₀ ≠ 0) :
    coordinateRing A I j₀ →+* κ :=
  (Scheme.ΓSpecIso (.of κ)).hom.hom.comp
    ((oneFrame a j₀ hj).chartRingHom (Spec.map (CommRingCat.ofHom β)) PUnit.unit le_rfl)

private theorem chartHom_coefficient (a : I → κ) (j₀ : I) (hj : a j₀ ≠ 0) (r : A) :
    chartHom β a j₀ hj (coordinateRingCoefficient A I j₀ r) = β r := by
  change (Scheme.ΓSpecIso (.of κ)).hom.hom
    ((oneFrame a j₀ hj).chartRingHom (Spec.map (CommRingCat.ofHom β)) PUnit.unit le_rfl
      (coordinateRingCoefficient A I j₀ r)) = _
  have hc := congrArg (Scheme.ΓSpecIso (.of κ)).hom.hom
    ((oneFrame a j₀ hj).chartRingHom_coefficient
      (Spec.map (CommRingCat.ofHom β)) PUnit.unit le_rfl r)
  refine hc.trans ?_
  change (Scheme.ΓSpecIso (.of κ)).hom.hom
    (sectionRestrict (Spec (.of κ)) (show ⊤ ≤ ⊤ from le_top)
      ((Spec.map (CommRingCat.ofHom β)).appTop.hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom r))) = _
  rw [restrict_self]
  change (((Scheme.ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom β)).appTop) ≫
    (Scheme.ΓSpecIso (.of κ)).hom).hom r = β r
  rw [Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem chartHom_ratio (a : I → κ) (j₀ : I) (hj : a j₀ ≠ 0) (j : I) :
    chartHom β a j₀ hj (coordinateRatio A I j₀ j) = a j * (a j₀)⁻¹ := by
  change (Scheme.ΓSpecIso (.of κ)).hom.hom
    ((oneFrame a j₀ hj).chartRingHom (Spec.map (CommRingCat.ofHom β)) PUnit.unit le_rfl
      (coordinateRatio A I j₀ j)) = _
  have hc := congrArg (Scheme.ΓSpecIso (.of κ)).hom.hom
    ((oneFrame a j₀ hj).chartRingHom_ratio
      (Spec.map (CommRingCat.ofHom β)) PUnit.unit le_rfl j)
  refine hc.trans ?_
  have hf := fieldFrame_coefficient a j₀ hj j
  exact (congrArg (Scheme.ΓSpecIso (.of κ)).hom.hom hf).trans
    ((Scheme.ΓSpecIso (.of κ)).commRingCatIsoToRingEquiv.apply_symm_apply _)

private theorem chartRingHom_surjective (a : I → κ)
    (ha : letI : Module A κ := Module.compHom κ β
      Submodule.span A (Set.range a) = ⊤) (j₀ : I) (hj : a j₀ ≠ 0) :
    Function.Surjective ((oneFrame a j₀ hj).chartRingHom
      (Spec.map (CommRingCat.ofHom β)) PUnit.unit le_rfl) := by
  let : Module A κ := Module.compHom κ β
  have hφ : Function.Surjective (chartHom β a j₀ hj) :=
    surjective_of_scaled_span β (chartHom β a j₀ hj) a ha (Units.mk0 (a j₀) hj)⁻¹
      (fun r => ⟨coordinateRingCoefficient A I j₀ r, chartHom_coefficient β a j₀ hj r⟩)
      (fun j => ⟨coordinateRatio A I j₀ j, (chartHom_ratio β a j₀ hj j).trans (mul_comm _ _)⟩)
  intro y
  obtain ⟨x, hx⟩ := hφ ((Scheme.ΓSpecIso (.of κ)).hom.hom y)
  exact ⟨x, (Scheme.ΓSpecIso (.of κ)).commRingCatIsoToRingEquiv.injective hx⟩

/-- The literal native projective point of the original full-span family is closed. -/
theorem isClosedImmersion_mapOfFiniteFamily [Finite I] (a : I → κ)
    (ha : letI : Module A κ := Module.compHom κ β
      Submodule.span A (Set.range a) = ⊤) [Epi (Sigma.desc (family a))] :
    IsClosedImmersion (mapOfFiniteFamily (Spec.map (CommRingCat.ofHom β))
      (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf)
      (unit_rankOne (Spec (.of κ))) (family a)) := by
  let : Module A κ := Module.compHom κ β
  let p := Spec.map (CommRingCat.ofHom β)
  let M := SheafOfModules.unit (Spec (.of κ)).ringCatSheaf
  let q := mapOfFiniteFamily p M (unit_rankOne (Spec (.of κ))) (family a)
  obtain ⟨j₀, hj⟩ := exists_nonzero β a ha
  let F := oneFrame a j₀ hj
  have hq : q = F.map p := by
    apply SectionFrames.map_eq_of_iso _ F p (Iso.refl M)
    intro j O
    simp only [generatingSectionsOfFamily_section]
    rfl
  have hpre : IsPreimmersion q := by
    rw [hq]
    have hchart : IsPreimmersion (F.chartMap p PUnit.unit le_rfl) := by
      let : IsClosedImmersion (Spec.map (CommRingCat.ofHom
          (F.chartRingHom p PUnit.unit le_rfl))) :=
        IsClosedImmersion.spec_of_surjective _ (chartRingHom_surjective β a ha j₀ hj)
      have : IsIso (F.U PUnit.unit).toSpecΓ := by
        change IsIso (isAffineOpen_top (Spec (.of κ))).isoSpec.hom
        infer_instance
      dsimp only [SectionFrames.chartMap]
      infer_instance
    have ht : IsPreimmersion ((⊤ : (Spec (.of κ)).Opens).ι ≫ F.map p) :=
      (congrArg (fun h => IsPreimmersion h) (F.ι_map p PUnit.unit)).mpr hchart
    let : IsIso (⊤ : (Spec (.of κ)).Opens).ι := by
      change IsIso (Spec (.of κ)).topIso.hom
      infer_instance
    have hh : IsPreimmersion (inv (⊤ : (Spec (.of κ)).Opens).ι ≫
        ((⊤ : (Spec (.of κ)).Opens).ι ≫ F.map p)) := by infer_instance
    simpa only [IsIso.inv_hom_id_assoc] using hh
  let : IsPreimmersion q := hpre
  let : IsFinite p := (IsFinite.SpecMap_iff (CommRingCat.ofHom β)).mpr
    (coefficient_finite β a ha)
  have : IsProper (q ≫ toSpec A I) := by
    rw [show q ≫ toSpec A I = p from mapOfFiniteFamily_toSpec p M _ (family a)]
    infer_instance
  let : IsProper q := IsProper.of_comp q (toSpec A I)
  exact IsClosedImmersion.of_isPreimmersion q (by
    simpa only [Set.image_univ] using q.isClosedMap Set.univ isClosed_univ)

/-- Full span alone derives generation and closes the same literal original projective map. -/
theorem isClosedImmersion_of_span [Finite I] (a : I → κ)
    (ha : letI : Module A κ := Module.compHom κ β
      Submodule.span A (Set.range a) = ⊤) :
    letI := family_epi_of_span β a ha
    IsClosedImmersion (mapOfFiniteFamily (Spec.map (CommRingCat.ofHom β))
      (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf)
      (unit_rankOne (Spec (.of κ))) (family a)) := by
  let : Module A κ := Module.compHom κ β
  let := family_epi_of_span β a ha
  exact isClosedImmersion_mapOfFiniteFamily β a ha

end AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan

variable {A κ I : Type u} [CommRing A] [Field κ] (β : A →+* κ)

private theorem chartHom_eq_of_ratios (a : I → κ) (i₀ : I) (hi₀ : a i₀ ≠ 0)
    (φ : coordinateRing A I i₀ →+* κ)
    (hβ : ∀ r, φ (coordinateRingCoefficient A I i₀ r) = β r)
    (hratio : ∀ j, φ (coordinateRatio A I i₀ j) = a j * (a i₀)⁻¹) :
    chartHom β a i₀ hi₀ = φ := by
  have h : (chartHom β a i₀ hi₀).comp (polynomialToCoordinateRing A I i₀) =
      φ.comp (polynomialToCoordinateRing A I i₀) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, polynomialToCoordinateRing_C] using
        (chartHom_coefficient β a i₀ hi₀ r).trans (hβ r).symm
    · intro j
      simpa only [RingHom.comp_apply, polynomialToCoordinateRing_X] using
        (chartHom_ratio β a i₀ hi₀ j.1).trans (hratio j.1).symm
  have h' := congrArg (fun g => g.comp (coordinateRingToPolynomial A I i₀)) h
  simpa only [RingHom.comp_assoc, polynomialToCoordinateRing_comp_coordinateRingToPolynomial,
    RingHom.comp_id] using h'

/-- The same original field-point family has the supplied native chart map
when its actual ratios agree. Generation comes from the original nonzero coordinate. -/
theorem mapOfFiniteFamily_eq_chart_of_ratios [Finite I]
    (a : I → κ) (i₀ : I) (hi₀ : a i₀ ≠ 0) (φ : coordinateRing A I i₀ →+* κ)
    (hβ : ∀ r, φ (coordinateRingCoefficient A I i₀ r) = β r)
    (hratio : ∀ j, φ (coordinateRatio A I i₀ j) = a j * (a i₀)⁻¹) :
    letI := family_epi_of_nonzero a i₀ hi₀
    mapOfFiniteFamily (Spec.map (CommRingCat.ofHom β))
        (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf)
        (unit_rankOne (Spec (.of κ))) (family a) =
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule I A) (MvPolynomial.X i₀)
          (MvPolynomial.isHomogeneous_X A i₀) Nat.zero_lt_one := by
  let := family_epi_of_nonzero a i₀ hi₀
  let p := Spec.map (CommRingCat.ofHom β)
  let M := SheafOfModules.unit (Spec (.of κ)).ringCatSheaf
  let q := mapOfFiniteFamily p M (unit_rankOne (Spec (.of κ))) (family a)
  let F := oneFrame a i₀ hi₀
  let ιP := Proj.awayι (MvPolynomial.homogeneousSubmodule I A) (MvPolynomial.X i₀)
    (MvPolynomial.isHomogeneous_X A i₀) Nat.zero_lt_one
  have hq : q = F.map p := by
    apply SectionFrames.map_eq_of_iso _ F p (Iso.refl M)
    intro j O
    simp only [generatingSectionsOfFamily_section]
    rfl
  have hκ := chartHom_eq_of_ratios β a i₀ hi₀ φ hβ hratio
  have hΓ : F.chartRingHom p PUnit.unit le_rfl =
      (Scheme.ΓSpecIso (.of κ)).inv.hom.comp φ := by
    ext z
    apply (Scheme.ΓSpecIso (.of κ)).commRingCatIsoToRingEquiv.injective
    change chartHom β a i₀ hi₀ z =
      (Scheme.ΓSpecIso (.of κ)).hom.hom ((Scheme.ΓSpecIso (.of κ)).inv.hom (φ z))
    exact (RingHom.congr_fun hκ z).trans
      ((Scheme.ΓSpecIso (.of κ)).commRingCatIsoToRingEquiv.apply_symm_apply _).symm
  let : IsIso (⊤ : (Spec (.of κ)).Opens).ι := by
    change IsIso (Spec (.of κ)).topIso.hom
    infer_instance
  change q = Spec.map (CommRingCat.ofHom φ) ≫ ιP
  apply (cancel_epi (⊤ : (Spec (.of κ)).Opens).ι).mp
  calc
    _ = F.chartMap p PUnit.unit le_rfl :=
      (congrArg (fun g => (⊤ : (Spec (.of κ)).Opens).ι ≫ g) hq).trans
        (F.ι_map p PUnit.unit)
    _ = (⊤ : (Spec (.of κ)).Opens).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of κ)).inv.hom.comp φ)) ≫ ιP := by
      change (⊤ : (Spec (.of κ)).Opens).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (F.chartRingHom p PUnit.unit le_rfl)) ≫ ιP = _
      rw [hΓ]
    _ = _ := by
      change (⊤ : (Spec (.of κ)).Opens).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of κ)).inv) ≫ ιP = _
      rw [Spec.map_comp, Scheme.Opens.toSpecΓ_top]
      simp only [Category.assoc]
      rw [toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]

private theorem chart_values_selected (a : I → κ) (i₀ : I)
    (φ : coordinateRing A I i₀ →+* κ)
    (ha : ∀ j, a j = φ (coordinateRatio A I i₀ j)) : a i₀ = 1 := by
  rw [ha i₀, coordinateRatio_self, map_one]

/-- Original values of a native chart homomorphism define exactly its native
projective map. The selected original coordinate is one and supplies generation. -/
theorem mapOfFiniteFamily_eq_chart_of_values [Finite I]
    (a : I → κ) (i₀ : I) (φ : coordinateRing A I i₀ →+* κ)
    (hβ : ∀ r, φ (coordinateRingCoefficient A I i₀ r) = β r)
    (ha : ∀ j, a j = φ (coordinateRatio A I i₀ j)) :
    letI := family_epi_of_nonzero a i₀ (by
      rw [ha i₀, coordinateRatio_self, map_one]
      exact one_ne_zero)
    mapOfFiniteFamily (Spec.map (CommRingCat.ofHom β))
        (SheafOfModules.unit (Spec (.of κ)).ringCatSheaf)
        (unit_rankOne (Spec (.of κ))) (family a) =
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule I A) (MvPolynomial.X i₀)
          (MvPolynomial.isHomogeneous_X A i₀) Nat.zero_lt_one := by
  have hi₀ : a i₀ ≠ 0 := by
    rw [chart_values_selected a i₀ φ ha]
    exact one_ne_zero
  let := family_epi_of_nonzero a i₀ hi₀
  apply mapOfFiniteFamily_eq_chart_of_ratios β a i₀ hi₀ φ hβ
  intro j
  rw [chart_values_selected a i₀ φ ha, inv_one, mul_one]
  exact (ha j).symm

end AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan

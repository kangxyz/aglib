/-
Copyright (c) 2026 R5Lab contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.PrincipalChain
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteEmbedding.Map

/-!
# Actual projective pencils from principal-section chains

A lift of the distinguished quotient section gives two generating sections of
the original line module. Their original local coefficients define a morphism
to native two-coordinate polynomial projective space, over the original base.
The first coordinate open has precisely the supplied open `W` as its preimage.
No affineness of `W`, field hypothesis, or projectivity premise is used.
-/




@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.PrincipalPencil

/-- Two projective coordinates in the original base-ring universe. -/
abbrev Index := ULift.{u} (Fin 2)

/-- The first index in the universe-lifted two-coordinate projective index type. -/
def first : Index.{u} := ⟨0⟩
/-- The second index in the universe-lifted two-coordinate projective index type. -/
def second : Index.{u} := ⟨1⟩

@[simp] theorem first_ne_second : (first : Index.{u}) ≠ second := by decide
@[simp] theorem second_ne_first : (second : Index.{u}) ≠ first := by decide

theorem index_cases (i : Index.{u}) : i = first ∨ i = second := by
  rcases i with ⟨⟨i, hi⟩⟩
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of R))

/-- The original structural coefficients, restricted to an actual source open. -/
def baseCoefficient (O : X.Opens) : R →+* Γ(X, O) :=
  (sectionRestrict X le_top).comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)

@[simp]
theorem baseCoefficient_restrict {O S : X.Opens} (h : S ≤ O) (r : R) :
    sectionRestrict X h (baseCoefficient p O r) = baseCoefficient p S r := by
  simp only [baseCoefficient, RingHom.comp_apply, sectionRestrict_comp]

/-- Evaluation in a native standard P1 chart, with its one nonconstant ratio. -/
def chartRingHom (O : X.Opens) (i : Index.{u}) (v : Γ(X, O)) :
    coordinateRing R Index.{u} i →+* Γ(X, O) :=
  (eval₂Hom (baseCoefficient p O) (fun _ => v)).comp
    (coordinateRingToPolynomial R Index.{u} i)

@[simp]
theorem chartRingHom_coefficient (O : X.Opens) (i : Index.{u}) (v : Γ(X, O)) (r : R) :
    chartRingHom p O i v (coordinateRingCoefficient R Index.{u} i r) =
      baseCoefficient p O r := by
  simp [chartRingHom]

theorem chartRingHom_ratio (O : X.Opens) (i j : Index.{u}) (v : Γ(X, O)) :
    chartRingHom p O i v (coordinateRatio R Index.{u} i j) = if j = i then 1 else v := by
  classical
  by_cases hji : j = i
  · subst j
    simp
  · change (eval₂Hom (baseCoefficient p O) (fun _ => v))
      (coordinateRingToPolynomial R Index.{u} i
        (coordinateRatio R Index.{u} i (⟨j, hji⟩ : {j : Index.{u} // j ≠ i}).1)) = _
    rw [coordinateRingToPolynomial_ratio, eval₂Hom_X', ite_eq_right hji]

theorem chartRingHom_restrict {O S : X.Opens} (h : S ≤ O) (i : Index.{u}) (v : Γ(X, O)) :
    (sectionRestrict X h).comp (chartRingHom p O i v) =
      chartRingHom p S i (sectionRestrict X h v) := by
  unfold chartRingHom
  rw [← RingHom.comp_assoc]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    simp

/-- An actual morphism from an arbitrary source open into a native projective chart. -/
def chartMap (O : X.Opens) (i : Index.{u}) (v : Γ(X, O)) :
    O.toScheme ⟶ ProjectiveSpace R Index.{u} :=
  O.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartRingHom p O i v)) ≫
    Proj.awayι (homogeneousSubmodule Index.{u} R) (MvPolynomial.X i) (isHomogeneous_X R i)
      Nat.zero_lt_one

theorem chartMap_restrict {O S : X.Opens} (h : S ≤ O) (i : Index.{u}) (v : Γ(X, O)) :
    X.homOfLE h ≫ chartMap p O i v = chartMap p S i (sectionRestrict X h v) := by
  rw [chartMap]
  simp only [← Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc]
  change S.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom ((sectionRestrict X h).comp (chartRingHom p O i v))) ≫ _ = _
  rw [chartRingHom_restrict]
  rfl

theorem chartMap_toSpec (O : X.Opens) (i : Index.{u}) (v : Γ(X, O)) :
    chartMap p O i v ≫ toSpec R Index.{u} = O.ι ≫ p := by
  have hc : CommRingCat.ofHom (coordinateRingCoefficient R Index.{u} i) ≫
      CommRingCat.ofHom (chartRingHom p O i v) = CommRingCat.ofHom (baseCoefficient p O) := by
    ext r
    exact chartRingHom_coefficient p O i v r
  rw [chartMap, Category.assoc, Category.assoc, coordinateChart_toSpec, ← Spec.map_comp]
  change O.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom (coordinateRingCoefficient R Index.{u} i) ≫
      CommRingCat.ofHom (chartRingHom p O i v)) = _
  rw [hc]
  change O.toSpecΓ ≫ Spec.map
    (((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) ≫ X.presheaf.map (homOfLE le_top).op) = _
  rw [Spec.map_comp, Spec.map_comp]
  simp only [← Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top O]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc p, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem chartMap_preimage (O : X.Opens) (i j : Index.{u}) (v : Γ(X, O)) :
    chartMap p O i v ⁻¹ᵁ coordinateOpen R Index.{u} j =
      O.ι ⁻¹ᵁ X.basicOpen (if j = i then 1 else v) := by
  rw [chartMap, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    coordinateChart_preimage_coordinateOpen, SpecMap_preimage_basicOpen]
  change O.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen
    (chartRingHom p O i v (coordinateRatio R Index.{u} i j)) = _
  rw [chartRingHom_ratio, Scheme.Opens.toSpecΓ_preimage_basicOpen]

variable (C : PrincipalChain X)

/-- The original local coefficient of an actual global line-module section. -/
def coefficientOn (m : ℕ) (τ : Γ(C.line m, ⊤)) (i :
  AlgebraicGeometry.Scheme.Modules.Invertible.PrincipalChain.Index.{u})
    {O : X.Opens} (hi : O ≤ C.cover i) : Γ(X, O) :=
  C.coefficients m i hi ((C.line m).val.map (homOfLE le_top).op τ)

theorem coefficientOn_restrict (m : ℕ) (τ : Γ(C.line m, ⊤)) (i :
  AlgebraicGeometry.Scheme.Modules.Invertible.PrincipalChain.Index.{u})
    {O S : X.Opens} (h : S ≤ O) (hi : O ≤ C.cover i) :
    sectionRestrict X h (coefficientOn C m τ i hi) =
      coefficientOn C m τ i (h.trans hi) := by
  change sectionRestrict X h (sectionRestrict X (le_inf le_rfl hi)
      (sectionRestrict X (inf_le_inf le_top le_rfl) (τ.val i))) =
    sectionRestrict X (le_inf le_rfl (h.trans hi))
      (sectionRestrict X (inf_le_inf le_top le_rfl) (τ.val i))
  simp only [sectionRestrict_comp]

theorem coefficientOn_transition (m : ℕ) (τ : Γ(C.line m, ⊤))
    {O : X.Opens} (hU : O ≤ C.U) (hW : O ≤ C.W) :
    coefficientOn C m τ ⟨true⟩ hU =
      sectionRestrict X hU C.f ^ m * coefficientOn C m τ ⟨false⟩ hW := by
  have hu : ((C.cocycle.transitionOn ⟨true⟩ ⟨false⟩ hU hW) : Γ(X, O)) =
      sectionRestrict X hU C.f := by
    change sectionRestrict X (le_inf hU hW) (C.overlapUnit : Γ(X, C.U ⊓ C.W)) = _
    rw [C.overlapUnit_val, sectionRestrict_comp]
  have h := (C.cocycle.zpow (m : ℤ)).localSectionsEquiv_transition
    ⟨true⟩ ⟨false⟩ hU hW ((C.line m).val.map (homOfLE le_top).op τ)
  change coefficientOn C m τ ⟨true⟩ hU =
    ((C.cocycle.zpow (m : ℤ)).transitionOn ⟨true⟩ ⟨false⟩ hU hW : Γ(X, O)) *
      coefficientOn C m τ ⟨false⟩ hW at h
  rw [UnitCocycle.zpow_transitionOn, zpow_natCast, Units.val_pow_eq_pow_val, hu] at h
  exact h

variable (n : ℕ) (τ : Γ(C.line (n + 1), ⊤))

/-- The original `U`-frame coefficient of the lifted section. -/
def coefficientU : Γ(X, C.U) := coefficientOn C (n + 1) τ ⟨true⟩ le_rfl

/-- The second affine chart of the source pencil: where the lifted section is a frame. -/
def secondOpen : X.Opens := X.basicOpen (coefficientU C n τ)

theorem secondOpen_le : secondOpen C n τ ≤ C.U := X.basicOpen_le _

/-- The original `U` coefficient becomes an actual unit on its nonvanishing open. -/
def coefficientUnit : (Γ(X, secondOpen C n τ))ˣ :=
  (show IsUnit (sectionRestrict X (secondOpen_le C n τ) (coefficientU C n τ)) from
    X.toRingedSpace.isUnit_res_basicOpen (coefficientU C n τ)).unit

@[simp]
theorem coefficientUnit_val : (coefficientUnit C n τ : Γ(X, secondOpen C n τ)) =
    sectionRestrict X (secondOpen_le C n τ) (coefficientU C n τ) :=
  IsUnit.unit_spec _

/-- On `W`, the actual power section has coefficient one, so this is `τ / σ^(n+1)`. -/
def firstFunction : Γ(X, C.W) := coefficientOn C (n + 1) τ ⟨false⟩ le_rfl

/-- On the second source open, normalize the actual power section by the lifted section. -/
def secondFunction : Γ(X, secondOpen C n τ) :=
  coefficientOn C (n + 1) (C.powerSection (n + 1)) ⟨true⟩ (secondOpen_le C n τ) *
    ((coefficientUnit C n τ)⁻¹).val

theorem secondFunction_eq : secondFunction C n τ =
    sectionRestrict X (secondOpen_le C n τ) C.f ^ (n + 1) *
      ((coefficientUnit C n τ)⁻¹).val := by
  unfold secondFunction coefficientOn
  rw [C.powerSection_U]

/-- The actual line transition identifies the two affine coordinates as reciprocals. -/
theorem functions_reciprocal {O : X.Opens} (hW : O ≤ C.W) (hV : O ≤ secondOpen C n τ) :
    sectionRestrict X hW (firstFunction C n τ) *
      sectionRestrict X hV (secondFunction C n τ) = 1 := by
  have ht : sectionRestrict X (hV.trans (secondOpen_le C n τ)) (coefficientU C n τ) =
      sectionRestrict X (hV.trans (secondOpen_le C n τ)) C.f ^ (n + 1) *
        sectionRestrict X hW (firstFunction C n τ) := by
    unfold coefficientU firstFunction
    rw [coefficientOn_restrict, coefficientOn_restrict]
    exact coefficientOn_transition C (n + 1) τ _ _
  have ha : sectionRestrict X (hV.trans (secondOpen_le C n τ)) (coefficientU C n τ) *
      sectionRestrict X hV ((coefficientUnit C n τ)⁻¹).val = 1 := by
    have h := congrArg (sectionRestrict X hV) (Units.mul_inv (coefficientUnit C n τ))
    simpa only [map_mul, map_one, coefficientUnit_val, sectionRestrict_comp] using h
  rw [secondFunction_eq, map_mul, map_pow, sectionRestrict_comp]
  calc
    _ = (sectionRestrict X (hV.trans (secondOpen_le C n τ)) C.f ^ (n + 1) *
        sectionRestrict X hW (firstFunction C n τ)) *
          sectionRestrict X hV ((coefficientUnit C n τ)⁻¹).val := by ring
    _ = _ := by rw [← ht]; exact ha

/-- A quotient lift yields a genuine two-open source cover. -/
theorem covers (hprincipal : C.U ⊓ C.W = X.basicOpen C.f)
    (hτ : (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n) :
    C.W ⊔ secondOpen C n τ = ⊤ := by
  obtain ⟨b, hb⟩ := C.coefficients_lift_U n τ hτ
  change coefficientU C n τ = 1 + C.f * b at hb
  have hone : (1 : Γ(X, C.U)) = coefficientU C n τ + C.f * (-b) := by rw [hb]; ring
  have hU : C.U ≤ secondOpen C n τ ⊔ X.basicOpen C.f := by
    calc
      C.U = X.basicOpen (1 : Γ(X, C.U)) := X.basicOpen_one.symm
      _ = X.basicOpen (coefficientU C n τ + C.f * (-b)) := congrArg X.basicOpen hone
      _ ≤ secondOpen C n τ ⊔ X.basicOpen (C.f * (-b)) := X.basicOpen_add_le _ _
      _ ≤ secondOpen C n τ ⊔ X.basicOpen C.f := sup_le_sup_left
        (by rw [X.basicOpen_mul]; exact inf_le_left) _
  apply le_antisymm le_top
  rw [← C.covers]
  refine sup_le ?_ le_sup_left
  apply hU.trans
  refine sup_le le_sup_right ?_
  rw [← hprincipal]
  exact inf_le_right.trans le_sup_left

/-- The second source coordinate vanishes precisely along the supplied principal boundary. -/
theorem basicOpen_secondFunction (hprincipal : C.U ⊓ C.W = X.basicOpen C.f) :
    X.basicOpen (secondFunction C n τ) = secondOpen C n τ ⊓ C.W := by
  rw [secondFunction_eq, X.basicOpen_mul, X.basicOpen_pow _ (Nat.succ_pos n),
    X.basicOpen_of_isUnit (Units.isUnit _), Scheme.basicOpen_res]
  rw [← hprincipal]
  have hV := secondOpen_le C n τ
  rw [← inf_assoc, inf_eq_left.mpr hV]
  exact le_antisymm inf_le_left (le_inf le_rfl inf_le_left)

/-- The two actual maps to native P1 agree on every common source subopen. -/
theorem chartMaps_agree {O : X.Opens} (hW : O ≤ C.W) (hV : O ≤ secondOpen C n τ) :
    X.homOfLE hW ≫ chartMap p C.W first (firstFunction C n τ) =
      X.homOfLE hV ≫ chartMap p (secondOpen C n τ) second (secondFunction C n τ) := by
  rw [chartMap_restrict, chartMap_restrict]
  unfold chartMap
  apply congrArg (fun q => O.toSpecΓ ≫ q)
  apply FiniteEmbedding.chart_maps_eq_of_rescaling
  · intro r
    rw [chartRingHom_coefficient, chartRingHom_coefficient]
  · rw [chartRingHom_ratio, ite_eq_right second_ne_first]
    exact isUnit_iff_exists_inv.mpr
      ⟨sectionRestrict X hV (secondFunction C n τ), functions_reciprocal C n τ hW hV⟩
  · intro k
    rcases index_cases k with rfl | rfl
    · simpa [chartRingHom_ratio] using (functions_reciprocal C n τ hW hV).symm
    · simp [chartRingHom_ratio]

/-- The two actual source opens on which the pencil is written in affine coordinates. -/
abbrev sourceOpen : Bool → X.Opens
  | true => C.W
  | false => secondOpen C n τ

theorem iSup_sourceOpen_eq_top (hprincipal : C.U ⊓ C.W = X.basicOpen C.f)
    (hτ : (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n) :
    iSup (sourceOpen C n τ) = ⊤ := by
  apply le_antisymm le_top
  rw [← covers C n τ hprincipal hτ]
  exact sup_le (le_iSup (sourceOpen C n τ) true) (le_iSup (sourceOpen C n τ) false)

/-- The two-open source cover determined by a lift of the principal-chain quotient section,
under the overlap and lifting hypotheses. -/
abbrev sourceOpenCover (hprincipal : C.U ⊓ C.W = X.basicOpen C.f)
    (hτ : (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n) : X.OpenCover :=
  X.openCoverOfIsOpenCover (sourceOpen C n τ) (.mk (iSup_sourceOpen_eq_top C n τ hprincipal hτ))

/-- The local projective-space map on each of the two opens, using the corresponding
coefficients of the principal pencil. -/
def localMap : (i : Bool) → (sourceOpen C n τ i).toScheme ⟶ ProjectiveSpace R Index.{u}
  | true => chartMap p C.W first (firstFunction C n τ)
  | false => chartMap p (secondOpen C n τ) second (secondFunction C n τ)

theorem localMap_compatible (i j : Bool) :
    CategoryTheory.Limits.pullback.fst (sourceOpen C n τ i).ι (sourceOpen C n τ j).ι ≫
        localMap p C n τ i =
      CategoryTheory.Limits.pullback.snd (sourceOpen C n τ i).ι (sourceOpen C n τ j).ι ≫
        localMap p C n τ j := by
  let h := isPullback_opens_inf (sourceOpen C n τ i) (sourceOpen C n τ j)
  apply (cancel_epi h.isoPullback.hom).mp
  simp only [← Category.assoc]
  rw [h.isoPullback_hom_fst, h.isoPullback_hom_snd]
  cases i <;> cases j
  · rfl
  · exact (chartMaps_agree p C n τ inf_le_right inf_le_left).symm
  · exact chartMaps_agree p C n τ inf_le_left inf_le_right
  · rfl

/-- The actual projective-line morphism defined by the original power section and
the original lift of the distinguished quotient section. -/
def map (hprincipal : C.U ⊓ C.W = X.basicOpen C.f)
    (hτ : (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n) :
    X ⟶ ProjectiveSpace R Index.{u} :=
  (sourceOpenCover C n τ hprincipal hτ).glueMorphisms
    (localMap p C n τ) (localMap_compatible p C n τ)

@[reassoc (attr := simp)]
theorem ι_map (hprincipal : C.U ⊓ C.W = X.basicOpen C.f)
    (hτ : (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n) (i : Bool) :
    (sourceOpen C n τ i).ι ≫ map p C n τ hprincipal hτ = localMap p C n τ i :=
  (sourceOpenCover C n τ hprincipal hτ).ι_glueMorphisms _ _ i

theorem localMap_preimage_first (hprincipal : C.U ⊓ C.W = X.basicOpen C.f) (i : Bool) :
    localMap p C n τ i ⁻¹ᵁ coordinateOpen R Index.{u} first =
      (sourceOpen C n τ i).ι ⁻¹ᵁ C.W := by
  cases i
  · rw [localMap, chartMap_preimage, ite_eq_right first_ne_second,
      basicOpen_secondFunction C n τ hprincipal]
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
  · rw [localMap, chartMap_preimage, ite_eq_left rfl, X.basicOpen_one]

/-- The first target coordinate is nonvanishing exactly on the original open `W`. -/
theorem map_preimage_first (hprincipal : C.U ⊓ C.W = X.basicOpen C.f)
    (hτ : (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n) :
    map p C n τ hprincipal hτ ⁻¹ᵁ coordinateOpen R Index.{u} first = C.W := by
  ext x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ iSup (sourceOpen C n τ) by rw [iSup_sourceOpen_eq_top C n τ hprincipal hτ]; trivial)
  have h := congrArg
    (fun O : (sourceOpen C n τ i).toScheme.Opens => (⟨x, hi⟩ : sourceOpen C n τ i) ∈ O)
    ((congrArg (fun q => q ⁻¹ᵁ coordinateOpen R Index.{u} first)
      (ι_map p C n τ hprincipal hτ i)).trans (localMap_preimage_first p C n τ hprincipal i))
  exact eq_iff_iff.mp h

/-- The actual pencil morphism commutes with the original structural morphism. -/
@[reassoc]
theorem map_toSpec (hprincipal : C.U ⊓ C.W = X.basicOpen C.f)
    (hτ : (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n) :
    map p C n τ hprincipal hτ ≫ toSpec R Index.{u} = p := by
  apply (sourceOpenCover C n τ hprincipal hτ).hom_ext
  intro i
  change (sourceOpen C n τ i).ι ≫ map p C n τ hprincipal hτ ≫ toSpec R Index.{u} =
    (sourceOpen C n τ i).ι ≫ p
  rw [ι_map_assoc]
  cases i <;> exact chartMap_toSpec _ _ _ _

/-- A literal lift in the actual principal chain supplies an actual over-base P1 morphism. -/
theorem exists_map (hprincipal : C.U ⊓ C.W = X.basicOpen C.f)
    (hτ : (C.quotientMap n).val.app (op ⊤) τ = C.quotientSection n) :
    ∃ φ : X ⟶ ProjectiveSpace R Index.{u},
      φ ≫ toSpec R Index.{u} = p ∧ φ ⁻¹ᵁ coordinateOpen R Index.{u} first = C.W :=
  ⟨map p C n τ hprincipal hτ, map_toSpec p C n τ hprincipal hτ,
    map_preimage_first p C n τ hprincipal hτ⟩

end AlgebraicGeometry.ProjectiveSpace.PrincipalPencil

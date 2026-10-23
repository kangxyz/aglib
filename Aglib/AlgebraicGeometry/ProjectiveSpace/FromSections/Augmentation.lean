/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOneEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.AffineChart
public import Aglib.RingTheory.GradedAlgebra.HomogeneousLocalization.DegreeOne
public import Mathlib.Tactic.Ring

/-!
# Linear augmentation of the original projective coordinates

A finitely supported coefficient family adds its original linear combination
as one extra homogeneous coordinate. The original degree-one embedding theorem
supplies the actual closed immersion. Composition with a degree-one presentation
retains its augmented original generators. On an affine unit-module family whose
specified linear combination is one, the resulting map is the original standard
affine-chart map of the same family.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

variable {R ι : Type u} [CommRing R] (u : ι →₀ R)

/-- The original finitely supported linear combination of homogeneous coordinates. -/
def linearForm : MvPolynomial ι R :=
  Finsupp.linearCombination R (fun i : ι => X i) u

theorem linearForm_mem : linearForm u ∈ homogeneousSubmodule ι R 1 := by
  rw [homogeneousSubmodule_one_eq_span_X, ← Finsupp.range_linearCombination]
  exact ⟨u, rfl⟩

/-- Add the specified linear form while keeping every original coordinate. -/
def family : Option ι → MvPolynomial ι R :=
  fun i => i.elim (linearForm u) (fun j => X j)

theorem family_span :
    Submodule.span R (Set.range (family u)) = homogeneousSubmodule ι R 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    cases i with
    | none => exact linearForm_mem u
    | some i => exact isHomogeneous_X R i
  · rw [homogeneousSubmodule_one_eq_span_X, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨some i, rfl⟩

/-- The original graded polynomial substitution for coordinate augmentation. -/
def presentation : homogeneousSubmodule (Option ι) R →+*ᵍ homogeneousSubmodule ι R :=
  Proj.DegreeOneEmbedding.presentation (homogeneousSubmodule ι R) (family u)
    (family_span u) (homogeneousSubmodule_one_pow R)

/-- The original augmentation presentation satisfies the native irrelevant-ideal condition. -/
theorem irrelevant_le_map : HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R) ≤
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Option ι) R)).map (presentation u) :=
  Proj.DegreeOneEmbedding.irrelevant_le_map (homogeneousSubmodule ι R) (family u)
    (family_span u) (homogeneousSubmodule_one_pow R)

/-- The actual original degree-one closed embedding defined by the augmented coordinates. -/
def embedding : ProjectiveSpace R ι ⟶ ProjectiveSpace R (Option ι) :=
  Proj.DegreeOneEmbedding.embedding (homogeneousSubmodule ι R) (family u)
    (family_span u) (homogeneousSubmodule_one_pow R)

instance embedding_isClosedImmersion : IsClosedImmersion (embedding u) :=
  Proj.DegreeOneEmbedding.embedding_isClosedImmersion _ _ _ _

@[reassoc]
theorem embedding_toSpec :
    embedding u ≫ ProjectiveSpace.toSpec R (Option ι) = ProjectiveSpace.toSpec R ι := by
  have h0 : algebraMap R (homogeneousSubmodule ι R 0) =
      toHomogeneousSubmoduleZero R ι := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    rfl
  simpa only [embedding, Proj.DegreeOneEmbedding.structureMap, ProjectiveSpace.toSpec, h0]
    using Proj.DegreeOneEmbedding.embedding_toSpec (homogeneousSubmodule ι R)
      (family u) (family_span u) (homogeneousSubmodule_one_pow R)

theorem presentation_C (r : R) : presentation u (C r) = C r := by
  exact (MvPolynomial.aeval (family u)).commutes r

theorem presentation_X_none : presentation u (X none) = linearForm u := by
  change MvPolynomial.aeval (family u) (X none) = _
  rw [aeval_X]
  rfl

theorem presentation_X_some (i : ι) : presentation u (X (some i)) = X i := by
  change MvPolynomial.aeval (family u) (X (some i)) = _
  rw [aeval_X]
  rfl

private theorem presentation_mem {n : ℕ} {p : MvPolynomial (Option ι) R}
    (hp : p ∈ homogeneousSubmodule (Option ι) R n) :
    presentation u p ∈ homogeneousSubmodule ι R n := by
  change (presentation u).toRingHom p ∈ homogeneousSubmodule ι R n
  exact (presentation u).map_mem hp

/-- The original homogeneous-localization map on the chart of a retained coordinate. -/
def chartMap (i : ι) : ProjectiveSpace.coordinateRing R (Option ι) (some i) →+*
    ProjectiveSpace.coordinateRing R ι i :=
  HomogeneousLocalization.map (presentation u) <| by
    rintro _ ⟨n, rfl⟩
    change presentation u (X (some i) ^ n) ∈ Submonoid.powers (X i)
    rw [map_pow, presentation_X_some]
    exact ⟨n, rfl⟩

theorem chartMap_mk (i : ι) (n : ℕ) (p : MvPolynomial (Option ι) R)
    (hp : p ∈ homogeneousSubmodule (Option ι) R n) :
    chartMap u i
        (Away.mk (homogeneousSubmodule (Option ι) R) (isHomogeneous_X R (some i))
          n p (by simpa only [smul_eq_mul, mul_one] using hp)) =
      Away.mk (homogeneousSubmodule ι R) (isHomogeneous_X R i) n (presentation u p)
        (by simpa only [smul_eq_mul, mul_one] using presentation_mem u hp) := by
  apply HomogeneousLocalization.val_injective
  change (Localization.mk (presentation u p) ⟨presentation u (X (some i) ^ n), _⟩ :
      Localization (Submonoid.powers (X i))) =
    Localization.mk (presentation u p) ⟨X i ^ n, _⟩
  simp only [map_pow, presentation_X_some]

theorem chartMap_coefficient (i : ι) (r : R) :
    chartMap u i (ProjectiveSpace.coordinateRingCoefficient R (Option ι) (some i) r) =
      ProjectiveSpace.coordinateRingCoefficient R ι i r := by
  apply HomogeneousLocalization.val_injective
  change (Localization.mk (presentation u (MvPolynomial.C r)) ⟨presentation u 1, _⟩ :
      Localization (Submonoid.powers (X i))) = Localization.mk (MvPolynomial.C r) ⟨1, _⟩
  simp only [presentation_C, map_one]

theorem chartMap_ratio_some (i j : ι) :
    chartMap u i (ProjectiveSpace.coordinateRatio R (Option ι) (some i) (some j)) =
      ProjectiveSpace.coordinateRatio R ι i j := by
  rw [ProjectiveSpace.coordinateRatio, chartMap_mk u i 1 (X (some j))
    (isHomogeneous_X R (some j))]
  simp only [presentation_X_some, ProjectiveSpace.coordinateRatio]

theorem dehomogenize_linearForm (i : ι) :
    Away.dehomogenize (homogeneousSubmodule ι R) (isHomogeneous_X R i) (linearForm u) =
      u.sum (fun j r => ProjectiveSpace.coordinateRingCoefficient R ι i r *
        ProjectiveSpace.coordinateRatio R ι i j) := by
  let d := Away.dehomogenize (homogeneousSubmodule ι R) (isHomogeneous_X R i)
  have hc (r : R) : d (MvPolynomial.C r) =
      ProjectiveSpace.coordinateRingCoefficient R ι i r :=
    Away.dehomogenize_fromZero (homogeneousSubmodule ι R) (isHomogeneous_X R i)
      (toHomogeneousSubmoduleZero R ι r)
  have hx (j : ι) : d (X j) = ProjectiveSpace.coordinateRatio R ι i j :=
    Away.dehomogenize_homogeneous (homogeneousSubmodule ι R) (isHomogeneous_X R i)
      (X j) (isHomogeneous_X R j)
  change d (Finsupp.linearCombination R (fun j : ι => X j) u) = _
  rw [Finsupp.linearCombination_apply, map_finsuppSum]
  apply Finset.sum_congr rfl
  intro j hj
  change d (u j • X j) =
    ProjectiveSpace.coordinateRingCoefficient R ι i (u j) *
      ProjectiveSpace.coordinateRatio R ι i j
  rw [Algebra.smul_def, map_mul]
  exact congrArg₂ (· * ·) (hc (u j)) (hx j)

theorem chartMap_ratio_none (i : ι) :
    chartMap u i (ProjectiveSpace.coordinateRatio R (Option ι) (some i) none) =
      u.sum (fun j r => ProjectiveSpace.coordinateRingCoefficient R ι i r *
        ProjectiveSpace.coordinateRatio R ι i j) := by
  rw [ProjectiveSpace.coordinateRatio, chartMap_mk u i 1 (X none)
    (isHomogeneous_X R none)]
  simpa only [presentation_X_none] using
    (Away.dehomogenize_homogeneous (homogeneousSubmodule ι R)
    (isHomogeneous_X R i) (linearForm u) (linearForm_mem u)).symm.trans
      (dehomogenize_linearForm u i)

theorem awayι_comp_embedding (i : ι) :
    Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i) Nat.zero_lt_one ≫
      embedding u =
    Spec.map (CommRingCat.ofHom (chartMap u i)) ≫
      Proj.awayι (homogeneousSubmodule (Option ι) R) (X (some i))
        (isHomogeneous_X R (some i)) Nat.zero_lt_one := by
  have H (x : MvPolynomial ι R) (hx : x = presentation u (X (some i)))
      (hd : x ∈ homogeneousSubmodule ι R 1) :
      Proj.awayι (homogeneousSubmodule ι R) x hd Nat.zero_lt_one ≫
          Proj.map (presentation u) (irrelevant_le_map u) =
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.map (presentation u)
            (P := Submonoid.powers (X (some i))) (Q := Submonoid.powers x)
            (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [hx]⟩))) ≫
          Proj.awayι (homogeneousSubmodule (Option ι) R) (X (some i))
            (isHomogeneous_X R (some i)) Nat.zero_lt_one := by
    subst x
    exact Proj.awayι_comp_map (presentation u) (irrelevant_le_map u)
      Nat.zero_lt_one (X (some i)) (isHomogeneous_X R (some i))
  change Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i)
      Nat.zero_lt_one ≫ Proj.map (presentation u) (irrelevant_le_map u) = _
  simpa only [chartMap] using H (X i) (presentation_X_some u i).symm (isHomogeneous_X R i)

variable {C : Type u} [CommRing C] [Algebra R C]
  (G : ℕ → Submodule R C) [GradedAlgebra G] (g : ι → C)
  (hg : Submodule.span R (Set.range g) = G 1)
  (hpow : ∀ n : ℕ, (G 1) ^ n = G n)

omit [GradedAlgebra G] in
theorem eval_linearForm :
    Proj.DegreeOneEmbedding.presentation G g hg hpow (linearForm u) =
      Finsupp.linearCombination R g u := by
  change (MvPolynomial.aeval g).toLinearMap
      (Finsupp.linearCombination R (fun i : ι => X i) u) = _
  rw [Finsupp.apply_linearCombination]
  apply congrArg (fun v : ι → C => Finsupp.linearCombination R v u)
  funext i
  exact aeval_X g i

/-- The same original degree-one generators with their prescribed combination adjoined. -/
def augmentedFamily : Option ι → C :=
  fun i => i.elim (Finsupp.linearCombination R g u) g

omit [GradedAlgebra G] in
theorem augmentedFamily_span (hgen : Submodule.span R (Set.range g) = G 1) :
    Submodule.span R (Set.range (augmentedFamily u g)) = G 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    cases i with
    | none =>
      change Finsupp.linearCombination R g u ∈ G 1
      rw [← hgen, ← Finsupp.range_linearCombination]
      exact ⟨u, rfl⟩
    | some i =>
      change g i ∈ G 1
      rw [← hgen]
      exact Submodule.subset_span ⟨i, rfl⟩
  · rw [← hgen, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨some i, rfl⟩

omit [GradedAlgebra G] in
/-- Actual generator evaluation commutes with the original augmentation substitution. -/
theorem presentation_comp :
    (Proj.DegreeOneEmbedding.presentation G g hg hpow).comp (presentation u) =
      Proj.DegreeOneEmbedding.presentation G (augmentedFamily u g)
        (augmentedFamily_span u G g hg) hpow := by
  have hRing :
      ((Proj.DegreeOneEmbedding.presentation G g hg hpow).comp (presentation u)).toRingHom =
        (Proj.DegreeOneEmbedding.presentation G (augmentedFamily u g)
          (augmentedFamily_span u G g hg) hpow).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change Proj.DegreeOneEmbedding.presentation G g hg hpow
        (presentation u (MvPolynomial.C r)) = _
      rw [presentation_C]
      exact ((MvPolynomial.aeval g).commutes r).trans
        ((MvPolynomial.aeval (augmentedFamily u g)).commutes r).symm
    · intro i
      cases i with
      | none =>
        change Proj.DegreeOneEmbedding.presentation G g hg hpow
            (presentation u (X none)) =
          MvPolynomial.aeval (augmentedFamily u g) (X none)
        rw [presentation_X_none, eval_linearForm, aeval_X]
        rfl
      | some i =>
        change Proj.DegreeOneEmbedding.presentation G g hg hpow
            (presentation u (X (some i))) =
          MvPolynomial.aeval (augmentedFamily u g) (X (some i))
        rw [presentation_X_some]
        change MvPolynomial.aeval g (X i) =
          MvPolynomial.aeval (augmentedFamily u g) (X (some i))
        rw [aeval_X, aeval_X]
        rfl
  apply GradedRingHom.ext
  intro p
  exact RingHom.congr_fun hRing p

/-- Composing the actual degree-one embedding gives the embedding of its augmented family. -/
theorem embedding_comp :
    Proj.DegreeOneEmbedding.embedding G g hg hpow ≫ embedding u =
      Proj.DegreeOneEmbedding.embedding G (augmentedFamily u g)
        (augmentedFamily_span u G g hg) hpow := by
  change Proj.map (Proj.DegreeOneEmbedding.presentation G g hg hpow)
      (Proj.DegreeOneEmbedding.irrelevant_le_map G g hg hpow) ≫
        Proj.map (presentation u)
          (irrelevant_le_map u) =
    Proj.map (Proj.DegreeOneEmbedding.presentation G (augmentedFamily u g)
      (augmentedFamily_span u G g hg) hpow)
        (Proj.DegreeOneEmbedding.irrelevant_le_map G (augmentedFamily u g)
          (augmentedFamily_span u G g hg) hpow)
  simpa only [presentation_comp] using
    (Proj.map_comp (presentation u) (Proj.DegreeOneEmbedding.presentation G g hg hpow)
      (irrelevant_le_map u) (Proj.DegreeOneEmbedding.irrelevant_le_map G g hg hpow)).symm

end AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

open AlgebraicGeometry.ProjectiveSpace

variable {R T ι : Type u} [CommRing R] [CommRing T]

private theorem augmented_chart_eq_none (u : ι →₀ R) (i : ι)
    (β : R →+* T) (c : ι → T)
    (hcomb : u.sum (fun j r => β r * c j) = 1)
    (φ : coordinateRing R ι i →+* T)
    (hβ : ∀ r, φ (coordinateRingCoefficient R ι i r) = β r)
    (z : T) (hc : ∀ j, φ (coordinateRatio R ι i j) = z * c j) :
    Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i)
          Nat.zero_lt_one ≫ embedding u =
      ProjectiveSpace.FromSections.AffineChart.map β c := by
  have hnone : (φ.comp (chartMap u i))
      (coordinateRatio R (Option ι) (some i) none) = z := by
    rw [RingHom.comp_apply, chartMap_ratio_none, map_finsuppSum]
    calc
      _ = u.sum (fun j r => β r * (z * c j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        change φ (coordinateRingCoefficient R ι i (u j) * coordinateRatio R ι i j) =
          β (u j) * (z * c j)
        rw [map_mul, hβ, hc]
      _ = z * u.sum (fun j r => β r * c j) := by
        simp only [Finsupp.sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = z := by rw [hcomb, mul_one]
  have hz : IsUnit z := by
    have hi : 1 = z * c i := by
      simpa only [coordinateRatio_self, map_one] using hc i
    exact isUnit_iff_exists_inv.mpr ⟨c i, hi.symm⟩
  rw [awayι_comp_embedding, ← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom (φ.comp (chartMap u i))) ≫
      Proj.awayι (homogeneousSubmodule (Option ι) R) (X (some i))
        (isHomogeneous_X R (some i)) Nat.zero_lt_one =
    Spec.map (CommRingCat.ofHom (FromSections.AffineChart.ringHom β c)) ≫
      Proj.awayι (homogeneousSubmodule (Option ι) R) (X none)
        (isHomogeneous_X R none) Nat.zero_lt_one
  apply FiniteEmbedding.chart_maps_eq_of_rescaling (some i) none
  · intro r
    rw [RingHom.comp_apply, chartMap_coefficient, hβ,
      FromSections.AffineChart.ringHom_coefficient]
  · rw [hnone]
    exact hz
  · intro j
    cases j with
    | none => rw [coordinateRatio_self, map_one, mul_one]
    | some j =>
      rw [RingHom.comp_apply, chartMap_ratio_some, hc, hnone,
        FromSections.AffineChart.ringHom_ratio]
      rfl

end AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

namespace AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

open Opposite AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace.FromSections

private def originalGeneratingSections {Z : Scheme.{u}} {I : Type u} (M : Z.Modules)
    (s : I → (SheafOfModules.unit Z.ringCatSheaf ⟶ M))
    (hs : Epi (CategoryTheory.Limits.Sigma.desc s)) : M.GeneratingSections :=
  @generatingSectionsOfFamily I Z M s hs

private theorem originalGeneratingSections_section {Z : Scheme.{u}} {I : Type u}
    (M : Z.Modules) (s : I → (SheafOfModules.unit Z.ringCatSheaf ⟶ M))
    (hs : Epi (CategoryTheory.Limits.Sigma.desc s)) (j : I) :
    (originalGeneratingSections M s hs).s j = M.unitHomEquiv (s j) :=
  @generatingSectionsOfFamily_section I Z M s hs j

private theorem originalGeneratingSections_isFiniteType {Z : Scheme.{u}} {I : Type u}
    [Finite I] (M : Z.Modules) (s : I → (SheafOfModules.unit Z.ringCatSheaf ⟶ M))
    (hs : Epi (CategoryTheory.Limits.Sigma.desc s)) :
    (originalGeneratingSections M s hs).IsFiniteType :=
  @generatingSectionsOfFamily_isFiniteType I Z M inferInstance s hs

private def unitSectionValue (Z : Scheme.{u}) (U : Z.Opens) :
    let V : ModuleCat.{u} Γ(Z, U) :=
      (SheafOfModules.unit Z.ringCatSheaf).val.obj (op U)
    Γ(Z, U) →ₗ[Γ(Z, U)] V := by
  change Γ(Z, U) →ₗ[Γ(Z, U)] Γ(Z, U)
  exact LinearMap.id

private theorem ringLinearMap_apply (A : Type u) [CommRing A]
    (l : A →ₗ[A] A) (a : A) : l a = l 1 * a := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using l.map_smul a (1 : A)

variable {R T ι : Type u} [CommRing R] [CommRing T]

/-- The original affine structure module, with its scheme-module carrier explicit. -/
abbrev unitModule (T : Type u) [CommRing T] : (Spec (.of T)).Modules :=
  SheafOfModules.unit (Spec (.of T)).ringCatSheaf

/-- The unchanged original affine unit-module section family. -/
def plainFamily (c : ι → T) (j : ι) :
    SheafOfModules.unit (Spec (.of T)).ringCatSheaf ⟶ unitModule T :=
  unitMul (Spec (.of T)) ((Scheme.ΓSpecIso (.of T)).inv (c j))

private def affineRestriction (U : (Spec (.of T)).Opens) :
    CommRingCat.of T ⟶ Γ(Spec (.of T), U) :=
  (Scheme.ΓSpecIso (.of T)).inv ≫
    (Spec (.of T)).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op

private theorem plainFamily_value (c : ι → T) (U : (Spec (.of T)).Opens) (j : ι) :
    ((unitModule T).unitHomEquiv
      (plainFamily c j)).val (op U) =
        unitSectionValue (Spec (.of T)) U (affineRestriction U (c j)) := by
  rw [plainFamily, unitMul, Equiv.apply_symm_apply]
  rfl

private theorem frame_coefficients (c : ι → T)
    [hepi : Epi
      (CategoryTheory.Limits.Sigma.desc (C := (Spec (.of T)).Modules) (plainFamily c))]
    (F : SectionFrames (unitModule T)
      (originalGeneratingSections (unitModule T) (plainFamily c) hepi).s) (k : F.K) :
    ∃ z : Γ(Spec (.of T), F.U k), ∀ j : ι,
      F.coefficientOn k le_rfl j = z * affineRestriction (F.U k) (c j) := by
  let M : (Spec (.of T)).Modules := unitModule T
  let e : Γ(M, F.U k) ≃ₗ[Γ(Spec (.of T), F.U k)] Γ(Spec (.of T), F.U k) :=
    LocalFrames.coefficient F.U M F.frame k le_rfl
  let A : CommRingCat := Γ(Spec (.of T), F.U k)
  let l : A →ₗ[A] A := e.toLinearMap.comp (unitSectionValue (Spec (.of T)) (F.U k))
  refine ⟨l 1, fun j => ?_⟩
  change e (((originalGeneratingSections (unitModule T) (plainFamily c) hepi).s j).val
    (op (F.U k))) =
    l 1 * affineRestriction (F.U k) (c j)
  have hvalue : ((originalGeneratingSections (unitModule T) (plainFamily c) hepi).s j).val
      (op (F.U k)) =
      unitSectionValue (Spec (.of T)) (F.U k) (affineRestriction (F.U k) (c j)) := by
    have hs := originalGeneratingSections_section (unitModule T) (plainFamily c) hepi j
    have hv := congrArg (fun t : (unitModule T).sections => t.val (op (F.U k))) hs
    exact hv.trans (plainFamily_value c (F.U k) j)
  exact (congrArg e hvalue).trans (ringLinearMap_apply A l (affineRestriction (F.U k) (c j)))

private theorem baseCoefficient_affine (β : R →+* T) (U : (Spec (.of T)).Opens) (r : R) :
    SectionFrames.baseCoefficient (Spec.map (CommRingCat.ofHom β)) U r =
      affineRestriction U (β r) := by
  change (sectionRestrict (Spec (.of T)) le_top)
      ((Spec.map (CommRingCat.ofHom β)).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
    (sectionRestrict (Spec (.of T)) le_top) ((Scheme.ΓSpecIso (.of T)).inv (β r))
  exact congrArg (sectionRestrict (Spec (.of T)) le_top)
    (congrArg (fun q : CommRingCat.of R ⟶ Γ(Spec (.of T), ⊤) => q r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)).symm)

private theorem affineRestriction_triangle (U : (Spec (.of T)).Opens) :
    U.toSpecΓ ≫ Spec.map (affineRestriction U) = U.ι := by
  change U.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of T)).inv ≫
    (Spec (.of T)).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) = _
  rw [Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private theorem affineChart_map_comp_spec {A : Type u} [CommRing A]
    (β : R →+* T) (b : T →+* A) (c : ι → T) :
    Spec.map (CommRingCat.ofHom b) ≫ AffineChart.map β c =
      AffineChart.map (b.comp β) (b ∘ c) := by
  have h : b.comp (MvPolynomial.eval₂Hom β c) =
      MvPolynomial.eval₂Hom (b.comp β) (b ∘ c) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, eval₂Hom_C]
    · intro j
      simp only [RingHom.comp_apply, eval₂Hom_X', Function.comp_apply]
  have hr : b.comp (AffineChart.ringHom β c) =
      AffineChart.ringHom (b.comp β) (b ∘ c) := by
    apply RingHom.ext
    intro p
    exact RingHom.congr_fun h (optionCoordinateRingEquivPolynomial R ι p)
  have hcat : CommRingCat.ofHom (AffineChart.ringHom β c) ≫ CommRingCat.ofHom b =
      CommRingCat.ofHom (AffineChart.ringHom (b.comp β) (b ∘ c)) := by
    apply CommRingCat.hom_ext
    exact hr
  unfold AffineChart.map
  rw [← Spec.map_comp_assoc, hcat]

/-- Augmenting the original finite unit-module family by its specified linear
combination equal to one gives its actual standard affine-chart morphism. -/
theorem plainFamily_map_augmentation [Finite ι]
    (u : ι →₀ R) (β : R →+* T) (c : ι → T)
    [hepi : Epi
      (CategoryTheory.Limits.Sigma.desc (C := (Spec (.of T)).Modules) (plainFamily c))]
    (hunit : IsLocallyRankOne (Spec (.of T))
      (unitModule T))
    (hcomb : u.sum (fun j r => β r * c j) = 1) :
    @mapOfFiniteFamily R _ ι (Spec (.of T)) (Spec.map (CommRingCat.ofHom β))
        (unitModule T) hunit inferInstance (plainFamily c) hepi ≫
      embedding u = AffineChart.map β c := by
  let M : (Spec (.of T)).Modules := unitModule T
  let σ := originalGeneratingSections M (plainFamily c) hepi
  let : σ.IsFiniteType := originalGeneratingSections_isFiniteType M (plainFamily c) hepi
  let F := framesOfGeneratingSections M hunit σ
  change F.map (Spec.map (CommRingCat.ofHom β)) ≫ embedding u = AffineChart.map β c
  apply F.sourceOpenCover.hom_ext
  intro k
  change F.K at k
  change (F.U k).ι ≫ F.map (Spec.map (CommRingCat.ofHom β)) ≫ embedding u =
    (F.U k).ι ≫ AffineChart.map β c
  rw [F.ι_map_assoc]
  obtain ⟨z, hz⟩ := frame_coefficients (hepi := hepi) c F k
  let A : CommRingCat := Γ(Spec (.of T), F.U k)
  let b : T →+* A := (affineRestriction (F.U k)).hom
  have hc : u.sum (fun j r => (b.comp β) r * (b ∘ c) j) = 1 := by
    have h := congrArg b hcomb
    simpa only [map_finsuppSum, map_mul, map_one, RingHom.comp_apply,
      Function.comp_apply] using h
  have hβ (r : R) :
      F.chartRingHom (Spec.map (CommRingCat.ofHom β)) k le_rfl
        (coordinateRingCoefficient R ι (F.coordinate k) r) = (b.comp β) r :=
    (F.chartRingHom_coefficient (Spec.map (CommRingCat.ofHom β)) k le_rfl r).trans
      (baseCoefficient_affine β (F.U k) r)
  have hx (j : ι) :
      F.chartRingHom (Spec.map (CommRingCat.ofHom β)) k le_rfl
        (coordinateRatio R ι (F.coordinate k) j) = z * (b ∘ c) j :=
    (F.chartRingHom_ratio (Spec.map (CommRingCat.ofHom β)) k le_rfl j).trans (hz j)
  have hh := augmented_chart_eq_none u (F.coordinate k) (b.comp β) (b ∘ c) hc
    (F.chartRingHom (Spec.map (CommRingCat.ofHom β)) k le_rfl) hβ z hx
  unfold SectionFrames.chartMap
  simp only [Category.assoc]
  refine (congrArg (fun q => (F.U k).toSpecΓ ≫ q) hh).trans ?_
  rw [← affineChart_map_comp_spec β b c, ← Category.assoc]
  change ((F.U k).toSpecΓ ≫ Spec.map (affineRestriction (F.U k))) ≫ AffineChart.map β c = _
  rw [affineRestriction_triangle]

end AlgebraicGeometry.ProjectiveSpace.FromSections.Augmentation

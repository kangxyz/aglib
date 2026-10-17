/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.LocalCriterion
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Sections
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Global functions after every base change over a local Noetherian ring

Let `R` be a local Noetherian ring with residue field `k`, and let
`f : X ⟶ Spec R` be proper and flat with geometrically integral closed fibre.
The constants theorem makes the original degree-zero residue comparison of the
structure module surjective. The proper local criterion then makes
`H⁰(X, O_X)` free with invertible base-change maps after every ring map; its
residue tensor is one-dimensional, so the structure map `R → Γ(X, ⊤)` is
bijective by Nakayama. Consequently, for every ring map `σ : R →+* B` and every
supplied cartesian square over `Spec.map σ`, the structure map of the new
scheme to `Spec B` is bijective on global functions (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Ex. 3.11, p. 25, in the geometrically integral
case).

Only the closed fibre is assumed geometrically integral. Finite presentation is
not a hypothesis. The target rings need be neither Noetherian nor flat.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

/-- Over a local ring, a finite flat module with a one-dimensional residue tensor spanned
by `m` is free of rank one on `m`. -/
theorem IsLocalRing.bijective_smul_of_bijective_residueField_tmul {R : Type*} [CommRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Flat R M] (m : M)
    (h : Function.Bijective (fun c : IsLocalRing.ResidueField R => c ⊗ₜ[R] m)) :
    Function.Bijective (fun r : R => r • m) := by
  let k := IsLocalRing.ResidueField R
  let v : Unit → M := fun _ => m
  have hk : Function.Bijective
      (Finsupp.linearCombination k (TensorProduct.mk R k M 1 ∘ v)) := by
    have e : (Finsupp.linearCombination k (TensorProduct.mk R k M 1 ∘ v) :
        (Unit →₀ k) → k ⊗[R] M) =
          (fun c : k => c ⊗ₜ[R] m) ∘ (Finsupp.uniqueLinearEquiv (R := k) (M := k) ()) := by
      funext l
      rw [Function.comp_apply, Finsupp.linearCombination_unique,
        Finsupp.uniqueLinearEquiv_apply]
      change l () • ((1 : k) ⊗ₜ[R] m) = l () ⊗ₜ[R] m
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact h.comp (LinearEquiv.bijective _)
  have hR := Module.IsLocalRing.linearCombination_bijective_of_flat v hk
  have e : (fun r : R => r • m) =
      (Finsupp.linearCombination R v) ∘
        (Finsupp.uniqueLinearEquiv (R := R) (M := R) ()).symm := by
    funext r
    rw [Function.comp_apply, Finsupp.linearCombination_unique]
    simp [v]
  rw [e]
  exact hR.comp (LinearEquiv.bijective _)

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R]

/-- The structural action on degree-zero structure cohomology is multiplication by the
structural map on global functions. -/
theorem unitSections_smul {X : Scheme.{u}} (α : R →+* Γ(X, ⊤)) (r : R)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 0) :
    letI := moduleCohomologyModuleOfHom X α (SheafOfModules.unit X.ringCatSheaf) 0
    unitSections X (r • x) = α r * unitSections X x :=
  (moduleH0EquivOfHom X α (SheafOfModules.unit X.ringCatSheaf)).map_smul r x

variable [IsLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

/-- The closed fibre of a morphism to the spectrum of a local ring. -/
abbrev closedFibreMap :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField R)) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))

variable [GeometricallyIntegral (closedFibreMap f)]

/-- With geometrically integral proper closed fibre, the original degree-zero residue
comparison of the structure module is surjective. -/
theorem epi_moduleCohomologyBaseChangeMap_residue_unit :
    Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R))
      (SheafOfModules.unit X.ringCatSheaf) 0) := by
  let k := IsLocalRing.ResidueField R
  let σ := algebraMap R k
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let := moduleCohomologyModuleOfHom X α O 0
  have hq : IsProper q := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  have : IsProper (Over.mk q).hom := hq
  have : GeometricallyIntegral (Over.mk q).hom := (inferInstance : GeometricallyIntegral q)
  have hβ : Function.Bijective β :=
    Scheme.constants_bijective_of_proper_geometricallyIntegral (Over.mk q)
  obtain ⟨x₁, hx₁⟩ : ∃ x : Sheaf.H.{u + 1} (moduleAddSheaf X O) 0, unitSections X x = 1 :=
    ⟨_, AddEquiv.apply_symm_apply _ _⟩
  rw [ModuleCat.epi_iff_surjective]
  intro y
  obtain ⟨c, hc⟩ := hβ.2 (pullbackUnitSections p y)
  refine ⟨c ⊗ₜ[R,σ] x₁, ?_⟩
  apply (pullbackUnitSections_bijective p).1
  have h := pullbackUnitSections_moduleCohomologyTensorMap_tmul p q f σ pullback.condition c x₁
  dsimp only at h
  rw [hx₁, map_one, mul_one] at h
  exact h.trans hc

variable {f} [IsNoetherianRing R] [Flat f]

/-- Over a local Noetherian base with geometrically integral proper flat closed fibre,
the structure map to global functions is bijective. -/
theorem bijective_structureMap_of_proper_geometricallyIntegral_closedFibre :
    Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) := by
  let k := IsLocalRing.ResidueField R
  let σ := algebraMap R k
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let H := Sheaf.H.{u + 1} (moduleAddSheaf X O) 0
  let := moduleCohomologyModuleOfHom X α O 0
  have hM := Scheme.Modules.affineLocallyFiniteType_unit X
  have hflat := Scheme.Modules.relativeFlat_unit_of_flat f
  have hres := epi_moduleCohomologyBaseChangeMap_residue_unit f
  have hfree : Module.Free R H :=
    moduleCohomology_free_zero_of_epi_residue_of_proper f O hM hflat hres
  have hfin : Module.Finite R H := moduleCohomology_finite_of_proper R f O hM 0
  have hiso := moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_proper f O hM hflat 0
    hres σ
  have hT : Function.Bijective (moduleCohomologyBaseChangeMap f σ O 0) :=
    ConcreteCategory.bijective_of_isIso _
  have hq : IsProper q := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  have : IsProper (Over.mk q).hom := hq
  have : GeometricallyIntegral (Over.mk q).hom := (inferInstance : GeometricallyIntegral q)
  have hβ : Function.Bijective β :=
    Scheme.constants_bijective_of_proper_geometricallyIntegral (Over.mk q)
  obtain ⟨x₁, hx₁⟩ : ∃ x : H, unitSections X x = 1 := ⟨_, AddEquiv.apply_symm_apply _ _⟩
  -- The residue tensor `c ↦ c ⊗ x₁` (extension of scalars) is bijective.
  have hres_tmul : Function.Bijective (fun c : k => c ⊗ₜ[R,σ] x₁) := by
    have e : (fun c : k => β c) =
        (pullbackUnitSections p) ∘ (moduleCohomologyBaseChangeMap f σ O 0) ∘
          (fun c : k => c ⊗ₜ[R,σ] x₁) := by
      funext c
      have h := pullbackUnitSections_moduleCohomologyTensorMap_tmul p q f σ
        pullback.condition c x₁
      dsimp only at h
      rw [hx₁, map_one, mul_one] at h
      exact h.symm
    have h2 : Function.Bijective ((pullbackUnitSections p) ∘
        (moduleCohomologyBaseChangeMap f σ O 0)) :=
      (pullbackUnitSections_bijective p).comp hT
    have h3 : Function.Bijective (((pullbackUnitSections p) ∘
        (moduleCohomologyBaseChangeMap f σ O 0)) ∘ (fun c : k => c ⊗ₜ[R,σ] x₁)) := by
      have h4 : (((pullbackUnitSections p) ∘ (moduleCohomologyBaseChangeMap f σ O 0)) ∘
          (fun c : k => c ⊗ₜ[R,σ] x₁)) = fun c => β c := e.symm
      rw [h4]
      exact hβ
    exact (Function.Bijective.of_comp_iff' h2 _).mp h3
  -- Transport to the ordinary residue tensor.
  let B' := (ModuleCat.restrictScalars σ).obj (ModuleCat.of k k)
  let e₀ : B' ≃ₗ[R] k :=
    { toFun := fun c => (c : k)
      invFun := fun c => (c : B')
      map_add' := fun _ _ => rfl
      map_smul' := fun r c => by
        change σ r * (show k from c) = r • (show k from c)
        exact (Algebra.smul_def r (show k from c)).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E := TensorProduct.congr e₀ (LinearEquiv.refl R H)
  have hk : Function.Bijective (fun c : k => c ⊗ₜ[R] x₁) := by
    have e : (fun c : k => c ⊗ₜ[R] x₁) = E ∘ (fun c : k => (c : B') ⊗ₜ[R] x₁) := by
      funext c
      simp [E, e₀]
    rw [e]
    exact E.bijective.comp hres_tmul
  have hsmul := IsLocalRing.bijective_smul_of_bijective_residueField_tmul x₁ hk
  have e : (fun r : R => α r) = (unitSections X) ∘ (fun r : R => r • x₁) := by
    funext r
    change α r = unitSections X (r • x₁)
    rw [unitSections_smul α r x₁, hx₁, mul_one]
  change Function.Bijective (fun r : R => α r)
  rw [e]
  exact (unitSections X).bijective.comp hsmul

/-- After every ring map `σ : R →+* B`, the actual base-changed scheme has the structure
map `B → Γ(X ×_R B, ⊤)` bijective. The new ring need be neither Noetherian nor flat. -/
theorem bijective_structureMap_pullback_of_proper_geometricallyIntegral_closedFibre
    {B : Type u} [CommRing B] (σ : R →+* B) :
    Function.Bijective ((pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) := by
  let k := IsLocalRing.ResidueField R
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let q := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let H := Sheaf.H.{u + 1} (moduleAddSheaf X O) 0
  let := moduleCohomologyModuleOfHom X α O 0
  have hM := Scheme.Modules.affineLocallyFiniteType_unit X
  have hflat := Scheme.Modules.relativeFlat_unit_of_flat f
  have hres := epi_moduleCohomologyBaseChangeMap_residue_unit f
  have hiso := moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_proper f O hM hflat 0
    hres σ
  have hT : Function.Bijective (moduleCohomologyBaseChangeMap f σ O 0) :=
    ConcreteCategory.bijective_of_isIso _
  obtain ⟨x₁, hx₁⟩ : ∃ x : H, unitSections X x = 1 := ⟨_, AddEquiv.apply_symm_apply _ _⟩
  have hα : Function.Bijective α :=
    bijective_structureMap_of_proper_geometricallyIntegral_closedFibre (f := f)
  have hsmul : Function.Bijective (fun r : R => r • x₁) := by
    have e : (fun r : R => r • x₁) = (unitSections X).symm ∘ (fun r : R => α r) := by
      funext r
      apply (unitSections X).injective
      rw [Function.comp_apply, AddEquiv.apply_symm_apply, unitSections_smul α r x₁, hx₁,
        mul_one]
    rw [e]
    exact (unitSections X).symm.bijective.comp hα
  let eR : R ≃ₗ[R] H := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R H x₁) hsmul
  let B' := (ModuleCat.restrictScalars σ).obj (ModuleCat.of B B)
  let E := (TensorProduct.rid R B').symm.trans (TensorProduct.congr (LinearEquiv.refl R B') eR)
  have hb : Function.Bijective (fun b : B => b ⊗ₜ[R,σ] x₁) := by
    have e : (fun b : B => b ⊗ₜ[R,σ] x₁) = fun b : B => E (show B' from b) := by
      funext b
      change _ = (TensorProduct.congr (LinearEquiv.refl R B') eR) ((show B' from b) ⊗ₜ[R] 1)
      rw [TensorProduct.congr_tmul]
      change _ = (show B' from b) ⊗ₜ[R] ((1 : R) • x₁)
      rw [one_smul]
    rw [e]
    exact E.bijective
  have e : (fun b : B => β b) = (pullbackUnitSections p) ∘
      (moduleCohomologyBaseChangeMap f σ O 0) ∘ (fun b : B => b ⊗ₜ[R,σ] x₁) := by
    funext b
    have h := pullbackUnitSections_moduleCohomologyTensorMap_tmul p q f σ
      pullback.condition b x₁
    dsimp only at h
    rw [hx₁, map_one, mul_one] at h
    exact h.symm
  change Function.Bijective (fun b : B => β b)
  rw [e]
  exact (pullbackUnitSections_bijective p).comp (hT.comp hb)

/-- The same conclusion on every supplied cartesian square over `Spec.map σ`: the structure
map of the new scheme to `Spec B` is bijective on global functions. -/
theorem bijective_appTop_of_isPullback_of_proper_geometricallyIntegral_closedFibre
    {B : Type u} [CommRing B] (σ : R →+* B) {Y : Scheme.{u}} {p : Y ⟶ X}
    {q : Y ⟶ Spec (CommRingCat.of B)}
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ))) :
    Function.Bijective q.appTop := by
  have h0 := bijective_structureMap_pullback_of_proper_geometricallyIntegral_closedFibre
    (f := f) σ
  have hΓ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv
  have h1 : Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop :=
    (Function.Bijective.of_comp_iff _ hΓ).mp h0
  have hq : q = h.isoPullback.hom ≫ pullback.snd _ _ := (IsPullback.isoPullback_hom_snd h).symm
  rw [hq, Scheme.Hom.comp_appTop]
  exact (ConcreteCategory.bijective_of_isIso h.isoPullback.hom.appTop).comp h1

end AlgebraicGeometry.Scheme.Cohomology

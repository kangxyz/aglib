/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.Away.FiniteTypeSubalgebra
public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite-type quasi-affine schemes in finite affine charts

Select finitely many global numerator sections from finite-type affine basic
opens. Their coefficient subalgebra is finite type, although the entire ring
of global sections need not be. Localization surjectivity gives actual local
closed immersions, hence an immersion over the original affine base.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

private theorem basicOpen_subalgebra_isImmersion
    {R : Type u} [CommRing R] {Y : Scheme.{u}} [Algebra R Γ(Y, ⊤)]
    (r : Γ(Y, ⊤)) (hr : IsAffineOpen (Y.basicOpen r))
    [Algebra R Γ(Y, Y.basicOpen r)]
    [IsScalarTower R Γ(Y, ⊤) Γ(Y, Y.basicOpen r)]
    [IsLocalization.Away r Γ(Y, Y.basicOpen r)]
    (t : Finset Γ(Y, ⊤))
    (ht : Algebra.adjoin R
      ((algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r) '' (t : Set Γ(Y, ⊤))) ∪
        {IsLocalization.Away.invSelf r}) = ⊤)
    (B : Subalgebra R Γ(Y, ⊤)) (hB : ∀ a ∈ t, a ∈ B) (hrB : r ∈ B) :
    IsImmersion ((Y.basicOpen r).ι ≫ Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom B.val.toRingHom)) := by
  let rB : B := ⟨r, hrB⟩
  let : IsLocalization.Away (B.val rB) Γ(Y, Y.basicOpen r) := inferInstanceAs
    (IsLocalization.Away r Γ(Y, Y.basicOpen r))
  let ψ := IsLocalization.Away.mapₐ (Localization.Away rB) Γ(Y, Y.basicOpen r) B.val rB
  have hψ : Function.Surjective ψ :=
    IsLocalization.Away.subalgebra_map_surjective_of_numerators r t ht B hrB hB
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hψ
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away rB)))) :=
    IsOpenImmersion.of_isLocalization rB
  let : IsIso (Y.basicOpen r).toSpecΓ := hr.isoSpec.isIso_hom
  have hpow : Submonoid.powers rB ≤ (Submonoid.powers r).comap B.val.toRingHom := by
    rintro a ⟨n, rfl⟩
    exact ⟨n, by simp [rB]⟩
  have he : CommRingCat.ofHom (algebraMap B (Localization.Away rB)) ≫
      CommRingCat.ofHom ψ.toRingHom =
      CommRingCat.ofHom B.val.toRingHom ≫
        Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op := by
    ext a
    exact IsLocalization.map_eq (T := Submonoid.powers r) hpow a
  rw [← Category.assoc, ← (Y.basicOpen r).toSpecΓ_SpecMap_presheaf_map_top, Category.assoc,
    ← Spec.map_comp, ← he, Spec.map_comp, ← Category.assoc]
  infer_instance

/-- A finite-type quasi-affine scheme has an actual immersion into the spectrum
of a finite-type algebra over the original base ring. No finite-generation
hypothesis is imposed on its full ring of global sections. -/
theorem exists_finiteType_affine_immersion {R : Type u} [CommRing R]
    {Y : Scheme.{u}} [Y.IsQuasiAffine] (f : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] :
    ∃ (A : Type u) (_ : CommRing A) (φ : R →+* A)
      (j : Y ⟶ Spec (CommRingCat.of A)),
      φ.FiniteType ∧ IsImmersion j ∧ j ≫ Spec.map (CommRingCat.ofHom φ) = f := by
  classical
  let φ : R →+* Γ(Y, ⊤) := ((ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
  let : Algebra R Γ(Y, ⊤) := φ.toAlgebra
  let (r : Γ(Y, ⊤)) : Algebra R Γ(Y, Y.basicOpen r) :=
    ((algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r)).comp φ).toAlgebra
  let (r : Γ(Y, ⊤)) : IsScalarTower R Γ(Y, ⊤) Γ(Y, Y.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let (r : Γ(Y, ⊤)) : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
  have hfin (r : Γ(Y, ⊤)) (hr : IsAffineOpen (Y.basicOpen r)) :
      Algebra.FiniteType R Γ(Y, Y.basicOpen r) := by
    have h₁ := f.finiteType_appLE (isAffineOpen_top (Spec (CommRingCat.of R))) hr
      (show Y.basicOpen r ≤ f ⁻¹ᵁ ⊤ from le_top)
    have h₂ : ((ΓSpecIso (CommRingCat.of R)).inv.hom).FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
    exact h₁.comp h₂
  have hcover (x : Y) : ∃ r : Γ(Y, ⊤), IsAffineOpen (Y.basicOpen r) ∧ x ∈ Y.basicOpen r := by
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hx, _⟩ :=
      (IsQuasiAffine.isBasis_basicOpen Y).exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
    exact ⟨r, hr, hx⟩
  choose r hr hxr using hcover
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : Y => (Y.basicOpen (r x) : Set Y))
    (fun x => (Y.basicOpen (r x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hxr x⟩)
  have hn (i : s) : ∃ t : Finset Γ(Y, ⊤), r i.val ∈ t ∧
      Algebra.adjoin R
        ((algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen (r i.val)) '' (t : Set Γ(Y, ⊤))) ∪
          {IsLocalization.Away.invSelf (r i.val)}) = ⊤ := by
    let := hfin (r i.val) (hr i.val)
    exact IsLocalization.Away.exists_finset_numerators (r i.val)
  choose t hrt ht using hn
  let T : Finset Γ(Y, ⊤) := Finset.univ.biUnion t
  let B : Subalgebra R Γ(Y, ⊤) := Algebra.adjoin R (T : Set Γ(Y, ⊤))
  have hB (i : s) (a : Γ(Y, ⊤)) (ha : a ∈ t i) : a ∈ B :=
    Algebra.subset_adjoin (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩)
  have hrB (i : s) : r i.val ∈ B := hB i _ (hrt i)
  let j : Y ⟶ Spec (CommRingCat.of B) :=
    Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom B.val.toRingHom)
  have hj : IsImmersion j := by
    let : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) :=
      { postcomp := fun i hi g hg => by
          let : IsOpenImmersion i := hi
          let : IsImmersion g := hg
          infer_instance }
    let : MorphismProperty.HasOfPostcompProperty (@IsImmersion) (@IsOpenImmersion) :=
      { of_postcomp := fun g k _ hgk => by
          let : IsImmersion (g ≫ k) := hgk
          exact IsImmersion.of_comp g k }
    apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion) j
    intro x
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨ha, hxa⟩ := Set.mem_iUnion.mp hxa
    let i : s := ⟨a, ha⟩
    let V : (Spec (CommRingCat.of B)).Opens :=
      PrimeSpectrum.basicOpen (⟨r a, hrB i⟩ : B)
    have he : j ⁻¹ᵁ V = Y.basicOpen (r a) := by
      exact (Hom.comp_preimage Y.toSpecΓ
        (Spec.map (CommRingCat.ofHom B.val.toRingHom)) V).trans
          ((congrArg (fun W => Y.toSpecΓ ⁻¹ᵁ W)
            (SpecMap_preimage_basicOpen (CommRingCat.ofHom B.val.toRingHom)
              (⟨r a, hrB i⟩ : B))).trans (Y.toSpecΓ_preimage_basicOpen (r a)))
    refine ⟨V, ?_, ?_⟩
    · change x ∈ j ⁻¹ᵁ V
      rw [he]
      exact hxa
    · rw [he]
      exact basicOpen_subalgebra_isImmersion (r a) (hr a) (t i) (ht i) B (hB i) (hrB i)
  let : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp ⟨T, rfl⟩
  refine ⟨B, inferInstance, algebraMap R B, j, RingHom.finiteType_algebraMap.mpr inferInstance,
    hj, ?_⟩
  have hφ : CommRingCat.ofHom (algebraMap R B) ≫ CommRingCat.ofHom B.val.toRingHom =
      (ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop := rfl
  dsimp only [j]
  rw [Category.assoc, ← Spec.map_comp, hφ, Spec.map_comp,
    ← toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The finite-type quasi-affine immersion lands in an actual standard affine
chart of finite projective space, with its original structural morphism. -/
theorem exists_projectiveChart_immersion_of_isQuasiAffine {R : Type u} [CommRing R]
    {Y : Scheme.{u}} [Y.IsQuasiAffine] (f : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] :
    ∃ (ι : Type u) (_ : Fintype ι)
      (j : Y ⟶ (ProjectiveSpace.coordinateOpen R (Option ι) none).toScheme),
      IsImmersion j ∧
        (j ≫ (ProjectiveSpace.coordinateOpen R (Option ι) none).ι) ≫
          ProjectiveSpace.toSpec R (Option ι) = f := by
  obtain ⟨A, hA, φ, j, hφ, hj, he⟩ := exists_finiteType_affine_immersion f
  let := hA
  let := hj
  obtain ⟨ι, hι, k, hk, hbase⟩ :=
    ProjectiveSpace.exists_projectiveChart_closedImmersion_of_finiteType φ hφ
  let := hι
  let := hk
  refine ⟨ι, hι, j ≫ k, inferInstance, ?_⟩
  calc
    ((j ≫ k) ≫ (ProjectiveSpace.coordinateOpen R (Option ι) none).ι) ≫
        ProjectiveSpace.toSpec R (Option ι) =
        j ≫ ((k ≫ (ProjectiveSpace.coordinateOpen R (Option ι) none).ι) ≫
          ProjectiveSpace.toSpec R (Option ι)) := by simp only [Category.assoc]
    _ = f := by rw [hbase, he]

end AlgebraicGeometry.Scheme

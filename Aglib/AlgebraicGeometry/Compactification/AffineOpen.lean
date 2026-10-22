/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Affine
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian

/-!
# Compactification through an affine base open

An affine source of finite type over an affine open embeds into a proper
scheme over the entire base. The ambient scheme is the base change of finite
projective space over the lifted integers. No finite-type assumption over
the integers and no Noetherian hypothesis are used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Compactify the literal composite through an affine base open. The
quasi-compactness hypothesis concerns this composite over the entire base. -/
theorem exists_schematicallyDense_compactification_through_affineOpen
    {X S : Scheme.{u}} [IsAffine X] {R : Type u} [CommRing R]
    (k : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion k]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    [QuasiCompact (f ≫ k)] :
    ∃ C : Compactification (f ≫ k), IsSchemeTheoreticallyDominant C.j := by
  let φ : R →+* Γ(X, ⊤) := ((ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
  have hf : f.appTop.hom.FiniteType := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact f.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  have hφ : φ.FiniteType := hf.comp
    (RingHom.FiniteType.of_surjective _
      (ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective)
  have hfac : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) = f := by
    change X.toSpecΓ ≫ Spec.map ((ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  obtain ⟨I, hI, j, hj, hjbase⟩ :=
    ProjectiveSpace.exists_projectiveImmersion_of_finiteType φ hφ
  let := hI
  let := hj
  let σ : ULift.{u} ℤ →+* R :=
    (Int.castRingHom R).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
  let s : S ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) := specULiftZIsTerminal.from S
  have hσ : Spec.map (CommRingCat.ofHom σ) = k ≫ s :=
    specULiftZIsTerminal.hom_ext _ _
  let pZ := ProjectiveSpace.toSpec (ULift.{u} ℤ) (Option I)
  let E := ProjectiveSpace.baseChangeIso σ (Option I) ≪≫
    pullback.congrHom (rfl : pZ = pZ) hσ
  let L := pullbackLeftPullbackSndIso pZ s k
  let m := E.hom ≫ L.inv ≫ pullback.fst (pullback.snd pZ s) k
  let p := pullback.snd pZ s
  have hsnd {A B C : Scheme.{u}} {a a' : A ⟶ C} {b b' : B ⟶ C}
      (ha : a = a') (hb : b = b') :
      (pullback.congrHom ha hb).hom ≫ pullback.snd a' b' = pullback.snd a b := by
    subst a'
    subst b'
    simp
  have hE : E.hom ≫ pullback.snd pZ (k ≫ s) =
      ProjectiveSpace.toSpec R (Option I) := by
    dsimp only [E]
    rw [Iso.trans_hom, Category.assoc, hsnd, ProjectiveSpace.baseChangeIso_hom_snd]
  have hL : L.inv ≫ pullback.fst (pullback.snd pZ s) k ≫ p =
      pullback.snd pZ (k ≫ s) ≫ k :=
    pullbackLeftPullbackSndIso_inv_fst_snd pZ s k
  have hmp : m ≫ p = ProjectiveSpace.toSpec R (Option I) ≫ k := by
    calc
      m ≫ p = E.hom ≫ (L.inv ≫ pullback.fst (pullback.snd pZ s) k ≫ p) := by
        simp only [m, Category.assoc]
      _ = E.hom ≫ pullback.snd pZ (k ≫ s) ≫ k := by rw [hL]
      _ = ProjectiveSpace.toSpec R (Option I) ≫ k := by rw [← Category.assoc, hE]
  let J := X.isoSpec.hom ≫ j ≫ m
  have hJ : J ≫ p = f ≫ k := by
    calc
      J ≫ p = X.isoSpec.hom ≫ j ≫ ProjectiveSpace.toSpec R (Option I) ≫ k := by
        simp only [J, Category.assoc, hmp]
      _ = (X.isoSpec.hom ≫ (j ≫ ProjectiveSpace.toSpec R (Option I))) ≫ k := by
        simp only [Category.assoc]
      _ = (X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)) ≫ k := by rw [hjbase]
      _ = f ≫ k := by rw [hfac]
  let : IsOpenImmersion m := by dsimp only [m]; infer_instance
  let : IsImmersion J := by dsimp only [J]; infer_instance
  let : IsProper p := by dsimp only [p, pZ]; infer_instance
  let : QuasiCompact (J ≫ p) := by rw [hJ]; infer_instance
  have : QuasiCompact J := QuasiCompact.of_comp J p
  exact ⟨Compactification.ofImmersion (f ≫ k) J p hJ, inferInstance⟩

/-- The topologically dense form of affine-open compactification, retaining
its original public interface. -/
theorem exists_compactification_through_affineOpen
    {X S : Scheme.{u}} [IsAffine X] {R : Type u} [CommRing R]
    (k : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion k]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    [QuasiCompact (f ≫ k)] :
    ∃ C : Compactification (f ≫ k), IsDominant C.j := by
  obtain ⟨C, hC⟩ := exists_schematicallyDense_compactification_through_affineOpen k f
  let : IsSchemeTheoreticallyDominant C.j := hC
  let : QuasiCompact (C.j ≫ C.p) := by rw [C.fac]; infer_instance
  have : QuasiCompact C.j := QuasiCompact.of_comp C.j C.p
  exact ⟨C, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom

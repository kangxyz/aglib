/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.FiniteProjective.ConeStep
public import Aglib.Algebra.Homology.MappingCone.Rotation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Actual finite-projective replacement of bounded flat complexes

A bounded nonnegative flat complex over a Noetherian ring, with finite
original homology, has an actual bounded finite-projective complex mapping
quasi-isomorphically to it. The proof successively covers the actual top
homology, truncates the original cone, and reassembles by native cone rotation.
The literal replacement map remains a quasi-isomorphism after every ring
scalar extension, by the proved bounded-above acyclic flat cone criterion.
No model or base-change-comparison family is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A bounded nonnegative flat complex with finite original homology over
a Noetherian ring has an actual finite-projective replacement with the same
strict term bounds and an actual quasi-isomorphism to the original complex. -/
theorem exists_finiteProjective_model
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℕ)
    [K.IsStrictlyGE 0] [K.IsStrictlyLE (n : ℤ)]
    [∀ i, Module.Flat R (K.X i)] [∀ i, Module.Finite R (K.homology i)] :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyGE 0 ∧ P.IsStrictlyLE (n : ℤ) ∧
      (∀ i, Module.Finite R (P.X i)) ∧ (∀ i, Module.Projective R (P.X i)) ∧
      ∃ u : P ⟶ K, QuasiIso u := by
  induction n generalizing K with
  | zero =>
    have hfinite₀ : Module.Finite R (K.X 0) := by
      let e : K.homology 0 ≅ K.X 0 :=
        (K.isoHomologyπ (-1) 0 (by simp)
          ((K.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _)).symm ≪≫
        K.iCyclesIso 0 1 (by simp)
          ((K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _)
      exact Module.Finite.equiv e.toLinearEquiv
    have hfinite (i : ℤ) : Module.Finite R (K.X i) := by
      by_cases hi : i = 0
      · subst i
        exact hfinite₀
      · have hz : IsZero (K.X i) := by
          obtain hi | hi := lt_or_gt_of_ne hi
          · exact K.isZero_of_isStrictlyGE 0 i hi
          · exact K.isZero_of_isStrictlyLE 0 i hi
        let := ModuleCat.subsingleton_of_isZero hz
        infer_instance
    have hprojective (i : ℤ) : Module.Projective R (K.X i) := by
      let : Module.Finite R (K.X i) := hfinite i
      let := Module.finitePresentation_of_finite R (K.X i)
      exact Module.Flat.projective_of_finitePresentation
    exact ⟨K, inferInstance, inferInstance, hfinite, hprojective, 𝟙 K, inferInstance⟩
  | succ n ih =>
    let : K.IsStrictlyLE ((n : ℤ) + 1) := by
      simpa only [Nat.cast_succ] using
        (inferInstance : K.IsStrictlyLE ((n + 1 : ℕ) : ℤ))
    obtain ⟨A, hAfinite, hAfree, φ, hφ, hLge, hLle, hLflat, hLfinite, hι⟩ :=
      exists_finiteFree_single_top_reduction K n
    let : Module.Finite R A := hAfinite
    let : Module.Free R A := hAfree
    let b : ℤ := (n : ℤ) + 1
    let J : CochainComplex (ModuleCat.{max u v} R) ℤ :=
      (single (ModuleCat.{max u v} R) (.up ℤ) b).obj A
    let L := (mappingCone φ).truncLE (n : ℤ)
    let : L.IsStrictlyGE 0 := hLge
    let : L.IsStrictlyLE (n : ℤ) := hLle
    let (i : ℤ) : Module.Flat R (L.X i) := hLflat i
    let (i : ℤ) : Module.Finite R (L.homology i) := hLfinite i
    obtain ⟨Q, hQge, hQle, hQfinite, hQprojective, s, hs⟩ := ih L
    let : Q.IsStrictlyGE 0 := hQge
    let : Q.IsStrictlyLE (n : ℤ) := hQle
    let (i : ℤ) : Module.Finite R (Q.X i) := hQfinite i
    let (i : ℤ) : Module.Projective R (Q.X i) := hQprojective i
    let : QuasiIso s := hs
    let : QuasiIso ((mappingCone φ).ιTruncLE (n : ℤ)) := hι
    let t : Q ⟶ mappingCone φ := s ≫ (mappingCone φ).ιTruncLE (n : ℤ)
    let : QuasiIso t := inferInstance
    let D := mappingCocone (t ≫ (mappingCone.triangle φ).mor₃)
    let u : D ⟶ K := mappingCone.reassemblyMap φ t
    let : QuasiIso u := mappingCone.reassemblyMap_quasiIso φ t
    have hJ (i : ℤ) : Module.Finite R (J.X i) ∧ Module.Projective R (J.X i) := by
      by_cases hi : i = b
      · subst i
        exact ⟨Module.Finite.equiv (singleObjXSelf (.up ℤ) b A).symm.toLinearEquiv,
          Module.Projective.of_equiv' (singleObjXSelf (.up ℤ) b A).symm.toLinearEquiv⟩
      · let := ModuleCat.subsingleton_of_isZero (isZero_single_obj_X (.up ℤ) b A i hi)
        exact ⟨inferInstance, inferInstance⟩
    let (i : ℤ) : Module.Finite R (J.X i) := (hJ i).1
    let (i : ℤ) : Module.Projective R (J.X i) := (hJ i).2
    have hDge : D.IsStrictlyGE 0 := by
      rw [isStrictlyGE_iff]
      intro i hi
      apply IsZero.of_iso _ (mappingCone.reassemblyTermIso φ t i)
      exact (biprod_isZero_iff _ _).mpr
        ⟨Q.isZero_of_isStrictlyGE 0 i hi,
          isZero_single_obj_X (.up ℤ) b A i (by dsimp [b]; omega)⟩
    have hDle : D.IsStrictlyLE b := by
      rw [isStrictlyLE_iff]
      intro i hi
      apply IsZero.of_iso _ (mappingCone.reassemblyTermIso φ t i)
      exact (biprod_isZero_iff _ _).mpr
        ⟨Q.isZero_of_isStrictlyLE (n : ℤ) i (by dsimp [b] at hi; omega),
          isZero_single_obj_X (.up ℤ) b A i (ne_of_gt hi)⟩
    have hDfinite (i : ℤ) : Module.Finite R (D.X i) := by
      let e : D.X i ≅ ModuleCat.of R (Q.X i × J.X i) :=
        mappingCone.reassemblyTermIso φ t i ≪≫ ModuleCat.biprodIsoProd _ _
      exact Module.Finite.equiv e.symm.toLinearEquiv
    have hDprojective (i : ℤ) : Module.Projective R (D.X i) := by
      let e : D.X i ≅ ModuleCat.of R (Q.X i × J.X i) :=
        mappingCone.reassemblyTermIso φ t i ≪≫ ModuleCat.biprodIsoProd _ _
      exact Module.Projective.of_equiv' e.symm.toLinearEquiv
    exact ⟨D, hDge, by simpa only [Nat.cast_succ] using hDle,
      hDfinite, hDprojective, u, inferInstance⟩

/-- The actual replacement map remains a quasi-isomorphism after every
ring scalar extension. This is proved for the original map from its bounded
flat cone, with independent ring and module-carrier universes. -/
theorem exists_finiteProjective_model_with_baseChange
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (n : ℕ)
    [K.IsStrictlyGE 0] [K.IsStrictlyLE (n : ℤ)]
    [∀ i, Module.Flat R (K.X i)] [∀ i, Module.Finite R (K.homology i)] :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      P.IsStrictlyGE 0 ∧ P.IsStrictlyLE (n : ℤ) ∧
      (∀ i, Module.Finite R (P.X i)) ∧ (∀ i, Module.Projective R (P.X i)) ∧
      ∃ u : P ⟶ K, QuasiIso u ∧
        ∀ (B : Type w) [CommRing B] (σ : R →+* B),
          QuasiIso (((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).map u) := by
  obtain ⟨P, hge, hle, hfinite, hprojective, u, hu⟩ := exists_finiteProjective_model K n
  let : P.IsStrictlyLE (n : ℤ) := hle
  let (i : ℤ) : Module.Projective R (P.X i) := hprojective i
  let : QuasiIso u := hu
  refine ⟨P, hge, hle, hfinite, hprojective, u, hu, ?_⟩
  intro B _ σ
  exact quasiIso_extendScalars_of_flat σ u (n : ℤ) (n : ℤ)

end CochainComplex

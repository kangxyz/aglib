/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.OpenExtension
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Refinement
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Density
public import Aglib.AlgebraicGeometry.Morphisms.Restrict.Agreement
public import Aglib.AlgebraicGeometry.Gluing.SchematicDensity

/-!
# Global maps from local admissible sequences

Actual local sequences extend to the base and admit a finite common refinement.
Their maps glue on the whole refined source, not just a partial domain. Agreement
is checked on the schematically dense protected open by actual Cartesian lifts.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

/-- Maps on local sequence modifications of a finite open cover extend to a
single global map after an actual admissible sequence. Both the structural
map and the prescribed map on the protected open are retained literally. -/
theorem exists_map_of_finite_cover {X P S : Scheme.{u}} [IsLocallyNoetherian X]
    (C : X.OpenCover.{v}) [Finite C.I₀] [∀ i, QuasiCompact (C.f i)]
    (U : X.Opens) [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι]
    (pX : X ⟶ S) (pP : P ⟶ S) [IsSeparated pP] (g : U.toScheme ⟶ P)
    (B : C.I₀ → Scheme.{u}) (γ : ∀ i, B i ⟶ C.X i)
    (hγ : ∀ i, AdmissibleSequence (C.f i ⁻¹ᵁ U) (γ i))
    (F : ∀ i, B i ⟶ P)
    (hbase : ∀ i, F i ≫ pP = γ i ≫ C.f i ≫ pX)
    (hagree : ∀ i, (γ i ⁻¹ᵁ C.f i ⁻¹ᵁ U).ι ≫ F i =
      (γ i ∣_ C.f i ⁻¹ᵁ U) ≫ (C.f i ∣_ U) ≫ g) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (G : Y ⟶ P),
      AdmissibleSequence U β ∧ IsProper β ∧ IsIso (β ∣_ U) ∧
      IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι ∧
      G ≫ pP = β ≫ pX ∧ (β ⁻¹ᵁ U).ι ≫ G = (β ∣_ U) ≫ g := by
  classical
  let : Fintype C.I₀ := Fintype.ofFinite _
  have hext := fun i ↦ (hγ i).exists_open_extension (C.f i) U
  choose A α m hα hm using hext
  obtain ⟨Y, β, a₀, hβ, ha₀⟩ :=
    exists_finite_refinement U A α hα Finset.univ
  let a : ∀ i, Y ⟶ A i := fun i ↦ a₀ ⟨i, Finset.mem_univ i⟩
  have ha : ∀ i, a i ≫ α i = β := fun i ↦ ha₀ ⟨i, Finset.mem_univ i⟩
  let : IsProper β := hβ.isProper
  let : IsIso (β ∣_ U) := hβ.restrict_isIso
  let : IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι :=
    hβ.preimage_open_isSchemeTheoreticallyDominant
  let : QuasiCompact (β ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict β U) inferInstance
  let D := C.pullback₁ β
  let b : ∀ i : C.I₀, D.X i ⟶ B i := fun i ↦
    (hm i).lift (pullback.fst β (C.f i) ≫ a i) (pullback.snd β (C.f i)) (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ pullback.fst β (C.f i) ≫ z) (ha i)).trans
          (pullback.condition (f := β) (g := C.f i))))
  have hb : ∀ i : C.I₀, b i ≫ γ i = pullback.snd β (C.f i) := fun i ↦
    (hm i).lift_snd _ _ _
  let H : ∀ i, D.X i ⟶ P := fun i ↦ b i ≫ F i
  have hbase' : ∀ i : C.I₀, D.f i ≫ (β ≫ pX) = H i ≫ pP := by
    intro i
    change pullback.fst β (C.f i) ≫ (β ≫ pX) = (b i ≫ F i) ≫ pP
    rw [Category.assoc, hbase, ← Category.assoc (b i) (γ i), hb]
    exact congrArg (fun z ↦ z ≫ pX) (pullback.condition (f := β) (g := C.f i))
  have hcompat : ∀ i : C.I₀, pullback.fst (D.f i) (β ⁻¹ᵁ U).ι ≫ H i =
      pullback.snd (D.f i) (β ⁻¹ᵁ U).ι ≫ ((β ∣_ U) ≫ g) := by
    intro i
    exact Hom.agreement_on_pullback_restriction (C.f i) β (γ i) (b i) (hb i)
      U g (F i) (hagree i)
  obtain ⟨G, _, hG, hGp⟩ := Scheme.Cover.exists_glue_of_schemeTheoreticallyDominant D
    (β ≫ pX) pP (β ⁻¹ᵁ U).ι ((β ∣_ U) ≫ g) H hbase' hcompat
  exact ⟨Y, β, G, hβ, inferInstance, inferInstance, inferInstance, hGp, hG⟩

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

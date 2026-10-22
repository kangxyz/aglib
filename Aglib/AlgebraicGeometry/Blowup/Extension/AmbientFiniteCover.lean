/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Extension.LocalMap
public import Aglib.AlgebraicGeometry.Blowup.Refinement.Finite
public import Aglib.AlgebraicGeometry.Gluing.SchematicDensity

/-!
# Local extension with a larger protected ambient open

Local centres are first extended across a finite cover, then from the given
open subscheme to the ambient scheme. The global finite refinement is an
isomorphism on the entire protected ambient open. Maps and schematic density
are asserted only over the original open subscheme, not over the ambient space.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Blowup

variable {X Z P S : Scheme.{u}} [IsLocallyNoetherian X]

/-- Global centres and their actual finite refinement extend local maps while
protecting a possibly larger ambient open. The map exists only over the
base-changed original open subscheme. -/
theorem exists_ambient_extension_of_finite_cover (q : Z ⟶ X)
    [IsOpenImmersion q] [QuasiCompact q] (C : Z.OpenCover.{v}) [Finite C.I₀]
    [∀ i, QuasiCompact (C.f i)] (V : X.Opens)
    [QuasiCompact (q ⁻¹ᵁ V).ι] [IsSchemeTheoreticallyDominant (q ⁻¹ᵁ V).ι]
    (pX : X ⟶ S) (pP : P ⟶ S) [IsSeparated pP] (g : (q ⁻¹ᵁ V).toScheme ⟶ P)
    (J : ∀ i, (C.X i).IdealSheafData) (B : ∀ i, BlowupDatum (J i))
    (F : ∀ i, (B i).Y ⟶ P)
    (hJ : ∀ i, (J i).comap (C.f i ⁻¹ᵁ q ⁻¹ᵁ V).ι = ⊤)
    (hbase : ∀ i, F i ≫ pP = (B i).map ≫ C.f i ≫ q ≫ pX)
    (hagree : ∀ i, ((B i).map ⁻¹ᵁ C.f i ⁻¹ᵁ q ⁻¹ᵁ V).ι ≫ F i =
      ((B i).map ∣_ C.f i ⁻¹ᵁ q ⁻¹ᵁ V) ≫ (C.f i ∣_ q ⁻¹ᵁ V) ≫ g) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (G : pullback β q ⟶ P),
      AdmissibleSequence V β ∧ IsProper β ∧ IsIso (β ∣_ V) ∧
      (Dense (V : Set X) → Dense ((β ⁻¹ᵁ V : Y.Opens) : Set Y)) ∧
      IsSchemeTheoreticallyDominant ((pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V).ι ∧
      G ≫ pP = pullback.snd β q ≫ q ≫ pX ∧
      ((pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V).ι ≫ G =
        ((pullback.snd β q) ∣_ q ⁻¹ᵁ V) ≫ g := by
  classical
  let : Fintype C.I₀ := Fintype.ofFinite _
  let KZ : C.I₀ → Z.IdealSheafData := fun i ↦ (J i).map (C.f i)
  let BZ : ∀ i, BlowupDatum (KZ i) := fun i ↦ blowupDatum (KZ i)
  let K : C.I₀ → X.IdealSheafData := fun i ↦ (KZ i).map q
  let BG : ∀ i, BlowupDatum (K i) := fun i ↦ blowupDatum (K i)
  have hKZ : ∀ i, (KZ i).comap (q ⁻¹ᵁ V).ι = ⊤ := fun i ↦
    (J i).map_comap_eq_top_of_comap_eq_top (C.f i) (q ⁻¹ᵁ V) (hJ i)
  have hK : ∀ i, (K i).comap V.ι = ⊤ := fun i ↦
    (KZ i).map_comap_eq_top_of_comap_eq_top q V (hKZ i)
  obtain ⟨Y, β, a, hseq, hβ, hV, htop, hd, ha⟩ :=
    exists_finite_admissible_refinement_of_flat_schematicallyDense_with_sequence
      V q K BG Finset.univ (fun i _ ↦ hK i)
  let : IsSchemeTheoreticallyDominant ((pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V).ι := hd
  let : QuasiCompact ((pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V).ι :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict (pullback.snd β q) (q ⁻¹ᵁ V)) inferInstance
  let a' : ∀ i, Y ⟶ (BG i).Y := fun i ↦ a ⟨i, Finset.mem_univ i⟩
  have ha' : ∀ i, a' i ≫ (BG i).map = β := fun i ↦ ha ⟨i, Finset.mem_univ i⟩
  let az : ∀ i, pullback β q ⟶ (BZ i).Y := fun i ↦
    LocalMap.lift q (KZ i) (BZ i) (BG i) β (a' i) (ha' i)
  have haz : ∀ i, az i ≫ (BZ i).map = pullback.snd β q := fun i ↦
    LocalMap.lift_map q (KZ i) (BZ i) (BG i) β (a' i) (ha' i)
  let l : ∀ i, pullback (pullback.snd β q) (C.f i) ⟶ (B i).Y := fun i ↦
    LocalMap.lift (C.f i) (J i) (B i) (BZ i) (pullback.snd β q) (az i) (haz i)
  let D := C.pullback₁ (pullback.snd β q)
  let H : ∀ i, D.X i ⟶ P := fun i ↦ l i ≫ F i
  have hb : ∀ i, D.f i ≫ (pullback.snd β q ≫ q ≫ pX) = H i ≫ pP := by
    intro i
    change pullback.fst (pullback.snd β q) (C.f i) ≫
      (pullback.snd β q ≫ q ≫ pX) = (l i ≫ F i) ≫ pP
    rw [Category.assoc, hbase, ← Category.assoc (l i) (B i).map, LocalMap.lift_map]
    exact congrArg (fun z ↦ z ≫ q ≫ pX)
      (pullback.condition (f := pullback.snd β q) (g := C.f i))
  have hc : ∀ i,
      pullback.fst (D.f i) ((pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V).ι ≫ H i =
      pullback.snd (D.f i) ((pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V).ι ≫
        (((pullback.snd β q) ∣_ q ⁻¹ᵁ V) ≫ g) := by
    intro i
    exact LocalMap.lift_agrees (C.f i) (J i) (B i) (BZ i)
      (pullback.snd β q) (az i) (haz i) (q ⁻¹ᵁ V) g (F i) (hagree i)
  obtain ⟨G, _, hG, hGp⟩ := Scheme.Cover.exists_glue_of_schemeTheoreticallyDominant D
    (pullback.snd β q ≫ q ≫ pX) pP ((pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V).ι
    (((pullback.snd β q) ∣_ q ⁻¹ᵁ V) ≫ g) H hb hc
  exact ⟨Y, β, G, hseq, hβ, hV, htop, hd, hGp, hG⟩

end AlgebraicGeometry.Scheme.Blowup

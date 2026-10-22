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
# Globalization of local admissible blowup extensions

Extend the actual local centres by schematic closure, refine their finitely
many native global blowups, and glue the actual pulled local maps. Schematic
density is assumed only on the protected open at this intermediate stage.
The output modification is a proper composite, not falsely a single blowup.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Blowup

variable {X P S : Scheme.{u}} [IsLocallyNoetherian X]

/-- Actual extensions on a finite open cover globalize after a finite
admissible refinement, retaining the protected-open and structural triangles. -/
theorem exists_extension_of_finite_cover (C : X.OpenCover.{v}) [Finite C.I₀]
    [∀ i, QuasiCompact (C.f i)] (U : X.Opens)
    [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι]
    (pX : X ⟶ S) (pP : P ⟶ S) [IsSeparated pP] (gU : U.toScheme ⟶ P)
    (J : ∀ i, (C.X i).IdealSheafData) (B : ∀ i, BlowupDatum (J i))
    (F : ∀ i, (B i).Y ⟶ P)
    (hJ : ∀ i, (J i).comap (C.f i ⁻¹ᵁ U).ι = ⊤)
    (hbase : ∀ i, F i ≫ pP = (B i).map ≫ C.f i ≫ pX)
    (hagree : ∀ i, ((B i).map ⁻¹ᵁ C.f i ⁻¹ᵁ U).ι ≫ F i =
      ((B i).map ∣_ C.f i ⁻¹ᵁ U) ≫ (C.f i ∣_ U) ≫ gU) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (G : Y ⟶ P),
      IsProper β ∧ IsIso (β ∣_ U) ∧
      IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι ∧
      G ≫ pP = β ≫ pX ∧ (β ⁻¹ᵁ U).ι ≫ G = (β ∣_ U) ≫ gU := by
  classical
  let : Fintype C.I₀ := Fintype.ofFinite _
  let K : C.I₀ → X.IdealSheafData := fun i ↦ (J i).map (C.f i)
  let BG : ∀ i, BlowupDatum (K i) := fun i ↦ blowupDatum (K i)
  have hK : ∀ i, (K i).comap U.ι = ⊤ := fun i ↦
    (J i).map_comap_eq_top_of_comap_eq_top (C.f i) U (hJ i)
  obtain ⟨Y, β, a, hβ, hU, hd, ha⟩ :=
    exists_finite_admissible_refinement_of_schematicallyDense U K BG Finset.univ
      (fun i _ ↦ hK i)
  let : IsProper β := hβ
  let : IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι := hd
  let : QuasiCompact (β ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict β U) inferInstance
  let a' : ∀ i, Y ⟶ (BG i).Y := fun i ↦ a ⟨i, Finset.mem_univ i⟩
  have ha' : ∀ i, a' i ≫ (BG i).map = β := fun i ↦ ha ⟨i, Finset.mem_univ i⟩
  let l : ∀ i, pullback β (C.f i) ⟶ (B i).Y := fun i ↦
    LocalMap.lift (C.f i) (J i) (B i) (BG i) β (a' i) (ha' i)
  let D := C.pullback₁ β
  let H : ∀ i, D.X i ⟶ P := fun i ↦ l i ≫ F i
  have hb : ∀ i, D.f i ≫ (β ≫ pX) = H i ≫ pP := by
    intro i
    change pullback.fst β (C.f i) ≫ (β ≫ pX) = (l i ≫ F i) ≫ pP
    rw [Category.assoc, hbase, ← Category.assoc (l i) (B i).map,
      LocalMap.lift_map]
    exact congrArg (fun z ↦ z ≫ pX) (pullback.condition (f := β) (g := C.f i))
  have hc : ∀ i, pullback.fst (D.f i) (β ⁻¹ᵁ U).ι ≫ H i =
      pullback.snd (D.f i) (β ⁻¹ᵁ U).ι ≫ ((β ∣_ U) ≫ gU) := by
    intro i
    exact LocalMap.lift_agrees (C.f i) (J i) (B i) (BG i) β (a' i) (ha' i)
      U gU (F i) (hagree i)
  obtain ⟨G, _, hG, hGp⟩ := Scheme.Cover.exists_glue_of_schemeTheoreticallyDominant D
    (β ≫ pX) pP (β ⁻¹ᵁ U).ι ((β ∣_ U) ≫ gU) H hb hc
  exact ⟨Y, β, G, hβ, hU, hd, hGp, hG⟩

end AlgebraicGeometry.Scheme.Blowup

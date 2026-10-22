/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GraphPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# A separated patch from a proper modification and a boundary complement

The overlap is the original protected open, transported through the actual
restricted isomorphism. Its graph is obtained by restricting the closed graph
of the proper modification embedded in its ambient scheme. This construction
does not identify an arbitrary ordinary pullback with a strict transform.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.SeparatedGluing

/-- Removing an ambient boundary whose inverse image is the complement of the
protected open produces a separated patch containing the original scheme. -/
theorem exists_boundary_patch
    {T X Y S : Scheme.{u}}
    (β : T ⟶ X) [IsProper β] (i : T ⟶ Y) [IsOpenImmersion i]
    (pX : X ⟶ S) [IsSeparated pX] (pY : Y ⟶ S) [IsSeparated pY]
    (h : i ≫ pY = β ≫ pX) (U : X.Opens) (O : Y.Opens)
    [IsIso (β ∣_ U)] (hpre : i ⁻¹ᵁ O = β ⁻¹ᵁ U) :
    ∃ (r : U.toScheme ⟶ O.toScheme) (hr : U.ι ≫ pX = r ≫ (O.ι ≫ pY))
      (ho : IsOpenImmersion r),
      letI := ho
      r ≫ O.ι = inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι ≫ i ∧
      IsClosedImmersion (pullback.lift U.ι r hr) ∧
      IsSeparated (pushout.desc pX (O.ι ≫ pY) hr) := by
  let g := pullback.lift i β h
  have hgf : g ≫ pullback.fst pY pX = i := pullback.lift_fst _ _ _
  have hgs : g ≫ pullback.snd pY pX = β := pullback.lift_snd _ _ _
  let : IsImmersion (g ≫ pullback.fst pY pX) := by rw [hgf]; infer_instance
  let : IsImmersion g := IsImmersion.of_comp g (pullback.fst pY pX)
  let : IsProper (g ≫ pullback.snd pY pX) := by rw [hgs]; infer_instance
  let : IsProper g := IsProper.of_comp g (pullback.snd pY pX)
  let : IsClosedImmersion g := IsClosedImmersion.of_isPreimmersion g
    g.isClosedMap.isClosed_range
  let e : U.toScheme ≅ pullback i O.ι :=
    (asIso (β ∣_ U)).symm ≪≫ T.isoOfEq hpre.symm ≪≫
      (pullbackRestrictIsoRestrict i O).symm
  have hef : e.hom ≫ pullback.fst i O.ι = inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
      pullbackRestrictIsoRestrict_inv_fst, Scheme.isoOfEq_hom_ι]
  let r := e.hom ≫ pullback.snd i O.ι
  let : IsOpenImmersion r := inferInstance
  have hri : r ≫ O.ι = inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι ≫ i := by
    calc
      r ≫ O.ι = (e.hom ≫ pullback.fst i O.ι) ≫ i := by
        dsimp only [r]
        rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      _ = inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι ≫ i := by rw [hef, Category.assoc]
  have hβU : (inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι) ≫ β = U.ι := by
    rw [Category.assoc, ← AlgebraicGeometry.morphismRestrict_ι,
      IsIso.inv_hom_id_assoc]
  have hr : U.ι ≫ pX = r ≫ (O.ι ≫ pY) := by
    calc
      U.ι ≫ pX = (inv (β ∣_ U) ≫ (β ⁻¹ᵁ U).ι) ≫ β ≫ pX := by
        rw [← Category.assoc, hβU]
      _ = r ≫ (O.ι ≫ pY) := by
        rw [Category.assoc, ← h]
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ pY) hri.symm
  let q := QuasiDomination.baseChangeGraph i β pY pX h O.ι
  let G := e.hom ≫ q ≫ (pullbackSymmetry (O.ι ≫ pY) pX).hom
  have hGf : G ≫ pullback.fst pX (O.ι ≫ pY) = U.ι := by
    calc
      G ≫ pullback.fst pX (O.ι ≫ pY) =
          (e.hom ≫ pullback.fst i O.ι) ≫ β := by
        simp only [G, q, Category.assoc, pullbackSymmetry_hom_comp_fst,
          QuasiDomination.baseChangeGraph_snd]
      _ = U.ι := (congrArg (fun z ↦ z ≫ β) hef).trans hβU
  have hGs : G ≫ pullback.snd pX (O.ι ≫ pY) = r := by
    simp only [G, q, Category.assoc, pullbackSymmetry_hom_comp_snd,
      QuasiDomination.baseChangeGraph_fst]
    rfl
  have hG : pullback.lift U.ι r hr = G := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hGf.symm
    · exact (pullback.lift_snd _ _ _).trans hGs.symm
  let : IsClosedImmersion (pullback.lift U.ι r hr) := by
    rw [hG]
    infer_instance
  exact ⟨r, hr, inferInstance, hri, inferInstance,
    separated_desc U.ι r pX (O.ι ≫ pY) hr⟩

end AlgebraicGeometry.Scheme.SeparatedGluing

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianSourcePolygon
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianSourcePolygon
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceBaseChangeSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawIterationSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.InverseImageCompositionEq

/-! # The original inverse-image polygon for two given Cartesian squares -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Hom.DenseCompactification

universe u wX wX₁ wX₂ wL wL₂ wLI wLS
variable {X X₁ X₂ S T U : Scheme.{u}}
  (f : X ⟶ S) (f₁ : X₁ ⟶ T) (f₂ : X₂ ⟶ U)
  (b : T ⟶ S) (c : U ⟶ T) (a : X₁ ⟶ X) (d : X₂ ⟶ X₁)
  (sq₁ : IsPullback a f₁ f b) (sq₂ : IsPullback d f₂ f₁ c)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wL₂} (ModuleSheaf (pullback c f₁) Λ)]
  [HasDerivedCategory.{wLI} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [HasDerivedCategory.{wLS} (ModuleSheaf (pullback (c ≫ b) f) Λ)]

/-- The native source polygon follows from the original inverse-image compositor
associativity and actual universal source projections. All seven models are independent. -/
theorem moduleUnboundedCartesianBaseChangeSourceIso_pasting :
    let eb := pullbackSourceIso f₁ sq₁.flip.isoPullback sq₁.flip.isoPullback_hom_fst c
    let eBI := sq₂.flip.isoPullback ≪≫ eb
    let dTotal := eqToIso (congrArg
      (fun z : X₂ ⟶ pullback (c ≫ b) f => moduleUnboundedDerivedInverseImage Λ z)
      (congrArg Iso.hom
        (cartesianPresentation_isoPullback_pasting_sourceIso f f₁ f₂ b c a d sq₁ sq₂))) ≪≫
      moduleUnboundedDerivedInverseImageCompIso Λ (iteratedSourceIso (f := f) b c).hom eBI.hom
    cartesianPastingSourceIso
      (moduleUnboundedCartesianBaseChangeSourceIso f f₁ b a sq₁ Λ)
      (cartesianPastingTargetSourceIso
        (moduleUnboundedSourceBaseChangeSquareIso (pullback.fst b f) f₁ sq₁.flip.isoPullback
          sq₁.flip.isoPullback_hom_fst c Λ)
        (moduleUnboundedCartesianBaseChangeSourceIso f₁ f₂ c d sq₂ Λ)
        (moduleUnboundedDerivedInverseImageCompIso Λ eb.hom sq₂.flip.isoPullback.hom))
      ((moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f)
        (pullback.snd c (pullback.fst b f))).symm ≪≫ moduleUnboundedRawIterationSourceIso b c Λ)
      dTotal =
    (moduleUnboundedDerivedInverseImageCompIso Λ a d).symm ≪≫
      moduleUnboundedCartesianBaseChangeSourceIso f f₂ (c ≫ b) (d ≫ a) (sq₂.paste_horiz sq₁) Λ := by
  let e := sq₁.flip.isoPullback
  let j := sq₂.flip.isoPullback
  let k := pullbackSourceIso f₁ e sq₁.flip.isoPullback_hom_fst c
  let i := iteratedSourceIso (f := f) b c
  let t := (sq₂.paste_horiz sq₁).flip.isoPullback
  let p := pullback.snd b f
  let v := pullback.snd c (pullback.fst b f)
  let s := pullback.snd (c ≫ b) f
  let r := pullback.snd c f₁
  have ha : a = e.hom ≫ p := sq₁.flip.isoPullback_hom_snd.symm
  have hd : d = j.hom ≫ r := sq₂.flip.isoPullback_hom_snd.symm
  have hk : r ≫ e.hom = k.hom ≫ v :=
    (pullbackSourceIso_hom_snd f₁ e sq₁.flip.isoPullback_hom_fst c).symm
  have hi : v ≫ p = i.hom ≫ s := (iteratedSourceIso_hom_snd b c).symm
  have ht : t.hom = (j.hom ≫ k.hom) ≫ i.hom := congrArg Iso.hom
    (cartesianPresentation_isoPullback_pasting_sourceIso f f₁ f₂ b c a d sq₁ sq₂)
  have hn : d ≫ e.hom = (j.hom ≫ k.hom) ≫ v := by
    rw [hd, Category.assoc, hk, Category.assoc]
  have hm : d ≫ e.hom = j.hom ≫ (r ≫ e.hom) := by rw [hd, Category.assoc]
  have htotal : d ≫ a = (d ≫ e.hom) ≫ p := by rw [ha, Category.assoc]
  have htotal' : d ≫ a = (j.hom ≫ k.hom) ≫ (v ≫ p) := by
    rw [htotal, hn, Category.assoc]
  have htp : d ≫ a = t.hom ≫ s := (sq₂.paste_horiz sq₁).flip.isoPullback_hom_snd.symm
  let q₁ := moduleUnboundedDerivedInverseImageCompEqIso Λ p e.hom a ha
  let q₂ := moduleUnboundedDerivedInverseImageCompEqIso Λ r j.hom d hd
  let c₁ := moduleUnboundedDerivedInverseImageCompEqIso Λ e.hom r (r ≫ e.hom) rfl
  let c₂ := moduleUnboundedDerivedInverseImageCompEqIso Λ v k.hom (r ≫ e.hom) hk
  let dBI := moduleUnboundedDerivedInverseImageCompEqIso Λ k.hom j.hom (j.hom ≫ k.hom) rfl
  let L := moduleUnboundedDerivedInverseImageCompEqIso Λ e.hom d (d ≫ e.hom) rfl
  let R := moduleUnboundedDerivedInverseImageCompEqIso Λ v (j.hom ≫ k.hom) (d ≫ e.hom) hn
  let E := moduleUnboundedDerivedInverseImageCompEqIso Λ (r ≫ e.hom) j.hom (d ≫ e.hom) hm
  have h₁ := moduleUnboundedDerivedInverseImageCompEqIso_assoc Λ e.hom r j.hom
    (r ≫ e.hom) d (d ≫ e.hom) rfl hd rfl hm
  have h₂ := moduleUnboundedDerivedInverseImageCompEqIso_assoc Λ v k.hom j.hom
    (r ≫ e.hom) (j.hom ≫ k.hom) (d ≫ e.hom) hk rfl hn hm
  let B := moduleUnboundedDerivedInverseImageCompEqIso Λ p (d ≫ e.hom) (d ≫ a) htotal
  let C := moduleUnboundedDerivedInverseImageCompEqIso Λ (v ≫ p) (j.hom ≫ k.hom)
    (d ≫ a) htotal'
  let δ := moduleUnboundedDerivedInverseImageCompEqIso Λ p v (v ≫ p) rfl
  let η := moduleUnboundedDerivedInverseImageCompEqIso Λ s i.hom (v ≫ p) hi
  let δt := moduleUnboundedDerivedInverseImageCompEqIso Λ a d (d ≫ a) rfl
  let ηt := moduleUnboundedDerivedInverseImageCompEqIso Λ s t.hom (d ≫ a) htp
  let D := moduleUnboundedDerivedInverseImageCompEqIso Λ i.hom (j.hom ≫ k.hom) t.hom ht
  have hA := moduleUnboundedDerivedInverseImageCompEqIso_assoc Λ p e.hom d
    a (d ≫ e.hom) (d ≫ a) ha rfl htotal rfl
  have hB := moduleUnboundedDerivedInverseImageCompEqIso_assoc Λ p v (j.hom ≫ k.hom)
    (v ≫ p) (d ≫ e.hom) (d ≫ a) rfl hn htotal htotal'
  have hC := moduleUnboundedDerivedInverseImageCompEqIso_assoc Λ s i.hom (j.hom ≫ k.hom)
    (v ≫ p) t.hom (d ≫ a) hi ht htp htotal'
  have hξ := cartesianPastingTargetSourceIso_of_assoc c₁ c₂ q₂ dBI L R E h₁ h₂
  have hρ := cartesianPastingSourceIso_of_assoc B C L R δ η δt ηt q₁ D hA hB hC
  rw [← hξ] at hρ
  simpa only [q₁, q₂, c₁, c₂, dBI, δ, η, δt, ηt, D,
    moduleUnboundedDerivedInverseImageCompEqIso, eqToIso_refl, Iso.refl_trans,
    moduleUnboundedCartesianBaseChangeSourceIso, moduleUnboundedSourceBaseChangeSquareIso,
    moduleUnboundedRawSourceBaseChangeSourceIso, moduleUnboundedRawIterationSourceIso,
    sourceBaseChangeIso, e, j, k, i, t, p, v, s, r, Iso.trans_hom] using hρ

end AlgebraicGeometry.Scheme.EtaleCohomology

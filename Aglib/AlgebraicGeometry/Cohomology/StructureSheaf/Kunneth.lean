/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenAffine
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenTop
public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris
public import Aglib.AlgebraicGeometry.Properties.AffineInduction

/-!
# Original global Künneth bijectivity for qcqs schemes over a field

Affine induction is applied to original open-immersion ranges in ONE fixed
ambient second factor. No positive-degree comparison theorem on another
scheme is transported into the mixed map. The resulting TOP map is then
identified with the literal original antidiagonal kappa.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (X Y : FScheme k)
  [QuasiCompact X.hom] [QuasiSeparated X.hom]

/-- All mixed-open maps on a fixed ambient qcqs second factor are bijective. -/
theorem structureOpenKunnethMap_bijective_of_qcqs
    [QuasiCompact Y.hom] [QuasiSeparated Y.hom] :
    ∀ (U : Y.left.Opens), IsCompact (U : Set Y.left) →
      ∀ n, Function.Bijective (structureOpenKunnethMap X Y U n) := by
  let C : Y.left.Opens → Prop := fun U =>
    ∀ n, Function.Bijective (structureOpenKunnethMap X Y U n)
  let P : Scheme.{u} → Prop := fun T =>
    ∀ (j : T ⟶ Y.left) [IsOpenImmersion j], C j.opensRange
  have hIso : ∀ {T T' : Scheme.{u}} (e : T ≅ T'), P T → P T' := by
    intro T T' e hT j hj
    let jT := e.hom ≫ j
    have hr : jT.opensRange = j.opensRange := by
      ext y
      change (∃ x, j (e.hom x) = y) ↔ ∃ x, j x = y
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨e.hom x, hx⟩
      · rintro ⟨x, hx⟩
        refine ⟨e.inv x, ?_⟩
        have he := congrArg (fun f : T' ⟶ T' => f x) e.inv_hom_id
        change e.hom (e.inv x) = x at he
        exact (congrArg j he).trans hx
    simpa only [hr] using hT jT
  have hAffine : ∀ (T : Scheme.{u}) [IsAffine T], P T := by
    intro T hT j hj n
    exact structureOpenKunnethMap_bijective_of_isAffineOpen X Y j.opensRange
      (isAffineOpen_opensRange j) n
  have hUnion : ∀ {T : Scheme.{u}} [QuasiSeparatedSpace T] (U V : T.Opens),
      IsCompact (U : Set T) → IsCompact (V : Set T) →
      P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P (U ⊔ V).toScheme := by
    intro T hT U V hU hV hPU hPV hPI j hj
    let fU : U.toScheme ⟶ (U ⊔ V).toScheme := T.homOfLE le_sup_left
    let fV : V.toScheme ⟶ (U ⊔ V).toScheme := T.homOfLE le_sup_right
    let fI : (U ⊓ V).toScheme ⟶ (U ⊔ V).toScheme :=
      T.homOfLE (inf_le_left.trans le_sup_left)
    let jU := fU ≫ j
    let jV := fV ≫ j
    let jI := fI ≫ j
    have hSup : jU.opensRange ⊔ jV.opensRange = j.opensRange := by
      ext y
      change ((∃ x : U.toScheme, j (fU x) = y) ∨
        (∃ x : V.toScheme, j (fV x) = y)) ↔ ∃ x : (U ⊔ V).toScheme, j x = y
      constructor
      · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
        · exact ⟨fU x, hx⟩
        · exact ⟨fV x, hx⟩
      · rintro ⟨x, hx⟩
        rcases x.property with hxU | hxV
        · left
          refine ⟨⟨x.val, hxU⟩, ?_⟩
          have he : fU ⟨x.val, hxU⟩ = x := by
            apply Subtype.ext
            simp only [fU, Scheme.homOfLE_apply]
          exact (congrArg j he).trans hx
        · right
          refine ⟨⟨x.val, hxV⟩, ?_⟩
          have he : fV ⟨x.val, hxV⟩ = x := by
            apply Subtype.ext
            simp only [fV, Scheme.homOfLE_apply]
          exact (congrArg j he).trans hx
    have hInf : jU.opensRange ⊓ jV.opensRange = jI.opensRange := by
      ext y
      change ((∃ x : U.toScheme, j (fU x) = y) ∧
        (∃ x : V.toScheme, j (fV x) = y)) ↔ ∃ x : (U ⊓ V).toScheme, j (fI x) = y
      constructor
      · rintro ⟨⟨x, hx⟩, ⟨z, hz⟩⟩
        have he : fU x = fV z := j.isOpenEmbedding.injective (hx.trans hz.symm)
        have he' : x.val = z.val := by
          have h := congrArg Subtype.val he
          simpa only [fU, fV, Scheme.homOfLE_apply] using h
        refine ⟨⟨x.val, x.property, he'.symm ▸ z.property⟩, ?_⟩
        have hi : fI ⟨x.val, x.property, he'.symm ▸ z.property⟩ = fU x := by
          apply Subtype.ext
          simp only [fI, fU, Scheme.homOfLE_apply]
        exact (congrArg j hi).trans hx
      · rintro ⟨x, hx⟩
        constructor
        · refine ⟨⟨x.val, x.property.1⟩, ?_⟩
          have hi : fU ⟨x.val, x.property.1⟩ = fI x := by
            apply Subtype.ext
            simp only [fU, fI, Scheme.homOfLE_apply]
          exact (congrArg j hi).trans hx
        · refine ⟨⟨x.val, x.property.2⟩, ?_⟩
          have hi : fV ⟨x.val, x.property.2⟩ = fI x := by
            apply Subtype.ext
            simp only [fV, fI, Scheme.homOfLE_apply]
          exact (congrArg j hi).trans hx
    have hI : C (jU.opensRange ⊓ jV.opensRange) := by
      rw [hInf]
      exact hPI jI
    have h := structureOpenKunnethMap_bijective_sup X Y jU.opensRange jV.opensRange
      (hPU jU) (hPV jV) hI
    rwa [hSup] at h
  let : CompactSpace Y.left := (quasiCompact_iff_compactSpace Y.hom).mp inferInstance
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  intro U hU n
  have hP := Scheme.AffineInduction.of_compactOpen P hIso hAffine hUnion U hU
  have hC : C U.ι.opensRange := hP U.ι
  have hCU : C U := Eq.mp (congrArg C (Scheme.Opens.opensRange_ι U)) hC
  exact hCU n

/-- The original finite-antidiagonal kappa is bijective in every degree for qcqs factors. -/
theorem structureKunnethMap_bijective [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (n : ℕ) :
    Function.Bijective (structureKunnethMap X Y n) := by
  let : CompactSpace Y.left := (quasiCompact_iff_compactSpace Y.hom).mp inferInstance
  apply structureKunnethMap_bijective_of_openTop X Y n
  exact structureOpenKunnethMap_bijective_of_qcqs X Y ⊤ isCompact_univ n

end AlgebraicGeometry.Scheme.Cohomology

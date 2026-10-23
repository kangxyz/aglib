/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PurelyInseparable.Stages

/-! # Morphism descent across arbitrary purely inseparable field extensions -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every map between actual base-changed finite-etale covers descends.
There is no finite-degree hypothesis on the purely inseparable extension. -/
theorem specBaseChange_full : (baseChange (Spec.algebraMap K L)).Full where
  map_surjective {Y Z} q := by
    let f := Spec.algebraMap K L
    let W := (Over.pullback Y.obj.hom).obj Z.obj
    have : CompactSpace Y.obj.left :=
      QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
    have : QuasiSeparatedSpace Y.obj.left :=
      quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
    have : LocallyOfFinitePresentation W.hom :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Z.obj.hom Y.obj.hom))
    let q₀ : pullback Y.obj.hom f ⟶ pullback Z.obj.hom f := q.hom.left
    have hq₀ : q₀ ≫ pullback.snd Z.obj.hom f = pullback.snd Y.obj.hom f :=
      Over.w q.hom
    let r : pullback Y.obj.hom f ⟶ W.left := pullback.lift
      (q₀ ≫ pullback.fst Z.obj.hom f) (pullback.fst Y.obj.hom f) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hq₀]
        exact (pullback.condition (f := Y.obj.hom) (g := f)).symm)
    obtain ⟨s, g, hg, hr⟩ := FieldLimit.exists_finite_field_hom K L Y.obj.hom W r
      (pullback.lift_snd _ _ _)
    let F := FieldLimit.finiteField K L s.unop
    let fs := Spec.algebraMap K F
    let e := pullbackSymmetry Y.obj.hom fs
    have hg' : g ≫ pullback.snd Z.obj.hom Y.obj.hom =
        pullback.snd fs Y.obj.hom := hg
    let a : (baseChange fs).obj Y ⟶ (baseChange fs).obj Z := ObjectProperty.homMk
      (Over.homMk (pullback.lift (e.hom ≫ g ≫ pullback.fst Z.obj.hom Y.obj.hom)
        (pullback.snd Y.obj.hom fs) (by
          change (e.hom ≫ g ≫ pullback.fst Z.obj.hom Y.obj.hom) ≫ Z.obj.hom =
            pullback.snd Y.obj.hom fs ≫ fs
          rw [Category.assoc, Category.assoc, pullback.condition,
            ← Category.assoc g, hg', ← Category.assoc e.hom]
          simp only [e, pullbackSymmetry_hom_comp_snd, pullback.condition]))
        (pullback.lift_snd _ _ _))
    let : (baseChange fs).IsEquivalence := finiteSpecBaseChange_isEquivalence K F
    obtain ⟨h, hh⟩ := (baseChange fs).map_surjective a
    have hs : pullback.snd fs Y.obj.hom ≫ h.hom.left =
        g ≫ pullback.fst Z.obj.hom Y.obj.hom := by
      have H : pullback.fst Y.obj.hom fs ≫ h.hom.left =
          e.hom ≫ g ≫ pullback.fst Z.obj.hom Y.obj.hom := by
        calc
          _ = ((baseChange fs).map h).hom.left ≫ pullback.fst Z.obj.hom fs :=
            (pullback.lift_fst _ _ _).symm
          _ = a.hom.left ≫ pullback.fst Z.obj.hom fs :=
            congrArg (fun k ↦ k.hom.left ≫ pullback.fst Z.obj.hom fs) hh
          _ = _ := pullback.lift_fst _ _ _
      calc
        _ = (e.inv ≫ pullback.fst Y.obj.hom fs) ≫ h.hom.left := by
          rw [show e.inv ≫ pullback.fst Y.obj.hom fs = pullback.snd fs Y.obj.hom
            from pullbackSymmetry_inv_comp_fst _ _]
        _ = e.inv ≫ (e.hom ≫ g ≫ pullback.fst Z.obj.hom Y.obj.hom) := by
          rw [Category.assoc, H]
        _ = _ := e.inv_hom_id_assoc _
    refine ⟨h, ?_⟩
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change ((Over.pullback f).map h.hom).left ≫ pullback.fst Z.obj.hom f = _
      simp only [Over.pullback_map_left, pullback.lift_fst]
      have hb := FieldLimit.fieldProjection_base K L Y.obj.hom s
      change FieldLimit.fieldProjection K L Y.obj.hom s ≫
        pullback.snd fs Y.obj.hom = pullback.fst Y.obj.hom f at hb
      calc
        pullback.fst Y.obj.hom f ≫ h.hom.left =
            (FieldLimit.fieldProjection K L Y.obj.hom s ≫
              pullback.snd fs Y.obj.hom) ≫ h.hom.left := by rw [hb]
        _ = FieldLimit.fieldProjection K L Y.obj.hom s ≫
            (g ≫ pullback.fst Z.obj.hom Y.obj.hom) := by rw [Category.assoc, hs]
        _ = r ≫ pullback.fst Z.obj.hom Y.obj.hom := by rw [← Category.assoc, hr]
        _ = q.hom.left ≫ pullback.fst Z.obj.hom f := by simp [r, q₀]
    · exact (Over.w ((baseChange f).map h).hom).trans (Over.w q.hom).symm

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

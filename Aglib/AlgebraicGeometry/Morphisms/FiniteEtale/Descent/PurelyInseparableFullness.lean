/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license aF described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FieldLimit

/-! # Finite-etale morphism descent over a purely inseparable field extension

Every morphism of the actual base-changed covers descends to a finite field
stage. Finite purely inseparable invariance then descends it to the original
scheme. The extension need not be finite, and the base need only be qcqs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal finite-etale pullback along the first projection is full for
an arbitrary purely inseparable field extension and a qcqs scheme over the field. -/
theorem projectionBaseChange_full {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (p : X ⟶ Spec (.of K)) :
    (baseChange (pullback.fst p (Spec.algebraMap K L))).Full where
  map_surjective {Y Z} q := by
    let a := Spec.algebraMap K L
    let f := pullback.fst p a
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
    let eY := pullbackRightPullbackFstIso p a Y.obj.hom
    have heY : eY.hom ≫ pullback.fst (Y.obj.hom ≫ p) a =
        pullback.fst Y.obj.hom f := pullbackRightPullbackFstIso_hom_fst p a Y.obj.hom
    let r : pullback (Y.obj.hom ≫ p) a ⟶ W.left := pullback.lift
      (eY.inv ≫ q₀ ≫ pullback.fst Z.obj.hom f)
      (pullback.fst (Y.obj.hom ≫ p) a) (by
        rw [Category.assoc, Category.assoc, pullback.condition,
          ← Category.assoc q₀, hq₀]
        exact pullbackRightPullbackFstIso_inv_snd_fst p a Y.obj.hom)
    obtain ⟨s, g, hg, hr⟩ := FieldLimit.exists_finite_field_hom K L
      (Y.obj.hom ≫ p) W r (pullback.lift_snd _ _ _)
    let F := FieldLimit.finiteField K L s.unop
    let aF := Spec.algebraMap K F
    let fs := pullback.fst p aF
    let e := pullbackRightPullbackFstIso p aF Y.obj.hom ≪≫
      pullbackSymmetry (Y.obj.hom ≫ p) aF
    have he : e.hom ≫ pullback.snd aF (Y.obj.hom ≫ p) =
        pullback.fst Y.obj.hom fs := by
      simp only [e, fs, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
        pullbackRightPullbackFstIso_hom_fst]
    have he_inv : e.inv ≫ pullback.fst Y.obj.hom fs =
        pullback.snd aF (Y.obj.hom ≫ p) := by
      rw [← he]
      exact e.inv_hom_id_assoc _
    have hg' : g ≫ pullback.snd Z.obj.hom Y.obj.hom =
        pullback.snd aF (Y.obj.hom ≫ p) := hg
    let qF : (baseChange fs).obj Y ⟶ (baseChange fs).obj Z := ObjectProperty.homMk
      (Over.homMk (pullback.lift (e.hom ≫ g ≫ pullback.fst Z.obj.hom Y.obj.hom)
        (pullback.snd Y.obj.hom fs) (by
          change (e.hom ≫ g ≫ pullback.fst Z.obj.hom Y.obj.hom) ≫ Z.obj.hom =
            pullback.snd Y.obj.hom fs ≫ fs
          rw [Category.assoc, Category.assoc, pullback.condition,
            ← Category.assoc g, hg', ← Category.assoc e.hom, he, pullback.condition]))
        (pullback.lift_snd _ _ _))
    let : (baseChange fs).IsEquivalence := Global.finitePureBaseChange_isEquivalence K F p
    obtain ⟨h, hh⟩ := (baseChange fs).map_surjective qF
    have hs : pullback.snd aF (Y.obj.hom ≫ p) ≫ h.hom.left =
        g ≫ pullback.fst Z.obj.hom Y.obj.hom := by
      have H : pullback.fst Y.obj.hom fs ≫ h.hom.left =
          e.hom ≫ g ≫ pullback.fst Z.obj.hom Y.obj.hom := by
        calc
          _ = ((baseChange fs).map h).hom.left ≫ pullback.fst Z.obj.hom fs :=
            (pullback.lift_fst _ _ _).symm
          _ = qF.hom.left ≫ pullback.fst Z.obj.hom fs :=
            congrArg (fun k ↦ k.hom.left ≫ pullback.fst Z.obj.hom fs) hh
          _ = _ := pullback.lift_fst _ _ _
      calc
        _ = (e.inv ≫ pullback.fst Y.obj.hom fs) ≫ h.hom.left := by rw [he_inv]
        _ = e.inv ≫ (e.hom ≫ g ≫ pullback.fst Z.obj.hom Y.obj.hom) := by
          rw [Category.assoc, H]
        _ = _ := e.inv_hom_id_assoc _
    refine ⟨h, ?_⟩
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change ((Over.pullback f).map h.hom).left ≫ pullback.fst Z.obj.hom f = _
      simp only [Over.pullback_map_left, pullback.lift_fst]
      have hb := FieldLimit.fieldProjection_base K L (Y.obj.hom ≫ p) s
      change FieldLimit.fieldProjection K L (Y.obj.hom ≫ p) s ≫
        pullback.snd aF (Y.obj.hom ≫ p) = pullback.fst (Y.obj.hom ≫ p) a at hb
      calc
        pullback.fst Y.obj.hom f ≫ h.hom.left =
            (eY.hom ≫ (FieldLimit.fieldProjection K L (Y.obj.hom ≫ p) s ≫
              pullback.snd aF (Y.obj.hom ≫ p))) ≫ h.hom.left := by rw [hb, heY]
        _ = eY.hom ≫ FieldLimit.fieldProjection K L (Y.obj.hom ≫ p) s ≫
            (g ≫ pullback.fst Z.obj.hom Y.obj.hom) := by
          simp only [Category.assoc]
          rw [hs]
        _ = eY.hom ≫ r ≫ pullback.fst Z.obj.hom Y.obj.hom := by
          rw [← Category.assoc (FieldLimit.fieldProjection K L (Y.obj.hom ≫ p) s), hr]
        _ = q.hom.left ≫ pullback.fst Z.obj.hom f := by simp [r, q₀]
    · exact (Over.w ((baseChange f).map h).hom).trans (Over.w q.hom).symm

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

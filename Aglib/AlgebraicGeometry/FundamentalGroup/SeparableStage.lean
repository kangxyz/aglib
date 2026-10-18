/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureDescent
public import Aglib.AlgebraicGeometry.FundamentalGroup.KernelFiniteStage
public import Mathlib.RingTheory.Etale.Field

/-!
# Passing a finite field-stage cover to its maximal separable subfield

The original finite purely inseparable base-change equivalence is applied to
the maximal separable subfield. All comparison maps are actual pullback maps.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange mk)

namespace AlgebraicGeometry.Scheme.FiniteEtale.SeparableStage

universe u
variable (K S E : Type u) [Field K] [Field S] [Field E]
  [Algebra K S] [Algebra S E] [Algebra K E] [IsScalarTower K S E]

theorem specTower : Spec.algebraMap S E ≫ Spec.algebraMap K S = Spec.algebraMap K E := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq K S E).symm

variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))

/-- The canonical isomorphism from successive base changes along `K → S → E` to base change
along `K → E` . -/
def towerIso :
    pullback (pullback.snd p (Spec.algebraMap K S)) (Spec.algebraMap S E) ≅
      pullback p (Spec.algebraMap K E) :=
  pullbackLeftPullbackSndIso p (Spec.algebraMap K S) (Spec.algebraMap S E) ≪≫
    pullback.congrHom rfl (specTower K S E)

/-- The projection from the `E` -base change of `X` to its `S` -base change in the given field
tower. -/
def extensionProjection : pullback p (Spec.algebraMap K E) ⟶
    pullback p (Spec.algebraMap K S) :=
  (towerIso K S E p).inv ≫
    pullback.fst (pullback.snd p (Spec.algebraMap K S)) (Spec.algebraMap S E)

theorem towerIso_hom_base :
    (towerIso K S E p).hom ≫ pullback.fst p (Spec.algebraMap K E) =
      pullback.fst (pullback.snd p (Spec.algebraMap K S)) (Spec.algebraMap S E) ≫
        pullback.fst p (Spec.algebraMap K S) := by
  simp only [towerIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.map, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

@[reassoc] theorem extensionProjection_base :
    extensionProjection K S E p ≫ pullback.fst p (Spec.algebraMap K S) =
      pullback.fst p (Spec.algebraMap K E) := by
  dsimp only [extensionProjection]
  rw [Category.assoc, ← towerIso_hom_base, Iso.inv_hom_id_assoc]

/-- Actual base change along the tower projection is an equivalence when the
upper field extension is finite purely inseparable. -/
theorem extensionProjection_isEquivalence [IsPurelyInseparable S E] [Module.Finite S E] :
    (baseChange (extensionProjection K S E p)).IsEquivalence := by
  let : (baseChange (pullback.fst (pullback.snd p (Spec.algebraMap K S))
      (Spec.algebraMap S E))).IsEquivalence :=
    PurelyInseparable.Global.finitePureBaseChange_isEquivalence S E
      (pullback.snd p (Spec.algebraMap K S))
  apply PurelyInseparable.Global.baseChange_isEquivalence_of_isoSquare
    (towerIso K S E p) (Iso.refl _) (extensionProjection K S E p)
    (pullback.fst (pullback.snd p (Spec.algebraMap K S)) (Spec.algebraMap S E))
  change (towerIso K S E p).hom ≫ ((towerIso K S E p).inv ≫ _) = _ ≫ 𝟙 _
  rw [Iso.hom_inv_id_assoc, Category.comp_id]

section FiniteSeparable
variable [Module.Finite K S] [Algebra.IsSeparable K S]

/-- The spectrum of the finite separable extension `S/K` , as a finite étale scheme over
`Spec K` . -/
def finiteSeparableFieldCover : Scheme.FiniteEtale (Spec (CommRingCat.of K)) := by
  let : Algebra.FormallyEtale K S := Algebra.FormallyEtale.of_isSeparable K S
  let : Algebra.FinitePresentation K S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale K S := { }
  let : IsFinite (Spec.algebraMap K S) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : Etale (Spec.algebraMap K S) :=
    (HasRingHomProperty.Spec_iff (P := @Etale.{u})).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  exact mk (Spec.algebraMap K S)

theorem stageProjection_finite : IsFinite (pullback.fst p (Spec.algebraMap K S)) := by
  let : IsFinite (Spec.algebraMap K S) := (finiteSeparableFieldCover K S).property.1
  infer_instance

theorem stageProjection_etale : Etale (pullback.fst p (Spec.algebraMap K S)) := by
  let : Etale (Spec.algebraMap K S) := (finiteSeparableFieldCover K S).property.2
  infer_instance

end FiniteSeparable

section MaximalSeparable
variable [Module.Finite K E]

/-- The maximal separable subfield supplies an actual finite étale stage. -/
def maximalSeparableEquivalence :
    Scheme.FiniteEtale (pullback p (Spec.algebraMap K (separableClosure K E))) ≌
      Scheme.FiniteEtale (pullback p (Spec.algebraMap K E)) := by
  let : (baseChange (extensionProjection K (separableClosure K E) E p)).IsEquivalence :=
    extensionProjection_isEquivalence K (separableClosure K E) E p
  exact (baseChange (extensionProjection K (separableClosure K E) E p)).asEquivalence

/-- The model of `Y` over the maximal separable subfield, chosen by the inverse descent
equivalence. -/
def maximalSeparableModel (Y : Scheme.FiniteEtale (pullback p (Spec.algebraMap K E))) :
    Scheme.FiniteEtale (pullback p (Spec.algebraMap K (separableClosure K E))) :=
  (maximalSeparableEquivalence K E p).inverse.obj Y

/-- The counit isomorphism identifying base change of the maximal separable model with `Y` . -/
def maximalSeparableModelIso (Y : Scheme.FiniteEtale (pullback p (Spec.algebraMap K E))) :
    (baseChange (extensionProjection K (separableClosure K E) E p)).obj
      (maximalSeparableModel K E p Y) ≅ Y :=
  (maximalSeparableEquivalence K E p).counitIso.app Y

end MaximalSeparable
end AlgebraicGeometry.Scheme.FiniteEtale.SeparableStage

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 193a50e2830e9403ee0e61b3483fd875a9cc500c354c979368bba9eadee7b5b7.
Definitions, hypotheses and universes are retained modulo native names. -/

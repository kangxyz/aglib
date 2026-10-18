/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.FiniteStageField

/-!
# StageFieldNaturality

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel
universe u

section FieldStage
variable (K S Ω : Type u) [Field K] [Field S] [Field Ω]
  [Algebra K S] [Module.Finite K S] [Algebra.IsSeparable K S]
  [Algebra K Ω] [Algebra S Ω] [IsScalarTower K S Ω] [Algebra.IsAlgebraic S Ω]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (CommRingCat.of K)) (o : Spec (CommRingCat.of K) ⟶ X)
  (ho : o ≫ p = 𝟙 _)

/-- The fibre point of the finite separable field cover induced by the compatible inclusion of
`S` into `Ω`. -/
abbrev towerPoint : Fiber (Spec.algebraMap K Ω) (SeparableStage.finiteSeparableFieldCover K S) :=
  Over.homMk (Spec.algebraMap S Ω) (SeparableStage.specTower K S Ω)

/-- At a finite separable field stage, the kernel action commutes with every
geometric arrow, including arrows that appear only after extending to Ω. -/
theorem fieldStage_action_naturality
    (n : ProjectionKernel (Spec.algebraMap K Ω) p o ho)
    (A B : Scheme.FiniteEtale ((baseChange p).obj (SeparableStage.finiteSeparableFieldCover K
      S)).obj.left)
    (γ : (baseChange (geometricStageRight (Spec.algebraMap K Ω) p
      (SeparableStage.finiteSeparableFieldCover K S) (towerPoint K S Ω))).obj A ⟶
      (baseChange (geometricStageRight (Spec.algebraMap K Ω) p
        (SeparableStage.finiteSeparableFieldCover K S) (towerPoint K S Ω))).obj B)
    (z : Fiber (baseChangePoint (Spec.algebraMap K Ω) p o ho)
      ((baseChange (geometricStageRight (Spec.algebraMap K Ω) p
        (SeparableStage.finiteSeparableFieldCover K S) (towerPoint K S Ω))).obj A)) :
    (fiberToFinite (baseChangePoint (Spec.algebraMap K Ω) p o ho)).map γ
      (ModelActions.action (geometricStage (Spec.algebraMap K Ω) p o ho
        (SeparableStage.finiteSeparableFieldCover K S) (towerPoint K S Ω))
        (kernelStageAut (Spec.algebraMap K Ω) p o ho n
          (SeparableStage.finiteSeparableFieldCover K S) (towerPoint K S Ω)) A z) =
      ModelActions.action (geometricStage (Spec.algebraMap K Ω) p o ho
        (SeparableStage.finiteSeparableFieldCover K S) (towerPoint K S Ω))
        (kernelStageAut (Spec.algebraMap K Ω) p o ho n
          (SeparableStage.finiteSeparableFieldCover K S) (towerPoint K S Ω)) B
        ((fiberToFinite (baseChangePoint (Spec.algebraMap K Ω) p o ho)).map γ z) := by
  let b := Spec.algebraMap K Ω
  let Z := SeparableStage.finiteSeparableFieldCover K S
  let q := towerPoint K S Ω
  let T := ((baseChange p).obj Z).obj.left
  let pS : T ⟶ Spec (CommRingCat.of S) := pullback.fst Z.obj.hom p
  let x := stagePoint b p o ho Z q
  have hx : x ≫ pS = Spec.algebraMap S Ω := stagePoint_to_base b p o ho Z q
  let a := kernelStageAut b p o ho n Z q
  have ha : pointedMap (PointedField.projection pS x hx) a = 1 :=
    kernelStageAut_projection b p o ho Z q n
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace ((baseChange p).obj Z).obj.hom
  have : QuasiSeparatedSpace T :=
    quasiSeparatedSpace_of_quasiSeparated ((baseChange p).obj Z).obj.hom
  let e := geometricStagePullbackIso b p Z q
  let i : Under.mk (baseChangePoint b p o ho) ⟶ Under.mk (PointedField.geometricPoint pS x hx) :=
    Under.homMk e.hom (by
      apply pullback.hom_ext
      · exact (Category.assoc _ _ _).trans
          ((congrArg (fun t ↦ baseChangePoint b p o ho ≫ t)
            (geometricStagePullbackIso_fst b p Z q)).trans
              ((Under.w (geometricStage b p o ho Z q)).trans (pullback.lift_fst _ _ _).symm))
      · exact (Category.assoc _ _ _).trans
          ((congrArg (fun t ↦ baseChangePoint b p o ho ≫ t)
            (geometricStagePullbackIso_snd b p Z q)).trans
              ((baseChangePoint_snd b p o ho).trans (pullback.lift_snd _ _ _).symm)))
  have : IsIso i.right := inferInstanceAs (IsIso e.hom)
  have hi : geometricStage b p o ho Z q = i ≫ PointedField.inclusion pS x hx :=
    Under.UnderMorphism.ext (geometricStagePullbackIso_fst b p Z q).symm
  exact ModelActions.source_change_naturality i (PointedField.inclusion pS x hx)
    (geometricStage b p o ho Z q) hi a (PointedField.action_naturality pS x hx a ha) A B γ z

end FieldStage

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 909e4ed71ff4689bd3ba4b54fd925f80d41b7e7a98d1856aef4fce5a6c116a27.
Definitions, hypotheses and universes are retained modulo native names. -/

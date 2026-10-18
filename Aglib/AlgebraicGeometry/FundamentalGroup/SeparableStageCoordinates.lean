/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.SeparableStage
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FieldLimit

/-!
# SeparableStageCoordinates

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.SeparableStage
universe u
variable (K S E : Type u) [Field K] [Field S] [Field E]
  [Algebra K S] [Algebra S E] [Algebra K E] [IsScalarTower K S E]
  {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))

theorem towerIso_hom_field :
    (towerIso K S E p).hom ≫ pullback.snd p (Spec.algebraMap K E) =
      pullback.snd (pullback.snd p (Spec.algebraMap K S)) (Spec.algebraMap S E) := by
  simp only [towerIso, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
    pullback.map, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

@[reassoc] theorem extensionProjection_field :
    extensionProjection K S E p ≫ pullback.snd p (Spec.algebraMap K S) =
      pullback.snd p (Spec.algebraMap K E) ≫ Spec.algebraMap S E := by
  dsimp only [extensionProjection]
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    ← towerIso_hom_field, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.FiniteEtale.SeparableStage

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldLimit
universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))

@[reassoc] theorem fieldProjection_field (s : (Finset Ω)ᵒᵖ) :
    fieldProjection K Ω p s ≫
        pullback.fst (Spec.algebraMap K (finiteField K Ω s.unop)) p =
      pullback.snd p (Spec.algebraMap K Ω) ≫
        Spec.map (CommRingCat.ofHom (finiteField K Ω s.unop).val.toRingHom) := by
  change ((pullbackSymmetry p (Spec.algebraMap K Ω)).hom ≫
      ((Over.pullback p).map ((fieldCone K Ω).π.app s)).left) ≫
        pullback.fst (Spec.algebraMap K (finiteField K Ω s.unop)) p = _
  rw [Category.assoc]
  have hf : ((Over.pullback p).map ((fieldCone K Ω).π.app s)).left ≫
      pullback.fst (Spec.algebraMap K (finiteField K Ω s.unop)) p =
    pullback.fst (Spec.algebraMap K Ω) p ≫
      Spec.map (CommRingCat.ofHom (finiteField K Ω s.unop).val.toRingHom) :=
    pullback.lift_fst _ _ _
  rw [hf, ← Category.assoc, pullbackSymmetry_hom_comp_fst]

end AlgebraicGeometry.Scheme.FiniteEtale.FieldLimit

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 9de44b38cc58e6ee294be71c308123261b29e4be3138f1a3c195b201a379e6a9.
Definitions, hypotheses and universes are retained modulo native names. -/

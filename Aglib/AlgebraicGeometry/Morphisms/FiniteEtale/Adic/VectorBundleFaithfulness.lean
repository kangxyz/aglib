/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.VectorBundleFullness

/-! # Detecting finite-etale maps through the original scalar section cone

First-stage equality determines the original maps at every nilpotent stage.
The original finite locally free structure modules and their quotient units
then detect the global map. No coherent-completion faithfulness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

variable {X : Scheme.{u}} (K : X.IdealSheafData)

/-- Equality on the first thickening determines every actual finite-etale restriction. -/
theorem baseChange_map_eq_of_first {C D : FiniteEtale X} {f g : C ⟶ D}
    (h : (baseChange (K ^ 1).subschemeι).map f =
      (baseChange (K ^ 1).subschemeι).map g) (n : ℕ) :
    (baseChange (K ^ n).subschemeι).map f =
      (baseChange (K ^ n).subschemeι).map g := by
  cases n with
  | zero =>
    let e := baseChangeComp (K ^ 1).subschemeι (stageMap K (Nat.zero_le 1))
    have hh : (baseChange (K ^ 1).subschemeι ⋙
        baseChange (stageMap K (Nat.zero_le 1))).map f =
        (baseChange (K ^ 1).subschemeι ⋙
        baseChange (stageMap K (Nat.zero_le 1))).map g :=
      congrArg (fun k => (baseChange (stageMap K (Nat.zero_le 1))).map k) h
    have he : (baseChange (stageMap K (Nat.zero_le 1) ≫ (K ^ 1).subschemeι)).map f =
        (baseChange (stageMap K (Nat.zero_le 1) ≫ (K ^ 1).subschemeι)).map g := by
      apply (cancel_mono (e.hom.app D)).mp
      rw [e.hom.naturality f, e.hom.naturality g, hh]
    rw [stageMap_ι K (Nat.zero_le 1)] at he
    exact he
  | succ n =>
    let j := stageMap K (Nat.succ_le_succ (Nat.zero_le n))
    let : (baseChange j).IsEquivalence :=
      stageMap_baseChange_isEquivalence K (Nat.succ_le_succ (Nat.zero_le n)) (by decide)
    apply (baseChange j).map_injective
    let e := baseChangeComp (K ^ (n + 1)).subschemeι j
    have hh : (baseChange (j ≫ (K ^ (n + 1)).subschemeι)).map f =
        (baseChange (j ≫ (K ^ (n + 1)).subschemeι)).map g := by
      rw [show j ≫ (K ^ (n + 1)).subschemeι = (K ^ 1).subschemeι from
        stageMap_ι K (Nat.succ_le_succ (Nat.zero_le n))]
      exact h
    apply (cancel_epi (e.hom.app C)).mp
    change e.hom.app C ≫ (baseChange (K ^ (n + 1)).subschemeι ⋙
      baseChange j).map f = e.hom.app C ≫
        (baseChange (K ^ (n + 1)).subschemeι ⋙ baseChange j).map g
    rw [← e.hom.naturality f, ← e.hom.naturality g, hh]

open Modules Modules.Coherent

variable [IsLocallyNoetherian X] [X.IsQuasiAffine]
  (hunit : IsLimit (idealSheafSectionCone X K (SheafOfModules.unit X.ringCatSheaf)))

include hunit in
/-- First-stage base change is faithful from the actual scalar section limit. -/
theorem firstStage_baseChange_faithful_of_unitSectionCone :
    (baseChange (K ^ 1).subschemeι).Faithful := by
  constructor
  intro C D f g hfg
  let : IsFiniteLocallyFree X (globalStructureCoherent C).obj :=
    globalStructure_finiteLocallyFree C
  let : IsFiniteLocallyFree X (globalStructureCoherent D).obj :=
    globalStructure_finiteLocallyFree D
  have hm : globalStructureMap f = globalStructureMap g := by
    apply vectorBundleCompletionMaps_injective X K hunit
      (globalStructureCoherent D).obj (globalStructureCoherent C).obj
      (restrictionCompletionData K C).val
    intro n
    change globalStructureMap f ≫
        ((idealSheafQuotientUnit X (K ^ n.unop)).app (globalStructureCoherent C).obj ≫
          (restrictionCompletionData K C).val.hom.app n) =
      globalStructureMap g ≫
        ((idealSheafQuotientUnit X (K ^ n.unop)).app (globalStructureCoherent C).obj ≫
          (restrictionCompletionData K C).val.hom.app n)
    rw [(restrictionCompletionData K C).property n.unop]
    change (Modules.Algebra.structureSheafFunctor X).map f.hom.op ≫
        (restrictionModuleUnit K C).app (op n.unop) =
      (Modules.Algebra.structureSheafFunctor X).map g.hom.op ≫
        (restrictionModuleUnit K C).app (op n.unop)
    rw [← restrictionModuleUnit_map K f n.unop, ← restrictionModuleUnit_map K g n.unop]
    have hs : restrictionStageMorphism K f n.unop = restrictionStageMorphism K g n.unop := by
      unfold restrictionStageMorphism
      rw [baseChange_map_eq_of_first K hfg n.unop]
    rw [hs]
  apply ObjectProperty.hom_ext
  exact Modules.Algebra.structurePullbackMap_over_injective f.hom g.hom hm

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLiftPullback
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.ValueLiftZero
public import Aglib.CategoryTheory.Sites.Hypercohomology.ContinuousPullbackConstant

/-! # The original constant-integer source of the value-lift pullback mate

The native source comparison is normalized on the original terminal section.
The resulting square keeps both original constant-integer maps; it does not
choose an unrelated isomorphism between their cohomology groups.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite


namespace CategoryTheory.Sheaf.BasisAcyclicity

open ModuleCoefficients Hypercohomology

universe c h d k v t

variable {C : Type c} [Category.{h} C] {D : Type d} [Category.{k} D]
  (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max h k v}]
  [HasSheafify K AddCommGrpCat.{max h k v}]
  [HasSheafify J AddCommGrpCat.{max h k v t}]
  [HasSheafify K AddCommGrpCat.{max h k v t}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h k v} J K).IsRightAdjoint]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max h k v t} J K).IsRightAdjoint]
  (U : C) (hU : IsTerminal U) (hGU : IsTerminal (G.obj U))

/-- The actual value-lift mate commutes with the original constant-integer
source maps, without requiring the mate to be invertible. -/
theorem valueLiftPullbackMap_constant :
    (G.sheafPullback AddCommGrpCat.{max h k v t} J K).map
        (valueLiftConstantMap.{c, h, max h k v, t} hU) ≫
      (valueLiftPullbackMap.{c, h, d, k, max h k v, t} G J K).app
        ((constantSheaf J AddCommGrpCat.{max h k v}).obj
          (AddCommGrpCat.of (ULift.{max h k v} ℤ))) ≫
      (valueLift.{d, k, max h k v, t} K).map
        (pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU).hom =
    (pullbackConstantIntegerIso.{c, h, d, k, max v t} G J K U hU hGU).hom ≫
      valueLiftConstantMap.{d, k, max h k v, t} hGU := by
  let A := (constantSheaf J AddCommGrpCat.{max h k v}).obj
    (AddCommGrpCat.of (ULift.{max h k v} ℤ))
  let B := (constantSheaf K AddCommGrpCat.{max h k v}).obj
    (AddCommGrpCat.of (ULift.{max h k v} ℤ))
  let q := pullbackConstantIntegerIso.{c, h, d, k, v} G J K U hU hGU
  let q' := pullbackConstantIntegerIso.{c, h, d, k, max v t} G J K U hU hGU
  let adj := G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v} J K
  let adj' := G.sheafAdjunctionContinuous AddCommGrpCat.{max h k v t} J K
  apply (adj'.homEquiv _ _).injective
  apply (constantHomSectionsEquiv hU _).injective
  rw [pullbackConstantIntegerIso_evaluation]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have hu := valueLiftPullbackMap_unit.{c, h, d, k, max h k v, t} G J K A
  simp only [valueLiftDirectImageIso, Iso.refl_hom, NatTrans.id_app] at hu
  change (valueLift.{c, h, max h k v, t} J).map (adj.unit.app A) =
    adj'.homEquiv _ _ ((valueLiftPullbackMap.{c, h, d, k, max h k v, t} G J K).app A) at hu
  rw [← hu]
  change constantHomSectionsEquiv hU _
    (valueLiftConstantMap.{c, h, max h k v, t} hU ≫
      (valueLift.{c, h, max h k v, t} J).map (adj.unit.app A) ≫
      (valueLift.{c, h, max h k v, t} J).map
        ((G.sheafPushforwardContinuous AddCommGrpCat.{max h k v} J K).map q.hom)) = _
  rw [← Functor.map_comp, valueLiftConstantMap_comp_sections]
  change ULift.up (constantHomSectionsEquiv hU _ (adj.homEquiv _ _ q.hom)) = _
  have hq := pullbackConstantIntegerIso_evaluation.{c, h, d, k, v} G J K U hU hGU B (𝟙 B)
  have hid := congrArg (fun a => constantHomSectionsEquiv hU _
    (adj.homEquiv _ _ a)) (Category.comp_id q.hom)
  rw [hid.symm.trans hq, valueLiftConstantMap_sections]

end CategoryTheory.Sheaf.BasisAcyclicity

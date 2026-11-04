/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationLaws
public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange

/-!
# Original Cartier evaluation with values in the actual roots scheme

If the original finite group is killed by `n`, its universal character has
`n`th power one. The original evaluation therefore factors uniquely through
the existing roots equalizer. This is a whole scheme equation in every
characteristic, including nonreduced test schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

open Scheme.OverField

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]

private theorem universalCharacter_pow_eq_one (n : ℕ)
    (hkill : (𝟙 G.X) ^ n = 1) :
    ((universalCharacter G).hom.hom) ^ n = 1 := by
  let D := (dualGroup G).X
  let F := Over.pullback D.hom
  let H := F.mapGrp.obj G
  let : GrpObj (F.obj G.X) := Functor.grpObjObj
  let m := F.homMonoidHom (X := G.X) (M := G.X)
  have hH : (𝟙 H.X) ^ n = 1 := by
    change (𝟙 (F.obj G.X)) ^ n = 1
    calc
      _ = (F.map (𝟙 G.X)) ^ n := by rw [F.map_id]
      _ = F.map ((𝟙 G.X) ^ n) := (m.map_pow _ _).symm
      _ = F.map 1 := congrArg F.map hkill
      _ = 1 := m.map_one
  let c : H ⟶ MultiplicativeGroup.groupScheme D.left := universalCharacter G
  have h := congrArg (fun q : H.X ⟶ H.X => q ≫ c.hom.hom) hH
  simpa only [MonObj.pow_comp, Category.id_comp, MonObj.one_comp, c] using h

/-- The original evaluation satisfies the original root equalizer equation. -/
theorem evaluation_comp_powerMap_eq_oneMap (n : ℕ)
    (hkill : (𝟙 G.X) ^ n = 1) :
    evaluation G ≫ MultiplicativeGroup.powerMap (Base k) n =
      evaluation G ≫ MultiplicativeGroup.oneMap (Base k) := by
  let D := (dualGroup G).X
  let H := ((Over.pullback D.hom).mapGrp.obj G).X
  let e := MultiplicativeBaseChange.unitsSectionsEquiv D.left H
  have hc := congrArg (fun c : H ⟶ (MultiplicativeGroup.groupScheme D.left).X => e c)
    (universalCharacter_pow_eq_one G n hkill)
  simp only [map_pow, map_one] at hc
  have hv : e (universalCharacter G).hom.hom =
      MultiplicativeGroup.sectionsUnitsEquiv (Base k) (G.X ⊗ D) (evaluation G) :=
    congrArg (MultiplicativeGroup.affineHomUnits (G.X ⊗ D).left)
      (universalCharacter_evaluation G)
  rw [hv] at hc
  apply (MultiplicativeGroup.sectionsUnitsEquiv (Base k) (G.X ⊗ D)).injective
  rw [MultiplicativeGroup.powerMap_comp, MultiplicativeGroup.oneMap_comp]
  exact hc

/-- Factor the same original evaluation through the actual roots scheme. -/
def evaluationRoots (n : ℕ) (hkill : (𝟙 G.X) ^ n = 1) :
    G.X ⊗ (dualGroup G).X ⟶ MultiplicativeGroup.rootsScheme (Base k) n :=
  equalizer.lift (evaluation G) (evaluation_comp_powerMap_eq_oneMap G n hkill)

/-- The factor has exactly the original evaluation as its composite. -/
@[reassoc (attr := simp)]
theorem evaluationRoots_comp_inclusion (n : ℕ) (hkill : (𝟙 G.X) ^ n = 1) :
    evaluationRoots G n hkill ≫ MultiplicativeGroup.rootsInclusion (Base k) n =
      evaluation G :=
  equalizer.lift_ι _ _

/-- Precomposition with an original parameter morphism preserves the
evaluation equation for the roots-valued factor. -/
theorem comp_evaluationRoots_comp_inclusion {T : FScheme k} (n : ℕ)
    (hkill : (𝟙 G.X) ^ n = 1) (a : T ⟶ G.X ⊗ (dualGroup G).X) :
    (a ≫ evaluationRoots G n hkill) ≫ MultiplicativeGroup.rootsInclusion (Base k) n =
      a ≫ evaluation G :=
  (Category.assoc _ _ _).trans (congrArg (fun b => a ≫ b)
    (evaluationRoots_comp_inclusion G n hkill))

/-- The original evaluation and original roots inclusion determine this factor. -/
theorem evaluationRoots_unique (n : ℕ) (hkill : (𝟙 G.X) ^ n = 1)
    (f : G.X ⊗ (dualGroup G).X ⟶ MultiplicativeGroup.rootsScheme (Base k) n)
    (hf : f ≫ MultiplicativeGroup.rootsInclusion (Base k) n = evaluation G) :
    f = evaluationRoots G n hkill := by
  apply equalizer.hom_ext (f := MultiplicativeGroup.powerMap (Base k) n)
    (g := MultiplicativeGroup.oneMap (Base k))
  exact hf.trans (evaluationRoots_comp_inclusion G n hkill).symm

end AlgebraicGeometry.Scheme.Group.CartierDuality

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationLaws

/-! The value of the original Cartier evaluation on two original test points. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- Evaluating the original character on the original test section gives
the value of the original whole pairing. Both sides use the same
multiplicative coordinate and the same original pullback. -/
theorem characterOfPoint_evaluation_section (T : FScheme k)
    (x : T ⟶ G.X) (y : T ⟶ (dualGroup G).X) :
    (lift x (𝟙 T)).left ≫ (characterOfPoint G T y).hom.hom.left ≫ prod.snd =
      (lift x y).left ≫ (evaluation G).left ≫ prod.snd := by
  have hm : groupPullbackBaseMap G y = (𝟙 G.X ⊗ₘ y).left := rfl
  have hxy : lift x (𝟙 T) ≫ (𝟙 G.X ⊗ₘ y) = lift x y := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  calc
    _ = (lift x (𝟙 T)).left ≫ groupPullbackBaseMap G y ≫ (evaluation G).left ≫ prod.snd :=
      congrArg (fun q => (lift x (𝟙 T)).left ≫ q) (characterOfPoint_evaluation G T y)
    _ = _ := by rw [hm, ← Category.assoc, ← Over.comp_left, hxy]

/-- The actual unit of the pairing is the original character's unit
restricted to the original test section. -/
theorem evaluation_units_eq_character_on_section (T : FScheme k)
    (x : T ⟶ G.X) (y : T ⟶ (dualGroup G).X) :
    MultiplicativeGroup.sectionsUnitsEquiv (Base k) T (lift x y ≫ evaluation G) =
      Units.map (lift x (𝟙 T)).left.appTop.hom.toMonoidHom
        (MultiplicativeGroup.sectionsUnitsEquiv T.left
          ((Over.pullback T.hom).mapGrp.obj G).X (characterEquiv G T y).hom.hom) := by
  let a := (lift x (𝟙 T)).left
  let c := (characterOfPoint G T y).hom.hom.left ≫ prod.snd
  have h := characterOfPoint_evaluation_section G T x y
  change MultiplicativeGroup.affineHomUnits T.left
      ((lift x y).left ≫ (evaluation G).left ≫ prod.snd) =
    Units.map a.appTop.hom.toMonoidHom (MultiplicativeGroup.affineHomUnits _ c)
  exact (congrArg (MultiplicativeGroup.affineHomUnits T.left) h.symm).trans
    (MultiplicativeGroup.affineHomUnits_comp a c)

end AlgebraicGeometry.Scheme.Group.CartierDuality

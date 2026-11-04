/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange

/-! The original Cartier character square on a pulled-back test point. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

open AlgebraicGeometry.Scheme.OverField (FScheme Base)

attribute [local instance] Over.cartesianMonoidalCategory

variable {k K : Type u} [Field k] [Field K]
  (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- A pulled-back original dual map gives the character of the adjoint test
point through the canonical composition comparison on the original group. -/
theorem dualGroupBaseChangeOverIso_character_square (i : Base K ⟶ Base k)
    (T : FScheme K) (U : FScheme k) (p : T ⟶ (Over.pullback i).obj U)
    (a : U ⟶ (dualGroup G).X) :
    characterEquiv ((Over.pullback i).mapGrp.obj G) T
        (p ≫ (Over.pullback i).map a ≫ (dualGroupBaseChangeOverIso K G i).hom) =
      (BaseChange.groupSchemeBaseChangeComp T.hom i).inv.app G ≫
        characterEquiv G ((Over.map i).obj T)
          ((((Over.mapPullbackAdj i).homEquiv T U).symm p) ≫ a) := by
  let d := p ≫ (Over.pullback i).map a
  let e := (dualGroupBaseChangeOverIso K G i).hom
  have h := dualGroupBaseChangeOverIso_character K G i T d
  have h' := characterEquivBaseChange_apply G (Over.mk i) T d
  dsimp only [Over.mk_hom, Over.mk_left] at h'
  have ha := (Over.mapPullbackAdj i).homEquiv_naturality_right_symm p a
  exact (congrArg (characterEquiv ((Over.pullback i).mapGrp.obj G) T)
    (Category.assoc p ((Over.pullback i).map a) e).symm).trans
      (h.trans (h'.trans (congrArg
        (fun x : (Over.map i).obj T ⟶ (dualGroup G).X =>
          (BaseChange.groupSchemeBaseChangeComp T.hom i).inv.app G ≫
            characterEquiv G ((Over.map i).obj T) x) ha)))

end AlgebraicGeometry.Scheme.Group.CartierDuality

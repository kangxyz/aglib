/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationLaws

/-! # The original character equivalence respects the original point products -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u
open AlgebraicGeometry.Scheme.OverField (FScheme Base)
attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]

private def primalTestIso (T : FScheme k) (x : T ⟶ G.X) :
    (Over.map G.X.hom).obj (Over.mk x.left) ≅ T :=
  Over.isoMk (Iso.refl _) (by simp [x.w])

private def primalTestPoint (T : FScheme k) (x : T ⟶ G.X)
    (p : T ⟶ (dualGroup G).X) :
    Over.mk x.left ⟶ ((Over.pullback G.X.hom).mapGrp.obj (dualGroup G)).X :=
  (MultiplicativeBaseChange.pullbackSectionsEquiv G.X.hom (dualGroup G) (Over.mk x.left)).symm
    ((primalTestIso G T x).hom ≫ p)

private theorem primalTestPoint_mul (T : FScheme k) (x : T ⟶ G.X)
    (p q : T ⟶ (dualGroup G).X) :
    primalTestPoint G T x (p * q) = primalTestPoint G T x p * primalTestPoint G T x q := by
  dsimp only [primalTestPoint]
  rw [MonObj.comp_mul, map_mul]

private theorem primalTestPoint_evaluation (T : FScheme k) (x : T ⟶ G.X)
    (p : T ⟶ (dualGroup G).X) :
    (primalTestPoint G T x p ≫ evaluationOverPrimal G).left ≫ prod.snd =
      (lift x p ≫ evaluation G).left ≫ prod.snd := by
  have hpoint : (primalTestPoint G T x p).left =
      pullback.lift p.left x.left (p.w.trans x.w.symm) := by
    have he := (MultiplicativeBaseChange.pullbackSectionsEquiv G.X.hom
      (dualGroup G) (Over.mk x.left)).apply_symm_apply
        ((primalTestIso G T x).hom ≫ p)
    have hf := congrArg Over.Hom.left he
    change (primalTestPoint G T x p).left ≫
      pullback.fst (dualGroup G).X.hom G.X.hom = (𝟙 T.left) ≫ p.left at hf
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst, Category.id_comp] using hf
    · have hw := (primalTestPoint G T x p).w
      dsimp only [Functor.mapGrp_obj_X, Over.pullback_obj_hom, Over.mk_hom] at hw
      simpa only [pullback.lift_snd] using hw
  have hswap : (primalTestPoint G T x p).left ≫
      (β_ (dualGroup G).X G.X).hom.left = (lift x p).left := by
    rw [hpoint, Over.braiding_hom_left, Over.lift_left]
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd]
  change ((primalTestPoint G T x p).left ≫
    prod.lift _ ((β_ (dualGroup G).X G.X).hom.left ≫
      (evaluation G).left ≫ prod.snd)) ≫ prod.snd = _
  rw [Category.assoc, prod.lift_snd]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (evaluation G).left ≫ prod.snd) hswap).trans
      (Category.assoc _ _ _).symm)

/-- Evaluate the same original pairing on two actual sections as a global unit. -/
def evaluationPointUnit (T : FScheme k) (x : T ⟶ G.X) (p : T ⟶ (dualGroup G).X) :
    Γ(T.left, ⊤)ˣ :=
  MultiplicativeGroup.sectionsUnitsEquiv (Base k) T (lift x p ≫ evaluation G)

/-- The original second-variable group law holds on all scheme-valued tests. -/
theorem evaluationPointUnit_mul (T : FScheme k) (x : T ⟶ G.X)
    (p q : T ⟶ (dualGroup G).X) :
    evaluationPointUnit G T x (p * q) =
      evaluationPointUnit G T x p * evaluationPointUnit G T x q := by
  let := MultiplicativeGroup.commGroup G.X.left
  let : IsMonHom (evaluationOverPrimal G) := evaluationOverPrimal_isMonHom G
  have hval (r : T ⟶ (dualGroup G).X) : evaluationPointUnit G T x r =
      MultiplicativeGroup.sectionsUnitsEquiv G.X.left (Over.mk x.left)
        (primalTestPoint G T x r ≫ evaluationOverPrimal G) := by
    exact congrArg (MultiplicativeGroup.affineHomUnits T.left)
      (primalTestPoint_evaluation G T x r).symm
  rw [hval, primalTestPoint_mul, MonObj.mul_comp,
    MultiplicativeGroup.sectionsUnitsEquiv_mul, ← hval, ← hval]

private theorem character_unit (T : FScheme k) (p : T ⟶ (dualGroup G).X) :
    MultiplicativeGroup.sectionsUnitsEquiv T.left
        ((Over.pullback T.hom).mapGrp.obj G).X (characterOfPoint G T p).hom.hom =
      evaluationPointUnit G (G.X ⊗ T) (fst G.X T) (snd G.X T ≫ p) := by
  have h := characterOfPoint_evaluation G T p
  have ht : lift (fst G.X T) (snd G.X T ≫ p) = 𝟙 G.X ⊗ₘ p := by
    simpa using (lift_fst_comp_snd_comp (𝟙 G.X) p)
  change MultiplicativeGroup.affineHomUnits (G.X ⊗ T).left
      ((characterOfPoint G T p).hom.hom.left ≫ prod.snd) =
    MultiplicativeGroup.affineHomUnits (G.X ⊗ T).left
      ((lift (fst G.X T) (snd G.X T ≫ p)).left ≫ (evaluation G).left ≫ prod.snd)
  rw [ht]
  exact congrArg (MultiplicativeGroup.affineHomUnits (G.X ⊗ T).left) h

/-- The original all-test character bijection preserves actual point multiplication. -/
theorem characterOfPoint_mul (T : FScheme k) (p q : T ⟶ (dualGroup G).X) :
    characterOfPoint G T (p * q) = characterOfPoint G T p * characterOfPoint G T q := by
  let := MultiplicativeGroup.commGroup T.left
  apply Grp.hom_ext
  apply (MultiplicativeGroup.sectionsUnitsEquiv T.left
    ((Over.pullback T.hom).mapGrp.obj G).X).injective
  change MultiplicativeGroup.sectionsUnitsEquiv T.left _
      (characterOfPoint G T (p * q)).hom.hom =
    MultiplicativeGroup.sectionsUnitsEquiv T.left _
      ((characterOfPoint G T p).hom.hom * (characterOfPoint G T q).hom.hom)
  rw [MultiplicativeGroup.sectionsUnitsEquiv_mul, character_unit, character_unit, character_unit,
    MonObj.comp_mul, evaluationPointUnit_mul]

/-- The same original character equivalence preserves multiplication without a new group model. -/
theorem characterEquiv_mul (T : FScheme k) (p q : T ⟶ (dualGroup G).X) :
    characterEquiv G T (p * q) = characterEquiv G T p * characterEquiv G T q :=
  characterOfPoint_mul G T p q

end AlgebraicGeometry.Scheme.Group.CartierDuality

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.StageBaseChange
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The actual nilpotent finite-etale cover tower

A prescribed first-stage cover lifts recursively through the literal positive
ideal-power transitions using the existing nilpotent equivalence. The zeroth
stage is its actual pullback to the empty thickening, not another lift across a
purported nilpotent map. The successor comparison determines original scheme
maps and cartesian squares. Their composites give the whole native tower.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

variable {X : Scheme.{u}} (K : X.IdealSheafData)

/-- Finite-etale covers of the actual powers, with their specified successor
base-change comparisons. No algebra structure is duplicated in this packet. -/
structure CoverSystem where
  /-- The actual finite-etale cover of each original ideal-power thickening. -/
  cover (n : ℕ) : FiniteEtale (K ^ n).subscheme
  /-- The specified base-change comparison from each original successor cover. -/
  reductionIso (n : ℕ) :
    (baseChange (stageMap K (Nat.le_succ n))).obj (cover (n + 1)) ≅ cover n

/-- The recursive object choice is made while all categories remain abstract. -/
def equivalenceTowerObj {D : ℕ → Type*} [∀ n, Category (D n)]
    (F : ∀ n, D (n + 1) ⥤ D n) (hF : ∀ n, (F n).IsEquivalence)
    (C : D 0) : (n : ℕ) → D n
  | 0 => C
  | n + 1 =>
    letI := hF n
    (F n).asEquivalence.inverse.obj (equivalenceTowerObj F hF C n)

/-- The original recursive choices and all their counits are constructed together. -/
def equivalenceTowerData {D : ℕ → Type*} [∀ n, Category (D n)]
    (F : ∀ n, D (n + 1) ⥤ D n) (hF : ∀ n, (F n).IsEquivalence)
    (C : D 0) :
    {O : (n : ℕ) → D n // O 0 = C ∧
      Nonempty (∀ n, (F n).obj (O (n + 1)) ≅ O n)} := by
  refine ⟨equivalenceTowerObj F hF C, rfl, ⟨fun n => ?_⟩⟩
  letI := hF n
  exact (F n).asEquivalence.counitIso.app _

/-- The positive native cover tower, with its original counit family. -/
def positiveCoverData (C : FiniteEtale (K ^ 1).subscheme) :=
  equivalenceTowerData
    (D := fun n => FiniteEtale (K ^ (n + 1)).subscheme)
    (fun n => baseChange (stageMap K (Nat.le_succ (n + 1))))
    (fun n => stageMap_baseChange_isEquivalence K
      (Nat.le_succ (n + 1)) (Nat.zero_lt_succ n)) C

/-- Positive stages are the object projection of the whole native counit packet. -/
def positiveCover (C : FiniteEtale (K ^ 1).subscheme) (n : ℕ) :
    FiniteEtale (K ^ (n + 1)).subscheme :=
  (positiveCoverData K C).val n

/-- The specified reduction is projected from that same original packet. -/
def positiveCoverReductionIso (C : FiniteEtale (K ^ 1).subscheme) (n : ℕ) :
    (baseChange (stageMap K (Nat.le_succ (n + 1)))).obj (positiveCover K C (n + 1)) ≅
      positiveCover K C n :=
  (positiveCoverData K C).property.2.some n

/-- Every prescribed first-stage cover produces an actual compatible tower.
There is no compatible-lift or adicity hypothesis on the prescribed cover. -/
def coverSystem (C : FiniteEtale (K ^ 1).subscheme) : CoverSystem K where
  cover
    | 0 => (baseChange (stageMap K (Nat.zero_le 1))).obj C
    | n + 1 => positiveCover K C n
  reductionIso
    | 0 => Iso.refl _
    | n + 1 => positiveCoverReductionIso K C n

@[simp]
theorem coverSystem_cover_one (C : FiniteEtale (K ^ 1).subscheme) :
    (coverSystem K C).cover 1 = C := rfl

namespace CoverSystem

variable {K} (T : CoverSystem K)

/-- The original structural morphism of a tower cover to the ambient scheme. -/
abbrev ambientMap (n : ℕ) : (T.cover n).obj.left ⟶ X :=
  (T.cover n).obj.hom ≫ (K ^ n).subschemeι

/-- The actual successor map, from the smaller cover to the larger cover. -/
def transition (n : ℕ) : (T.cover n).obj.left ⟶ (T.cover (n + 1)).obj.left :=
  (T.reductionIso n).inv.hom.left ≫
    pullback.fst (T.cover (n + 1)).obj.hom (stageMap K (Nat.le_succ n))

@[reassoc]
theorem transition_base (n : ℕ) :
    T.transition n ≫ (T.cover (n + 1)).obj.hom =
      (T.cover n).obj.hom ≫ stageMap K (Nat.le_succ n) := by
  dsimp only [transition]
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun k => k ≫ stageMap K (Nat.le_succ n))
    (Over.w (T.reductionIso n).inv.hom)

@[reassoc (attr := simp)]
theorem transition_ambientMap (n : ℕ) :
    T.transition n ≫ T.ambientMap (n + 1) = T.ambientMap n := by
  dsimp only [ambientMap]
  rw [← Category.assoc, transition_base, Category.assoc, stageMap_ι]

/-- The original successor cover square is cartesian. -/
theorem transition_isPullback (n : ℕ) :
    IsPullback (T.transition n) (T.cover n).obj.hom
      (T.cover (n + 1)).obj.hom (stageMap K (Nat.le_succ n)) := by
  exact IsPullback.of_iso_pullback ⟨T.transition_base n⟩
    ((forgetToScheme _).mapIso (T.reductionIso n).symm) rfl
    (Over.w (T.reductionIso n).inv.hom)

/-- The native diagram of actual covers over the original ambient scheme. -/
def diagram : ℕ ⥤ Over X :=
  Functor.ofSequence (X := fun n => Over.mk (T.ambientMap n))
    (fun n => Over.homMk (T.transition n) (T.transition_ambientMap n))

@[simp]
theorem diagram_obj (n : ℕ) : T.diagram.obj n = Over.mk (T.ambientMap n) := rfl

@[simp]
theorem diagram_map_succ (n : ℕ) :
    (T.diagram.map (homOfLE (Nat.le_succ n))).left = T.transition n := by
  simp [diagram]

/-- The actual zeroth cover is empty, for every compatible tower. -/
theorem cover_zero_isEmpty : IsEmpty (T.cover 0).obj.left := by
  let : IsEmpty (K ^ 0).subscheme := by
    rw [pow_zero, IdealSheafData.one_eq_top]
    infer_instance
  exact Function.isEmpty (T.cover 0).obj.hom

end CoverSystem

/-- The actual restriction tower of an existing global finite-etale cover. -/
def restrictionCoverSystem (C : FiniteEtale X) : CoverSystem K where
  cover n := (baseChange (K ^ n).subschemeι).obj C
  reductionIso n :=
    ((baseChangeComp (K ^ (n + 1)).subschemeι (stageMap K (Nat.le_succ n))).app C).symm ≪≫
      eqToIso (congrArg (fun j => (baseChange j).obj C) (stageMap_ι K (Nat.le_succ n)))

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

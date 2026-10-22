/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystem

/-!
# Unique compatible tower maps from the prescribed first-stage map

Nilpotent full faithfulness lifts maps directly between the original chosen
cover stages. No replacement tower or global map is assumed. Index zero is
obtained from the original reduction isomorphisms, separately from the positive
nilpotent stages.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

/-- The positive recursive morphism choice, before specializing any geometry. -/
def equivalenceTowerHom {D : ℕ → Type*} [∀ n, Category (D n)]
    (F : ∀ n, D (n + 1) ⥤ D n) (hF : ∀ n, (F n).Full)
    (P Q : ∀ n, D n) (eP : ∀ n, (F n).obj (P (n + 1)) ≅ P n)
    (eQ : ∀ n, (F n).obj (Q (n + 1)) ≅ Q n) (f : P 0 ⟶ Q 0) :
    ∀ n, P n ⟶ Q n
  | 0 => f
  | n + 1 =>
    letI := hF n
    (F n).preimage ((eP n).hom ≫ equivalenceTowerHom F hF P Q eP eQ f n ≫ (eQ n).inv)

/-- The original recursive maps and their whole transition equation family. -/
def equivalenceTowerHomData {D : ℕ → Type*} [∀ n, Category (D n)]
    (F : ∀ n, D (n + 1) ⥤ D n) (hF : ∀ n, (F n).Full)
    (P Q : ∀ n, D n) (eP : ∀ n, (F n).obj (P (n + 1)) ≅ P n)
    (eQ : ∀ n, (F n).obj (Q (n + 1)) ≅ Q n) (f : P 0 ⟶ Q 0) :
    {h : ∀ n, P n ⟶ Q n // h 0 = f ∧
      ∀ n, (F n).map (h (n + 1)) ≫ (eQ n).hom = (eP n).hom ≫ h n} := by
  refine ⟨equivalenceTowerHom F hF P Q eP eQ f, rfl, fun n => ?_⟩
  let := hF n
  change (F n).map ((F n).preimage _) ≫ _ = _
  simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Compose two original commuting squares before specializing any cover geometry. -/
theorem composeSquareRows {D : Type*} [Category D] {A B P Q R S : D}
    (a : A ⟶ P) (b : B ⟶ Q) (u : A ⟶ B) (v : P ⟶ Q)
    (s : P ⟶ R) (t : Q ⟶ S) (w : R ⟶ S)
    (ha : a ≫ v = u ≫ b) (hb : v ≫ t = s ≫ w) :
    (a ≫ s) ≫ w = u ≫ (b ≫ t) := by
  rw [Category.assoc, ← hb, ← Category.assoc, ha, Category.assoc]

namespace CoverSystem

variable {X : Scheme.{u}} {K : X.IdealSheafData} (T U : CoverSystem K)

/-- Original maps on every chosen cover stage, with their specified reduction compatibility. -/
structure Hom where
  /-- The original morphism at each chosen finite-etale cover stage. -/
  stage (n : ℕ) : T.cover n ⟶ U.cover n
  reduction (n : ℕ) :
    (baseChange (stageMap K (Nat.le_succ n))).map (stage (n + 1)) ≫
      (U.reductionIso n).hom = (T.reductionIso n).hom ≫ stage n

/-- Lift positive-stage maps directly between the actual two cover systems. -/
def positiveHomData (f : T.cover 1 ⟶ U.cover 1) :=
  equivalenceTowerHomData
    (D := fun n => FiniteEtale (K ^ (n + 1)).subscheme)
    (fun n => baseChange (stageMap K (Nat.le_succ (n + 1))))
    (fun n => by
      let : (baseChange (stageMap K (Nat.le_succ (n + 1)))).IsEquivalence :=
        stageMap_baseChange_isEquivalence K (Nat.le_succ (n + 1)) (Nat.zero_lt_succ n)
      infer_instance)
    (fun n => T.cover (n + 1)) (fun n => U.cover (n + 1))
    (fun n => T.reductionIso (n + 1)) (fun n => U.reductionIso (n + 1)) f

/-- The prescribed first-stage map has an actual compatible lift to all stages. -/
def homOfFirstStage (f : T.cover 1 ⟶ U.cover 1) : Hom T U where
  stage
    | 0 => (T.reductionIso 0).inv ≫
      (baseChange (stageMap K (Nat.le_succ 0))).map f ≫ (U.reductionIso 0).hom
    | n + 1 => (positiveHomData T U f).val n
  reduction
    | 0 => by simp only [Iso.hom_inv_id_assoc]; rfl
    | n + 1 => (positiveHomData T U f).property.2 n

@[simp]
theorem homOfFirstStage_stage_one (f : T.cover 1 ⟶ U.cover 1) :
    (homOfFirstStage T U f).stage 1 = f := rfl

namespace Hom

variable {T U} (h : Hom T U)

/-- Reduction compatibility also retains its original inverse-comparison equation. -/
theorem reduction_inv (n : ℕ) :
    (T.reductionIso n).inv ≫
      (baseChange (stageMap K (Nat.le_succ n))).map (h.stage (n + 1)) =
      h.stage n ≫ (U.reductionIso n).inv := by
  apply (cancel_epi (T.reductionIso n).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h.reduction n,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Original stage maps commute with the original scheme transitions. -/
@[reassoc]
theorem transition (n : ℕ) :
    T.transition n ≫ (h.stage (n + 1)).hom.left =
      (h.stage n).hom.left ≫ U.transition n := by
  have hp :
      ((baseChange (stageMap K (Nat.le_succ n))).map (h.stage (n + 1))).hom.left ≫
        pullback.fst (U.cover (n + 1)).obj.hom (stageMap K (Nat.le_succ n)) =
      pullback.fst (T.cover (n + 1)).obj.hom (stageMap K (Nat.le_succ n)) ≫
        (h.stage (n + 1)).hom.left := by
    simp [baseChange, forget, Over.pullback]
  have hi : (T.reductionIso n).inv.hom.left ≫
      ((baseChange (stageMap K (Nat.le_succ n))).map (h.stage (n + 1))).hom.left =
      (h.stage n).hom.left ≫ (U.reductionIso n).inv.hom.left := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left] using
      congrArg (fun k => k.hom.left) (h.reduction_inv n)
  exact composeSquareRows _ _ _ _ _ _ _ hi hp

/-- Original stage morphisms as arrows over the original ambient scheme. -/
def ambientStage (n : ℕ) : Over.mk (T.ambientMap n) ⟶ Over.mk (U.ambientMap n) :=
  (Over.map (K ^ n).subschemeι).map (h.stage n).hom

/-- First-stage equality determines all positive stages and the separately
constructed empty stage. -/
theorem ext_first {k : Hom T U} (e : h.stage 1 = k.stage 1) : h = k := by
  have hpos : ∀ n, h.stage (n + 1) = k.stage (n + 1) := by
    intro n
    induction n with
    | zero => exact e
    | succ n ih =>
      let : (baseChange (stageMap K (Nat.le_succ (n + 1)))).IsEquivalence :=
        stageMap_baseChange_isEquivalence K (Nat.le_succ (n + 1)) (Nat.zero_lt_succ n)
      apply (baseChange (stageMap K (Nat.le_succ (n + 1)))).map_injective
      apply (cancel_mono (U.reductionIso (n + 1)).hom).mp
      rw [h.reduction, k.reduction, ih]
  have hs : h.stage = k.stage := by
    funext n
    cases n with
    | zero =>
      apply (cancel_epi (T.reductionIso 0).hom).mp
      rw [← h.reduction 0, ← k.reduction 0, e]
    | succ n => exact hpos n
  cases h
  cases k
  cases hs
  rfl

end Hom

/-- Existence and uniqueness of the compatible actual lift of the given first-stage map. -/
theorem existsUnique_homOfFirstStage (f : T.cover 1 ⟶ U.cover 1) :
    ∃! h : Hom T U, h.stage 1 = f :=
  ⟨homOfFirstStage T U f, rfl, fun h hh => h.ext_first hh⟩

end CoverSystem

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

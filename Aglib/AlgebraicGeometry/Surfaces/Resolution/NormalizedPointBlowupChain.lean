/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# Finite chains of actual normalized closed-point blowups

Each step is the constructed ordinary blowup of the full original point
ideal, followed by normalization of its original generic inclusion. The
chain stores only these actual steps and their composite morphism.

Integrality, normality, dominance and the original function-field comparison
are proved here. Finiteness of normalization and properness are derived by
the completion-descent consumer under its actual surface hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- The original point blowup followed by its actual generic normalization. -/
abbrev normalizedPointBlowup (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) : Scheme.{u} :=
  let B := blowupDatum (X.fromSpecResidueField x).ker
  letI : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  (B.Y.fromSpecStalk (genericPoint B.Y)).normalization

/-- The original normalization arrow followed by the original blowdown. -/
def normalizedPointBlowupMap (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    normalizedPointBlowup X x hx hne ⟶ X := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  exact (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization ≫ B.map

/-- Integral source is intrinsic to the literal normalized point blowup. -/
theorem normalizedPointBlowup_isIntegral (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    IsIntegral (normalizedPointBlowup X x hx hne) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  change IsIntegral (B.Y.fromSpecStalk (genericPoint B.Y)).normalization
  infer_instance

/-- The actual generic normalization is normal at every original stalk. -/
theorem normalizedPointBlowup_normalStalks (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    NormalStalks (normalizedPointBlowup X x hx hne) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  exact genericNormalization_normalStalks B.Y

/-- Dominance is on the original composite normalization and blowup map. -/
theorem normalizedPointBlowupMap_isDominant (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    IsDominant (normalizedPointBlowupMap X x hx hne) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  let : IsDominant B.map := pointBlowup_isDominant X x hx hne
  let := genericNormalization_isDominant B.Y
  change IsDominant ((B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization ≫ B.map)
  infer_instance

/-- Birationality retains the actual generic stalk homomorphism. -/
theorem normalizedPointBlowupMap_functionFieldMap_isIso
    (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    letI := normalizedPointBlowup_isIntegral X x hx hne
    letI := normalizedPointBlowupMap_isDominant X x hx hne
    IsIso (CommRingCat.ofHom
      (Scheme.functionFieldMap (normalizedPointBlowupMap X x hx hne))) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  let : IsDominant B.map := pointBlowup_isDominant X x hx hne
  let ν := (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization
  let : IsDominant ν := genericNormalization_isDominant B.Y
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap B.map)) :=
    B.functionFieldMap_isIso (genericPoint_not_mem_pointCentre x hx hne)
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap ν)) :=
    genericNormalization_fieldMap_isIso B.Y
  change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (ν ≫ B.map)))
  rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp]
  infer_instance

/-- A finite chain of literal normalized closed-point blowups. It stores
no regularity, finiteness, properness or completion-comparison certificate. -/
inductive NormalizedPointBlowupChain :
    {Y X : Scheme.{u}} → (Y ⟶ X) → Type (u + 1)
  | refl (X : Scheme.{u}) : NormalizedPointBlowupChain (𝟙 X)
  | cons {X Y : Scheme.{u}} [IsIntegral X]
      (x : X) (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X)
      (g : Y ⟶ normalizedPointBlowup X x hx hne)
      (tail : NormalizedPointBlowupChain g) :
      NormalizedPointBlowupChain (g ≫ normalizedPointBlowupMap X x hx hne)

/-- The number of prescribed normalized point steps. -/
def NormalizedPointBlowupChain.length : {Y X : Scheme.{u}} → {f : Y ⟶ X} →
    NormalizedPointBlowupChain f → ℕ
  | _, _, _, .refl _ => 0
  | _, _, _, @NormalizedPointBlowupChain.cons _ _ _ _ _ _ _ tail => tail.length + 1

/-- Source integrality follows from the actual steps. -/
theorem NormalizedPointBlowupChain.isIntegral
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : NormalizedPointBlowupChain f) :
    IsIntegral X → IsIntegral Y := by
  induction c with
  | refl X => exact id
  | @cons X Y hX x hx hne g tail ih =>
    exact fun _ => ih (normalizedPointBlowup_isIntegral X x hx hne)

/-- Normality is preserved along the prescribed normalized steps. -/
theorem NormalizedPointBlowupChain.normalStalks
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : NormalizedPointBlowupChain f) :
    NormalStalks X → NormalStalks Y := by
  induction c with
  | refl X => exact id
  | @cons X Y hX x hx hne g tail ih =>
    exact fun _ => ih (normalizedPointBlowup_normalStalks X x hx hne)

/-- Dominance concerns the same original composite indexed by the chain. -/
theorem NormalizedPointBlowupChain.isDominant
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : NormalizedPointBlowupChain f) :
    IsIntegral X → IsDominant f := by
  induction c with
  | refl X => intro _; infer_instance
  | @cons X Y hX x hx hne g tail ih =>
    intro _
    let : IsDominant (normalizedPointBlowupMap X x hx hne) :=
      normalizedPointBlowupMap_isDominant X x hx hne
    let : IsDominant g := ih (normalizedPointBlowup_isIntegral X x hx hne)
    infer_instance

/-- The chain induces an isomorphism through its original function-field
map, using the original map of every normalization and ordinary blowdown. -/
theorem NormalizedPointBlowupChain.functionFieldMap_isIso
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : NormalizedPointBlowupChain f)
    (hX : IsIntegral X) :
    letI := hX
    letI := c.isIntegral hX
    letI := c.isDominant hX
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := by
  revert hX
  induction c with
  | refl X =>
    intro hX
    let := hX
    exact Scheme.FunctionField.fieldMap_isIso (𝟙 X)
  | @cons X Y hX x hx hne g tail ih =>
    intro _
    let hN := normalizedPointBlowup_isIntegral X x hx hne
    let : IsIntegral (normalizedPointBlowup X x hx hne) := hN
    let : IsIntegral Y := tail.isIntegral hN
    let : IsDominant (normalizedPointBlowupMap X x hx hne) :=
      normalizedPointBlowupMap_isDominant X x hx hne
    let : IsDominant g := tail.isDominant hN
    let : IsIso (CommRingCat.ofHom
        (Scheme.functionFieldMap (normalizedPointBlowupMap X x hx hne))) :=
      normalizedPointBlowupMap_functionFieldMap_isIso X x hx hne
    let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap g)) := ih hN
    change IsIso (CommRingCat.ofHom
      (Scheme.functionFieldMap (g ≫ normalizedPointBlowupMap X x hx hne)))
    rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance

end AlgebraicGeometry.Scheme.Blowup

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain
public import Aglib.AlgebraicGeometry.Normalization.ProperBirational
public import Aglib.AlgebraicGeometry.Blowup.Properness

/-!
# Finiteness of a prescribed first step from the proper terminal map

The chain datatype supplies the actual factorization, not properness.
Properness of the supplied total map makes its factor through the ordinary
first blowup proper. Its normal integral terminal source forces finiteness
of that blowup's literal generic normalization.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- A proper total prescribed chain forces finiteness of its literal first
normalization. No finiteness or properness is inferred from the chain alone. -/
theorem firstNormalization_isFinite_of_proper_chain
    {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X)
    (g : T ⟶ normalizedPointBlowup X x hx hne)
    (tail : NormalizedPointBlowupChain g)
    [IsProper (g ≫ normalizedPointBlowupMap X x hx hne)] :
    let B := blowupDatum (X.fromSpecResidueField x).ker
    letI := pointBlowup_isIntegral X x hx hne
    IsFinite (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  let N := normalizedPointBlowup X x hx hne
  let hN : IsIntegral N := normalizedPointBlowup_isIntegral X x hx hne
  let : IsIntegral N := hN
  let : IsIntegral T := tail.isIntegral hN
  let : IsDominant g := tail.isDominant hN
  let ν := (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization
  let : IsDominant ν := genericNormalization_isDominant B.Y
  let k := g ≫ ν
  have : IsProper (k ≫ B.map) := by
    change IsProper ((g ≫ ν) ≫ B.map)
    rw [Category.assoc]
    exact inferInstanceAs (IsProper (g ≫ normalizedPointBlowupMap X x hx hne))
  let : IsProper k := IsProper.of_comp k B.map
  let : IsDominant k := inferInstance
  have hT : NormalStalks T :=
    tail.normalStalks (normalizedPointBlowup_normalStalks X x hx hne)
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap g)) :=
    tail.functionFieldMap_isIso hN
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap ν)) :=
    genericNormalization_fieldMap_isIso B.Y
  have hk : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap k)) := by
    change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (g ≫ ν)))
    rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  exact genericNormalization_isFinite_of_proper_birational k hT hk

/-- Both the first step and the remaining tail are proper once the actual
whole chain is proper. This is the induction invariant used in globalization. -/
theorem firstStep_and_tail_isProper_of_proper_chain
    {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X)
    (g : T ⟶ normalizedPointBlowup X x hx hne)
    (tail : NormalizedPointBlowupChain g)
    [IsProper (g ≫ normalizedPointBlowupMap X x hx hne)] :
    IsProper (normalizedPointBlowupMap X x hx hne) ∧ IsProper g := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let : IsIntegral B.Y := pointBlowup_isIntegral X x hx hne
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let ν := (B.Y.fromSpecStalk (genericPoint B.Y)).fromNormalization
  let : IsFinite ν := firstNormalization_isFinite_of_proper_chain x hx hne g tail
  have hs : IsProper (normalizedPointBlowupMap X x hx hne) := by
    change IsProper (ν ≫ B.map)
    infer_instance
  let := hs
  exact ⟨hs, IsProper.of_comp g (normalizedPointBlowupMap X x hx hne)⟩

end AlgebraicGeometry.Scheme.Blowup

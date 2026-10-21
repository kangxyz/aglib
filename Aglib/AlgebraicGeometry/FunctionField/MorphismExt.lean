/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
Native extraction from `R5Lab.Aglib.AlgebraicGeometry.FunctionField.MorphismExt`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`2e397dc14c43766d24c6fa208854732019189b065d505d10dc62ebf2c0a028fe`.
Only source26–59: same-base constants compatibility delegates the existing stronger actual
  constants-square theorem, and separated uniqueness uses the existing actual generic-stalk
  naturality. No replacement field map, scalar map or function-field carrier is defined.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.FunctionField

/-- Actual function-field pullback preserves the same structural constants. -/
lemma map_constants {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (p : Y ⟶ Spec (.of k)) :
    (Scheme.functionFieldMap f).comp (Scheme.functionFieldConstants Y p) =
      Scheme.functionFieldConstants X (f ≫ p) := by
  simpa only [RingHom.comp_id] using
    (Scheme.functionFieldMap_constants f p (f ≫ p) (RingHom.id k) (by simp))

/-- Dominant morphisms to a separated target are determined by the actual field map. -/
lemma hom_ext {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Spec (.of k)) [IsSeparated p]
    (f g : X ⟶ Y) [IsDominant f] [IsDominant g]
    (hover : f ≫ p = g ≫ p)
    (hfield : Scheme.functionFieldMap f = Scheme.functionFieldMap g) : f = g := by
  apply ext_of_isDominant_of_isSeparated p
    (ι := X.fromSpecStalk (genericPoint X)) hover
  rw [Scheme.fromSpecStalk_genericPoint_naturality f,
    Scheme.fromSpecStalk_genericPoint_naturality g, hfield]

end AlgebraicGeometry.Scheme.FunctionField
end

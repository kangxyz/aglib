/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.SeparableStage
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# FiniteStageEmbedding

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChangeComp forget)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PointedInjection

universe u

theorem baseChange_map_mono {X T : Scheme.{u}} (f : T ⟶ X)
    {Y Z : Scheme.FiniteEtale X} (g : Y ⟶ Z) [Mono g] : Mono ((baseChange f).map g) := by
  let : Mono g.hom.left := Connectedness.mono_left g
  let : Mono g.hom := Over.mono_of_mono_left _
  have : Mono ((Over.pullback f).map g.hom) := inferInstance
  exact (forget T).mono_of_mono_map this

/-- An actual cover descended to a finite étale intermediate base embeds in
the pullback of its total cover over the original base. -/
theorem exists_subobject_of_finite_etale_model {X S T : Scheme.{u}}
    (f : S ⟶ X) [IsFinite f] [Etale f] (r : T ⟶ S) (π : T ⟶ X) (hr : r ≫ f = π)
    (Y : Scheme.FiniteEtale T) (A : Scheme.FiniteEtale S) (e : Y ≅ (baseChange r).obj A) :
    ∃ Z : Scheme.FiniteEtale X, ∃ j : Y ⟶ (baseChange π).obj Z, Mono j := by
  let Z := PointLift.totalCover f A
  let j := (baseChange r).map (PointLift.totalGraph f A)
  let : Mono j := baseChange_map_mono r (PointLift.totalGraph f A)
  let c : (baseChange r).obj ((baseChange f).obj Z) ≅ (baseChange π).obj Z :=
    ((baseChangeComp f r).app Z).symm ≪≫
      eqToIso (congrArg (fun q ↦ (baseChange q).obj Z) hr)
  exact ⟨Z, e.hom ≫ j ≫ c.hom, inferInstance⟩

end AlgebraicGeometry.Scheme.FiniteEtale.PointedInjection

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ebda850110724b2536b109b205e33dd36299f89d64730195fd781872799b3c4e.
Definitions, hypotheses and universes are retained modulo native names. -/

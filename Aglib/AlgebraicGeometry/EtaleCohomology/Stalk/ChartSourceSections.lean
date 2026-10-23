/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartSourceMap

/-! # Normalization of the actual chart comparison source on sections -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

private theorem composite_constant_sections {A B D : Type*}
    [Category* A] [Category* B] [Category* D]
    {L₀ : A ⥤ B} {R₀ : B ⥤ A} {L₁ : B ⥤ D} {R₁ : D ⥤ B} {L₂ : A ⥤ D}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₁ ⋙ R₀)
    (Z : A) (F : D) (a : L₂.obj Z ⟶ F) :
    a₀.homEquiv Z (R₁.obj F)
      ((a₁.unit.app (L₀.obj Z) ≫
        R₁.map (((a₀.comp a₁).leftAdjointUniq a₂).hom.app Z)) ≫ R₁.map a) =
      a₂.homEquiv Z F a := by
  rw [Category.assoc, ← R₁.map_comp]
  have hc (k : L₁.obj (L₀.obj Z) ⟶ F) :
      (a₀.comp a₁).homEquiv Z F k =
        a₀.homEquiv Z (R₁.obj F) (a₁.unit.app (L₀.obj Z) ≫ R₁.map k) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  rw [← hc]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- The source comparison is fixed by the original constant-sheaf adjunction,
not an arbitrary isomorphism of constant objects. -/
theorem chartSliceSource_sections
    (F : Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1})
    (a : Sheaf.SliceCohomology.sliceIntegers.{u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) U ⟶ F) :
    (constantSheafAdj (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}
      (etaleTerminalIsTerminal U.left)).homEquiv _ _
      (chartSliceSource U ≫ (etaleSliceSheafEquivalence U).inverse.map a) =
    (constantSheafAdj ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}
      ((etaleTerminalIsTerminal U.left).isTerminalObj (etaleSliceBackward U))).homEquiv _ _ a :=
  composite_constant_sections
    (constantSheafAdj (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}
      (etaleTerminalIsTerminal U.left))
    (etaleSliceSheafEquivalence U).toAdjunction
    (constantSheafAdj ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}
      ((etaleTerminalIsTerminal U.left).isTerminalObj (etaleSliceBackward U)))
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) F a

end AlgebraicGeometry.Scheme.EtaleCohomology

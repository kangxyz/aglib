/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Injective.SectionCycles

/-!
# Degree-zero normalization of geometric cohomology maps

The actual Ext-defined geometric map on additive sheaf cohomology agrees in
 degree zero with the adjoint coefficient map on actual global sections. These
comparisons are independent of fields, quasicoherence, affine hypotheses and
base change. They are extracted from the former field-base-change owner so
that general coefficient comparisons can reuse their single implementation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- In degree zero the Ext construction is the actual composite of sheaf maps. -/
theorem zariskiCohomologyMap_addEquiv₀
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) (x : Sheaf.H.{u + 1} A 0) :
    Abelian.Ext.addEquiv₀ (zariskiCohomologyMap f A B a 0 x) =
      (constantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
        (zariskiPullback f).map (Abelian.Ext.addEquiv₀ x) ≫ a := by
  apply (Abelian.Ext.mk₀_bijective _ _).injective
  rw [Abelian.Ext.mk₀_addEquiv₀_apply]
  conv_lhs => rw [← Abelian.Ext.mk₀_addEquiv₀_apply x]
  change ((Abelian.Ext.mk₀ _).comp
    ((Abelian.Ext.mk₀ _).mapExactFunctor (zariskiPullback f)) (Nat.zero_add 0)).comp
      (Abelian.Ext.mk₀ a) (Nat.add_zero 0) = _
  simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀, Category.assoc]

/-- Constant-sheaf transport was chosen by the global-sections adjunction,
so its effect on degree-zero classes is the actual adjoint coefficient map. -/
theorem zariskiCohomologyMap_equiv₀
    (A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (zariskiPullback f).obj A ⟶ B) (x : Sheaf.H.{u + 1} A 0) :
    Sheaf.H.equiv₀ B isTerminalTop (zariskiCohomologyMap f A B a 0 x) =
      (pushforwardSectionsIso f).hom.app B
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          f.base).homEquiv A B a).hom.app (op ⊤))
          (Sheaf.H.equiv₀ A isTerminalTop x)) := by
  let adjY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop
  let adjX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop
  let adjf := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
  let adj := (adjY.comp adjf).ofNatIsoRight (pushforwardSectionsIso f)
  change integerSheafHomEquiv B
    (Abelian.Ext.addEquiv₀ (zariskiCohomologyMap f A B a 0 x)) = _
  rw [zariskiCohomologyMap_addEquiv₀]
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    (adjX.homEquiv _ _ ((adj.leftAdjointUniq adjX).inv.app _ ≫
      (zariskiPullback f).map (Abelian.Ext.addEquiv₀ x) ≫ a)) = _
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    (adjY.homEquiv _ _
      (adjf.homEquiv _ _ ((zariskiPullback f).map (Abelian.Ext.addEquiv₀ x) ≫ a)) ≫
        (pushforwardSectionsIso f).hom.app B) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rfl

end AlgebraicGeometry.Scheme.Cohomology

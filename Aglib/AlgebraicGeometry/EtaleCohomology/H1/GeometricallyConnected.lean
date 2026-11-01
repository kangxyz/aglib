/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GeometricallyConnected
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteEtaleRigidity
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorClassification
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.GeometricallyConnected

/-! # Original H1 detection under geometrically connected base change

Constructed finite-etale full faithfulness supplies actual torsor-section
lifting. The existing torsor-to-Ext classification and finite-coefficient
representation prove injectivity of the original H1 pullback. No classification
premise, H1-surjectivity, finite-cover essential surjectivity or tame-extension
theorem is assumed. Field-extension statements retain an algebraically closed
base field and allow arbitrary schemes and arbitrary extension fields.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [GeometricallyConnected q]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]

/-- Actual finite-etale section descent detects zero and equality in the
original H1 of every finite locally constant coefficient. -/
theorem h1Pullback_injective_of_geometricallyConnected
    (hE : ∀ U : FiniteEtale X, EffectiveEpi (pullback.fst U.obj.hom q))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Function.Injective (h1Pullback q F) := by
  let ff := FiniteEtale.fullyFaithfulBaseChange_of_geometricallyConnected q hE
  let := ff.full
  exact FiniteEtaleRigidity.h1Pullback_injective_finite_of_full q
    (stacks03AJ X) (stacks03RV X) (stacks03AJ Y) F hF

/-- The fpqc geometric supplier for the original H1 injection. -/
theorem h1Pullback_injective_of_flat_quasiCompact_geometricallyConnected
    [Flat q] [QuasiCompact q]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Function.Injective (h1Pullback q F) :=
  h1Pullback_injective_of_geometricallyConnected q (fun _ => inferInstance) F hF

/-- The fppf geometric supplier for the original H1 injection, without
quasi-compactness. -/
theorem h1Pullback_injective_of_flat_lfp_geometricallyConnected
    [Flat q] [LocallyOfFinitePresentation q]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsFiniteLocallyConstant F) :
    Function.Injective (h1Pullback q F) :=
  h1Pullback_injective_of_geometricallyConnected q (fun _ => inferInstance) F hF

section FieldExtension

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  {Z : Scheme.{u}} (p : Z ⟶ Spec (.of k))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Z)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1}
    (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K)))))]

/-- The original H0 pullback is bijective after any field extension of an
algebraically closed base, for finite locally constant coefficients. -/
theorem h0Pullback_bijective_fieldExtension
    (F : AbelianSheaf.{u, u + 1} Z) (hF : IsFiniteLocallyConstant F) :
    Function.Bijective
      (h0Pullback (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) F) := by
  let := Scheme.Geometrically.fieldSpec_geometricallyConnected k K
  exact h0Pullback_bijective_of_flat_quasiCompact_geometricallyConnected
    (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) F hF

/-- The original H1 pullback is injective after the same field extension.
This is not the missing surjectivity or tame-cover-extension assertion. -/
theorem h1Pullback_injective_fieldExtension
    (F : AbelianSheaf.{u, u + 1} Z) (hF : IsFiniteLocallyConstant F) :
    Function.Injective
      (h1Pullback (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) F) := by
  let := Scheme.Geometrically.fieldSpec_geometricallyConnected k K
  exact h1Pullback_injective_of_flat_quasiCompact_geometricallyConnected
    (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) F hF

end FieldExtension

end AlgebraicGeometry.Scheme.EtaleCohomology

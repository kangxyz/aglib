/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.PurelyInseparableFullness
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic

/-! # Original H1 detection by a purely inseparable field base change

Finite-etale fullness detects the original Ext-based H1 classes. The source
and target Ext universes are independent, and the field extension may be infinite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields.PurelyInseparable

universe u w w'

attribute [local instance] hasSheafifyLarge

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] {X : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X] (p : X ⟶ Spec (.of K))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap K L)))]

/-- The original H1 map is injective for every finite locally constant
coefficient under a purely inseparable field base change of a qcqs scheme. -/
theorem h1Pullback_injective_finite
    (T : AbelianSheaf.{u, u + 1} X) (hT : IsFiniteLocallyConstant T) :
    Function.Injective (h1Pullback (pullback.fst p (Spec.algebraMap K L)) T) := by
  let := FiniteEtale.PurelyInseparable.projectionBaseChange_full K L p
  exact FiniteEtaleRigidity.h1Pullback_injective_finite_of_full
    (pullback.fst p (Spec.algebraMap K L)) (stacks03AJ X) (stacks03RV X)
    (stacks03AJ (pullback p (Spec.algebraMap K L))) T hT

/-- The literal constant-coefficient H1 map, including its canonical coefficient
transport, is injective in independent source and target Ext universes. -/
theorem constantH1Pullback_injective (A : Type u) [AddCommGroup A] [Finite A] :
    Function.Injective
      (ConstantFinite.pullbackH1 A (pullback.fst p (Spec.algebraMap K L))) := by
  let := FiniteEtale.PurelyInseparable.projectionBaseChange_full K L p
  exact ConstantFinite.pullbackH1_injective_of_full A (pullback.fst p (Spec.algebraMap K L))

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields.PurelyInseparable

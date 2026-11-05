/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FinitePresentable
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Compactness of constant module coefficients on qcqs schemes

The actual constant-sheaf/global-sections adjunction transports finite
presentation. This includes infinite coefficient rings and infinite additive
modules. No local-trivialization descent claim is made here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

variable (R : Type r) [Ring R] (X : Scheme.{u})

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

/-- Constant finitely presented native module sheaves on a qcqs scheme are
categorically finitely presentable, with unchanged coefficient ring and module. -/
theorem isFinitelyPresentable_constant_of_finitePresentation
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : ModuleCat.{u + 1} R) [Module.FinitePresentation R M] :
    IsFinitelyPresentable.{u + 1}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) := by
  let : PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    ModuleCat.Sheaf.forget_preservesFilteredColimits R
  let : IsFinitelyPresentable.{u + 1} M :=
    ModuleCat.isFinitelyPresentable_of_finitePresentation M
  let : CompactSpace (etaleTerminal X).left := inferInstanceAs (CompactSpace X)
  let : QuasiSeparatedSpace (etaleTerminal X).left :=
    inferInstanceAs (QuasiSeparatedSpace X)
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
        (op (etaleTerminal X))) := ⟨fun _ _ _ =>
    Continuity.qcqsModuleSections_preservesFilteredColimits R (etaleTerminal X)⟩
  let : ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
      (op (etaleTerminal X))).IsCardinalAccessible Cardinal.aleph0.{u + 1} :=
    Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mpr inferInstance
  exact (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R)
    (etaleTerminalIsTerminal X)).isCardinalPresentable_leftAdjoint_obj
      Cardinal.aleph0.{u + 1} M

/-- Over a left Noetherian ring, finite-type constant module coefficients are compact. -/
theorem isFinitelyPresentable_constant_of_finite [IsNoetherianRing R]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M] :
    IsFinitelyPresentable.{u + 1}
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact isFinitelyPresentable_constant_of_finitePresentation R X M

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

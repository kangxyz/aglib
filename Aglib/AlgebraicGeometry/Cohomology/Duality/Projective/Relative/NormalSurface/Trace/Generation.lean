/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.BaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.DegreeZero
public import Aglib.AlgebraicGeometry.Modules.Generators.Counit

/-!
# Sections of the original inverse-trace pullback

The original adjoint of an invertible trace is surjective on global sections,
as is its actual pullback through a flat Cartesian square with quasicoherent
coefficient and qcqs original morphism. The latter assertion uses the original
base-change mate and counit, not preservation of section surjectivity by an
arbitrary pullback. No generation or canonical-frame conclusion is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The original inverse-trace adjoint is surjective on global sections. -/
theorem ordinaryTracePullback_app_top_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : X.Modules} {N : Y.Modules} (τ : (pushforward f).obj M ⟶ N) [IsIso τ] :
    Function.Surjective ((ordinaryTracePullback f τ).val.app (op ⊤)) := by
  let e := (pullback f).mapIso (asIso τ).symm
  rw [ordinaryTracePullback_counit f τ]
  exact (counit_app_top_surjective f M).comp
    (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e).hom).2

/-- The original flat Cartesian pullback of the inverse-trace adjoint is
surjective on sections, through its actual base-change mate and counit. -/
theorem ordinaryTracePullback_baseChange_app_top_surjective
    {W X T Y : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ Y) (j : T ⟶ Y)
    (h : IsPullback a b f j) [Flat j] [QuasiCompact f] [QuasiSeparated f]
    {M : X.Modules} [M.IsQuasicoherent] {N : Y.Modules}
    (τ : (pushforward f).obj M ⟶ N) [IsIso τ] :
    Function.Surjective (((pullback a).map (ordinaryTracePullback f τ)).val.app (op ⊤)) := by
  let : IsIso ((cartesianBaseChangeMap a b f j h).app M) :=
    canonicalTraceOrdinaryBaseChange_isIso a b f j h M
  let e := (ordinaryTracePullbackSquareIso a b f j h).app N ≪≫
    (pullback b).mapIso ((pullback j).mapIso (asIso τ).symm ≪≫
      asIso ((cartesianBaseChangeMap a b f j h).app M))
  rw [ordinaryTracePullback_baseChange a b f j h τ]
  exact (counit_app_top_surjective b ((pullback a).obj M)).comp
    (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation W.ringCatSheaf (op ⊤)).mapIso e).hom).2

end AlgebraicGeometry.Scheme.Modules

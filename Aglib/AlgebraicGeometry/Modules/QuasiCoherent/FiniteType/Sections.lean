/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineOpenSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# Sections and pullbacks of finite-type sheaves

* `Scheme.Modules.QuasiCoherent.finite_sections_of_affineLocallyFiniteType`: for a sheaf `M`
  satisfying `affineLocallyFiniteType X M`, the sections `Γ(M, U)` on an affine open `U` form a
  finitely generated `Γ(X, U)`-module. The chart condition gives finite generation of the global
  sections of the restriction along `Spec Γ(X, U) ⟶ X`, and
  `AffineOpenSections.toSpecTopSectionsLinearEquiv` identifies them with `Γ(M, U)`.
* `Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_pullback_of_finitePresentation`: the
  pullback of a finitely presented sheaf along an arbitrary morphism satisfies the finite-type
  chart condition.

The pullback of a quasi-coherent sheaf of finite type along an arbitrary morphism is again of
finite type, but Aglib does not yet supply that theorem; the finite-type chart condition of a
pullback is available from finite presentation (here) or from a locally Noetherian target
(`affineLocallyFiniteType_pullback`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

/-- On an affine open `U`, the sections of a quasi-coherent sheaf of finite type form a finitely
generated `Γ(X, U)`-module. -/
theorem finite_sections_of_affineLocallyFiniteType {X : Scheme.{u}} (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (U : X.affineOpens) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have hU : IsAffineOpen U.1 := U.2
  have h : Module.Finite Γ(X, U) Γ(M.restrict hU.fromSpec, ⊤) := (hM Γ(X, U) hU.fromSpec).2
  exact Module.Finite.equiv (AffineOpenSections.toSpecTopSectionsLinearEquiv M hU).symm

/-- Under finite presentation, the pullback of a quasi-coherent sheaf along any morphism satisfies
the finite-type chart condition. -/
theorem affineLocallyFiniteType_pullback_of_finitePresentation {S T : Scheme.{u}} (g : T ⟶ S)
    (F : S.Modules) [F.IsFinitePresentation] :
    affineLocallyFiniteType T ((Scheme.Modules.pullback g).obj F) :=
  affineLocallyFiniteType_of_finitePresentation _

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent

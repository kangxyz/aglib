/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Mathlib.Algebra.Homology.QuasiIso

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/OpenCoverQuasiIso.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 48]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Quasi-isomorphisms detected on an original open cover

The exact original restriction functors retain their homology comparisons.
Their jointly conservative action on module sheaves detects quasi-isomorphisms
of complexes of any shape. The cover need not be finite.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X)
  [∀ i, IsOpenImmersion (a i)] (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
include hcover
/-- Original complex quasi-isomorphisms are detected on a genuine open cover. -/
theorem quasiIso_of_restrict_openCover {κ : Type w} {c : ComplexShape κ}
    {K L : HomologicalComplex X.Modules c} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso (((Scheme.Modules.restrictFunctor (a i)).mapHomologicalComplex c).map f)) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  apply isIso_of_restrict_openCover Y a hcover
  intro i
  let F := Scheme.Modules.restrictFunctor (a i)
  let φ := (shortComplexFunctor X.Modules c n).map f
  let := hf i
  have hφ : ShortComplex.QuasiIso (F.mapShortComplex.map φ) :=
    (quasiIsoAt_iff (((Scheme.Modules.restrictFunctor (a i)).mapHomologicalComplex c).map f) n).mp
      inferInstance
  exact (NatIso.isIso_map_iff (ShortComplex.homologyFunctorIso F) φ).mp
    (show IsIso ((F.mapShortComplex ⋙ ShortComplex.homologyFunctor (Y i).Modules).map φ) from
      (ShortComplex.quasiIso_iff _).mp hφ)
end AlgebraicGeometry.Scheme.Modules

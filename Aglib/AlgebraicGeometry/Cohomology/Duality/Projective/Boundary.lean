/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Pairing
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Exact

/-!
# Original Serre pairings and connecting maps

Composing an Ext class with the actual short exact extension class in its source pairs
with the original cohomology connecting map on the other input. This is literal native
Yoneda associativity together with the proved original Ext/cohomology boundary identity.
No sign adjustment or replacement boundary map is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- The canonical pairing identifies the original contravariant Ext boundary with the
original cohomology boundary on the other input, with exactly the native positive sign. -/
theorem projectiveSerrePairing_connecting (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace R ι).Modules) (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 + j = n)
    (y : Ext.{u + 1} S.X₁ (twistingSheaf R ι (-(Fintype.card ι : ℤ))) j)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) S.X₃) i) :
    projectiveSerrePairing R ι n e S.X₃ i (j + 1) (by omega)
        (hS.extClass.comp y (show 1 + j = j + 1 by omega)) x =
      projectiveSerrePairing R ι n e S.X₁ (i + 1) j hij y
        (moduleCohomologyConnectingOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) S hS i x) := by
  rw [projectiveSerrePairing_apply, projectiveSerrePairing_apply,
    moduleExtCohomologyAddEquiv_symm_connectingOfHom]
  exact congrArg (fun z => projectiveTrace R ι n e (moduleExtCohomologyMap
    (ProjectiveSpace R ι) (twistingSheaf R ι (-(Fintype.card ι : ℤ))) n z))
    (Ext.comp_assoc ((moduleExtCohomologyAddEquiv (ProjectiveSpace R ι) S.X₃ i).symm x)
      hS.extClass y rfl (show 1 + j = j + 1 by omega) hij).symm

end AlgebraicGeometry.Scheme.Cohomology

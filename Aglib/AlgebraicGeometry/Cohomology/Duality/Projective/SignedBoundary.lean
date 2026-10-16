/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Boundary
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The native signed Ext connecting map in the original Serre pairing

Mathlib's `Ext.δ` is `(-1)^(j+1)` times precomposition with the original extension
class in target degree `j+1`. The original Yoneda/trace pairing therefore carries this
exact sign when it pairs the native Ext connecting map with the original cohomology
connecting map. The unsigned extension-class identity remains in `Boundary`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- The original pairing retains exactly the sign in Mathlib's native contravariant
Ext connecting homomorphism. This requires no field or coherence hypothesis. -/
theorem projectiveSerrePairing_extδ (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace R ι).Modules) (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 + j = n)
    (y : Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      S.X₁ (twistingSheaf R ι (-(Fintype.card ι : ℤ))) j)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) S.X₃) i) :
    projectiveSerrePairing R ι n e S.X₃ i (j + 1) (by omega)
        (Ext.δ (C := (ProjectiveSpace R ι).Modules) hS j (j + 1) rfl y) x =
      Int.negOnePow (j + 1 : ℕ) •
        projectiveSerrePairing R ι n e S.X₁ (i + 1) j hij y
          (moduleCohomologyConnectingOfHom (ProjectiveSpace R ι)
            ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) S hS i x) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S.X₃ i
  rw [Ext.δ_apply, Units.smul_def, map_zsmul]
  change (Int.negOnePow (j + 1 : ℕ)).val •
    (projectiveSerrePairing R ι n e S.X₃ i (j + 1) (by omega)
      (hS.extClass.comp y (show 1 + j = j + 1 by omega)) x) = _
  rw [projectiveSerrePairing_connecting R ι n e S hS i j hij]
  rfl

end AlgebraicGeometry.Scheme.Cohomology

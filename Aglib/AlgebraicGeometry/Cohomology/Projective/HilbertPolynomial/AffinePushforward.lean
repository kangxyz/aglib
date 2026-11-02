/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.GlobalSections

/-!
# Original affine pushforwards with the same structural field map

Two original affine maps from the same scheme to projective space, with
the same structural field map, give the same cohomology dimensions and
Euler characteristic for the same quasicoherent source coefficient. The
existing native affine cohomology equivalence is used for each map; the
structural triangle identifies their actual scalar actions on the same
original source cohomology group.

No new cohomology realization, resolution input or rank multiplication
formula is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u) {X : Scheme.{u}}

/-- Original affine direct images under maps with the same field
structure have the same original cohomology dimensions. -/
theorem projectiveCohomologyDim_pushforward_eq_of_toSpec_eq
    (a b : X ⟶ ProjectiveSpace k ι) [IsAffineHom a] [IsAffineHom b]
    (hab : a ≫ toSpec k ι = b ≫ toSpec k ι) (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    projectiveCohomologyDim k ι ((Scheme.Modules.pushforward a).obj M) q =
      projectiveCohomologyDim k ι ((Scheme.Modules.pushforward b).obj M) q := by
  let α := projectiveConstants k ι
  have hα : a.appTop.hom.comp α = b.appTop.hom.comp α := by
    have h := congrArg (fun f : X ⟶ Spec (.of k) =>
      f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom) hab
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc,
      α, projectiveConstants] using h
  let D (β : k →+* Γ(X, ⊤)) : ℕ :=
    letI := moduleCohomologyModuleOfHom X β M q
    Module.finrank k (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)
  have ha : projectiveCohomologyDim k ι ((Scheme.Modules.pushforward a).obj M) q =
      D (a.appTop.hom.comp α) := by
    let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) α
      ((Scheme.Modules.pushforward a).obj M) q
    let := moduleCohomologyModuleOfHom X (a.appTop.hom.comp α) M q
    exact (moduleAffinePushforwardCohomologyLinearEquiv a α M q).finrank_eq
  have hb : projectiveCohomologyDim k ι ((Scheme.Modules.pushforward b).obj M) q =
      D (b.appTop.hom.comp α) := by
    let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) α
      ((Scheme.Modules.pushforward b).obj M) q
    let := moduleCohomologyModuleOfHom X (b.appTop.hom.comp α) M q
    exact (moduleAffinePushforwardCohomologyLinearEquiv b α M q).finrank_eq
  exact ha.trans ((congrArg D hα).trans hb.symm)

/-- The actual affine pushforward Euler characteristics agree for the
same original coefficient and the same structural field map. -/
theorem projectiveEulerChar_pushforward_eq_of_toSpec_eq
    (a b : X ⟶ ProjectiveSpace k ι) [IsAffineHom a] [IsAffineHom b]
    (hab : a ≫ toSpec k ι = b ≫ toSpec k ι) (M : X.Modules) [M.IsQuasicoherent] :
    projectiveEulerChar k ι ((Scheme.Modules.pushforward a).obj M) =
      projectiveEulerChar k ι ((Scheme.Modules.pushforward b).obj M) := by
  unfold projectiveEulerChar
  apply finsum_congr
  intro q
  rw [projectiveCohomologyDim_pushforward_eq_of_toSpec_eq k ι a b hab M q]

end AlgebraicGeometry.Scheme.Cohomology

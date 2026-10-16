/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.GeometricTop
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars

/-!
# Whole-space restriction is the original geometric open pullback

The original restriction from whole-space open cohomology to an open,
followed by the existing restricted-module cohomology equivalence, is the
actual geometric cohomology map for the original restriction adjunction
unit. The structural scalar actions and native open transports are retained.
No quasicoherence, flatness or geometric finiteness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original whole-space open restriction agrees, under the original
linear comparisons, with actual geometric pullback along the open immersion
and its original module restriction unit. -/
theorem moduleHPrimeOpenLinearEquiv_restriction_top_geometric (X : Scheme.{u})
    {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤)) (M : X.Modules)
    (V : X.Opens) (n : ℕ) (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n ⊤) :
    letI := moduleHPrimeModuleOfHom X α M n ⊤
    letI := moduleHPrimeModuleOfHom X α M n V
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom V.toScheme (V.ι.appTop.hom.comp α) (M.restrict V.ι) n
    moduleHPrimeOpenLinearEquiv X α M V n
        (moduleHPrimeRestrictionOfHom X α M n (homOfLE (show V ≤ ⊤ from le_top)) x) =
      moduleCohomologyMapAlong V.ι ((Scheme.Modules.restrictAdjunction V.ι).unit.app M) n
        (moduleHPrimeTopLinearEquivOfHom X α M n x) := by
  let := moduleHPrimeModuleOfHom X α M n ⊤
  let := moduleHPrimeModuleOfHom X α M n V
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom V.toScheme (V.ι.appTop.hom.comp α) (M.restrict V.ι) n
  rw [moduleHPrimeOpenLinearEquiv_geometric]
  let A := moduleAddSheaf X M
  let B := moduleAddSheaf V.toScheme (M.restrict V.ι)
  let a := moduleCoefficientPullback V.ι ((Scheme.Modules.restrictAdjunction V.ι).unit.app M)
  let g := zariskiCohomologyOpenMap V.ι A B a n
  let i : V ⟶ (⊤ : X.Opens) := homOfLE le_top
  let k : (⊤ : V.toScheme.Opens) ⟶ V.ι ⁻¹ᵁ V := eqToHom V.ι_preimage_self.symm
  have hn := congrArg (fun f => f x) (g.naturality i.op)
  change g.app (op V) ((A.cohomologyPresheaf n).map i.op x) =
    (B.cohomologyPresheaf n).map ((Opens.map V.ι.base).op.map i.op)
      (g.app (op ⊤) x) at hn
  change sheafHPrimeTopAddEquiv V.toScheme B n
      ((B.cohomologyPresheaf n).map k.op
        (g.app (op V) ((A.cohomologyPresheaf n).map i.op x))) =
    moduleCohomologyMapAlong V.ι ((Scheme.Modules.restrictAdjunction V.ι).unit.app M) n
      (sheafHPrimeTopAddEquiv X A n x)
  rw [hn]
  change sheafHPrimeTopAddEquiv V.toScheme B n
      (((B.cohomologyPresheaf n).map ((Opens.map V.ι.base).op.map i.op) ≫
        (B.cohomologyPresheaf n).map k.op) (g.app (op ⊤) x)) = _
  rw [← (B.cohomologyPresheaf n).map_comp]
  have h : (Opens.map V.ι.base).op.map i.op ≫ k.op =
      𝟙 (op (⊤ : V.toScheme.Opens)) := Subsingleton.elim _ _
  rw [h]
  erw [(B.cohomologyPresheaf n).map_id]
  exact sheafHPrimeTopAddEquiv_geometric V.ι A B a n x

end AlgebraicGeometry.Scheme.Cohomology

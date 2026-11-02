/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Coproduct
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit
public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FibreDimension

/-! # Relative flatness of locally free coefficients

Use the actual locally free cover, its original restricted basis, flatness
of free coproducts and the original stalk restriction comparison. No
Noetherianity, properness, finite-rank bound or cohomology theorem is needed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- A locally free coefficient is flat over the base of a flat morphism. -/
theorem relativeFlat_of_isLocallyFree_of_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] (M : X.Modules)
    [SheafOfModules.IsLocallyFree.{u} M] : relativeFlat f M := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  intro x
  obtain ⟨i, hi⟩ := (_root_.Opens.coversTop_iff X q.X).mp q.coversTop |>.exists_mem x
  let U : X.Opens := q.X i
  let E : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (q.generators i).I :=
    (restrictFunctorIsoPullback U.ι).app M ≪≫ (localBasisRestrictedIso M q hq i).symm
  have hfree : relativeFlat (U.ι ≫ f)
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (q.generators i).I) :=
    relativeFlat_coproduct (U.ι ≫ f)
      (fun _ : (q.generators i).I => SheafOfModules.unit U.toScheme.ringCatSheaf)
      (fun _ => relativeFlat_unit_of_flat (U.ι ≫ f))
  have hlocal : relativeFlat (U.ι ≫ f) (M.restrict U.ι) :=
    relativeFlat_of_iso (U.ι ≫ f) E hfree
  exact flat_stalk_of_flat_stalk_restrict U.ι f M ⟨x, hi⟩ (hlocal ⟨x, hi⟩)

end AlgebraicGeometry.Scheme.Modules

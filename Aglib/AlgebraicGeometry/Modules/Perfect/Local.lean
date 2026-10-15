/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Perfect.Restriction
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Local perfectness of module-sheaf complexes

Near every point, the actual restricted complex has an isomorphism in the native
derived category to a strict perfect complex. `Perfect` is the full category of
CHAIN COMPLEXES and chain maps satisfying this property, not a derived
subcategory. No global strict representative is asserted.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Local.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `706d05324a254c5734c9e6138888cdc875033cf40a4298e2ada16f2f5242b82f`.
Admitted subset: locallyPerfect, Perfect, zero/isomorphism/quasi-isomorphism invariance and
  strictToPerfect; native DerivedCategory and Q replace the source localization notation.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open scoped ZeroObject

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- Use the constructed native derived category in morphism universe `u + 1`. -/
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- A sheaf complex is perfect when it is locally isomorphic, in the actual
quasi-isomorphism localization, to a strict perfect complex. -/
def locallyPerfect (X : Scheme.{u}) : ObjectProperty (CochainComplex X.Modules ℤ) := fun K ↦
  ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ ∃ P : StrictPerfect U.toScheme,
    Nonempty ((DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj K) ≅
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj P.obj)

/-- The full category of genuinely locally perfect complexes. -/
abbrev Perfect (X : Scheme.{u}) := (locallyPerfect X).FullSubcategory

variable {X : Scheme.{u}}

/-- Strict perfectness implies local perfectness on every scheme. The
converse is deliberately not asserted. -/
theorem locallyPerfect_of_strictPerfect {K : CochainComplex X.Modules ℤ} (hK : strictPerfect X K) :
    locallyPerfect X K := by
  intro x
  refine ⟨⊤, by simp, ⟨(restrict (⊤ : X.Opens).ι).obj K,
    strictPerfect_restrict _ hK⟩, ⟨Iso.refl _⟩⟩

/-- Local perfectness is preserved by actual chain isomorphisms. -/
theorem locallyPerfect_of_iso {K L : CochainComplex X.Modules ℤ} (e : K ≅ L)
    (hK : locallyPerfect X K) : locallyPerfect X L := by
  intro x
  obtain ⟨U, hx, P, ⟨eP⟩⟩ := hK x
  exact ⟨U, hx, P, ⟨(DerivedCategory.Q (C := U.toScheme.Modules)).mapIso ((restrict U.ι).mapIso
    e.symm) ≪≫ eP⟩⟩

instance locallyPerfect_closedUnderIsomorphisms : (locallyPerfect X).IsClosedUnderIsomorphisms where
  of_iso e hK := locallyPerfect_of_iso e hK

/-- The zero complex is locally perfect. -/
instance locallyPerfect_containsZero : (locallyPerfect X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, locallyPerfect_of_strictPerfect
    (strictPerfect_of_isZero (isZero_zero _))⟩

/-- A quasi-isomorphism preserves local perfectness in both directions.
This uses actual restriction and inversion of quasi-isomorphisms. -/
theorem locallyPerfect_iff_of_quasiIso {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) [QuasiIso f] :
    locallyPerfect X K ↔ locallyPerfect X L := by
  constructor
  · intro hK x
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := hK x
    exact ⟨U, hx, P, ⟨(asIso ((DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict
      U.ι).map f))).symm ≪≫ eP⟩⟩
  · intro hL x
    obtain ⟨U, hx, P, ⟨eP⟩⟩ := hL x
    exact ⟨U, hx, P, ⟨asIso ((DerivedCategory.Q (C := U.toScheme.Modules)).map ((restrict U.ι).map
      f)) ≪≫ eP⟩⟩

/-- The fully faithful inclusion of strict perfect complexes into locally
perfect complexes. This is not asserted to be essentially surjective. -/
def strictToPerfect (X : Scheme.{u}) : StrictPerfect X ⥤ Perfect X :=
  ObjectProperty.ιOfLE (fun _ h ↦ locallyPerfect_of_strictPerfect h)

/-- The underlying sheaf complex is unchanged by this inclusion. -/
theorem strictToPerfect_comp_inclusion (X : Scheme.{u}) :
    strictToPerfect X ⋙ (locallyPerfect X).ι = (strictPerfect X).ι := rfl

end AlgebraicGeometry.Scheme.Modules.Complex

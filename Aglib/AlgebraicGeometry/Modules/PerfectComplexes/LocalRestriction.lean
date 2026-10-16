/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Open restriction and local perfectness

Actual restriction composition and the native exact derived restriction preserve
local perfectness. The factorization is the native natural isomorphism, including
its actual components; no parallel Gabriel–Zisman lift is introduced.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/LocalRestriction.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `9e6fda16dcd3977cb3553d5961036c2d6db5dbd47524c7b48744fc4ab42b23a1`.
Admitted subset: restriction composition, restriction of actual derived isomorphisms,
  derived-isomorphism invariance and perfectRestrict; derivedRestrict uses the native exact
  functor with its factorization.
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

attribute [local instance] Scheme.Modules.standardHasDerivedCategory

variable {V U X : Scheme.{u}}


variable (j : U ⟶ X) [IsOpenImmersion j]


/-- Local perfectness depends only on the isomorphism class in the actual
quasi-isomorphism localization. -/
theorem locallyPerfect_iff_of_derivedIso {K L : CochainComplex X.Modules ℤ}
    (e : (DerivedCategory.Q (C := X.Modules)).obj K ≅ (DerivedCategory.Q (C := X.Modules)).obj L) :
    locallyPerfect X K ↔ locallyPerfect X L := by
  constructor
  · intro hK x
    obtain ⟨O, hx, P, ⟨eP⟩⟩ := hK x
    exact ⟨O, hx, P, ⟨(restrictDerivedIso O.ι e).symm ≪≫ eP⟩⟩
  · intro hL x
    obtain ⟨O, hx, P, ⟨eP⟩⟩ := hL x
    exact ⟨O, hx, P, ⟨restrictDerivedIso O.ι e ≪≫ eP⟩⟩

/-- Local perfectness is preserved by open restriction. -/
theorem locallyPerfect_restrict {K : CochainComplex X.Modules ℤ} (hK : locallyPerfect X K) :
    locallyPerfect U ((restrict j).obj K) := by
  intro x
  obtain ⟨O, hx, P, ⟨eP⟩⟩ := hK (j x)
  let T : U.Opens := j ⁻¹ᵁ O
  let k : T.toScheme ⟶ O.toScheme := j ∣_ O
  have hk : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (j ∣_ O))
  let e : restrict j ⋙ restrict T.ι ≅ restrict O.ι ⋙ restrict k :=
    restrictCompIso T.ι j ≪≫
      eqToIso (restrict_congr (show T.ι ≫ j = k ≫ O.ι from (morphismRestrict_ι j O).symm)) ≪≫
      (restrictCompIso k O.ι).symm
  refine ⟨T, hx, ⟨(restrict k).obj P.obj, strictPerfect_restrict k P.property⟩, ?_⟩
  exact ⟨(DerivedCategory.Q (C := T.toScheme.Modules)).mapIso (e.app K) ≪≫ restrictDerivedIso k eP⟩

/-- Actual open restriction on the full category of locally perfect complexes. -/
def perfectRestrict : Perfect X ⥤ Perfect U :=
  (locallyPerfect U).lift ((locallyPerfect X).ι ⋙ restrict j)
    (fun K ↦ locallyPerfect_restrict j K.property)

end AlgebraicGeometry.Scheme.Modules.Complex

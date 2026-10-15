/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Perfect.Exact
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction

/-! # Open restriction of strict perfect complexes

Use the canonical ordinary complex restriction. Term bounds and finite local
freeness are preserved, as are the actual inherited short exact sequences.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Restriction.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `00896057a7423474dc1d4f8b6743337ce31c9f93490cbf5d11989649ccf1d3f3`.
Admitted subset: strictPerfect_restrict, strictRestrict and its additivity, strictExactRestrict;
  ordinary restriction is reused from Modules.Complex.Basic.
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

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Strict perfectness survives actual geometric open restriction. -/
theorem strictPerfect_restrict {K : CochainComplex X.Modules ℤ} (hK : strictPerfect X K) :
    strictPerfect U ((restrict j).obj K) := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hK
  refine ⟨⟨a, b, fun n hn ↦ (Scheme.Modules.restrictFunctor j).map_isZero (hb n hn)⟩, ?_⟩
  intro n
  let : IsFiniteLocallyFree X (K.X n) := hv n
  exact finiteLocallyFree_restrict j (K.X n)

/-- The restriction functor on strict perfect complexes. -/
def strictRestrict : StrictPerfect X ⥤ StrictPerfect U :=
  (strictPerfect U).lift ((strictPerfect X).ι ⋙ restrict j)
    (fun K ↦ strictPerfect_restrict j K.property)

instance strictRestrict_additive : (strictRestrict j).Additive := by
  unfold strictRestrict
  infer_instance

/-- Restriction preserves the actual inherited short exact sequences. -/
def strictExactRestrict : CategoryTheory.ExactCategory.ExactFunctor (strictExactStructure X)
  (strictExactStructure U)
  where
  toFunctor := strictRestrict j
  map_conflation S hS := by
    change ((S.map (strictPerfect X).ι).map (restrict j)).ShortExact
    exact hS.map_of_exact _


end AlgebraicGeometry.Scheme.Modules.Complex

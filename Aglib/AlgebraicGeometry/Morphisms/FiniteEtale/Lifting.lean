/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Connectedness
public import Aglib.CategoryTheory.Galois.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Actual finite-etale cover comparison and lifting

An actual base-change comparison transports rank from a displayed point of
the source to a preconnected target. A pointwise supplied equivalence of the
actual finite-etale categories transports connectedness in both directions,
including the very same chosen inverse object. No proper-Henselian comparison
or model-existence supplier is proved or assumed implicitly.

Source: unmarked slices of
`R5Lab.AlgebraicGeometry.Curves.LocalModels.CyclicCovers.GeneralLift`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`e62cfc4cb7711bac753202a8bcf27fbf4f11a52cf87ccf144ffb6df9b5671075`,
and `.SourceModel`, SHA-256
`bb898d7efd9798cb5657bffab1cf0ad44d163ab82a1823b05aa0daad889c2fae`.
The actual schemes, covers, maps, comparison isomorphism and witness point
replace only the application records that supplied those same data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale.Lifting

universe u
variable {S T : Scheme.{u}} (i : S ⟶ T)

/-- The original comparison and rank at its actual point determine the rank
on a preconnected target. The comparison's forward map is retained. -/
theorem finrank_eq_of_baseChangeIso [PreconnectedSpace T]
    (C : FiniteEtale T) (C₀ : FiniteEtale S) (e : (baseChange i).obj C ≅ C₀)
    (s : S) {n : ℕ} (hs : C₀.obj.hom.finrank s = n) (t : T) :
    C.obj.hom.finrank t = n := by
  have hr : ((baseChange i).obj C).obj.hom.finrank s = n := by
    have hw := Over.w e.hom.hom
    rw [← hw, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hs
  change (pullback.snd C.obj.hom i).finrank s = n at hr
  rw [Scheme.Hom.finrank_pullback_snd] at hr
  exact (C.obj.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace
    t (i s)).trans hr

/-- Positive rank at the original comparison point makes the same cover
surjective. This changes neither the cover nor its structural morphism. -/
theorem surjective_of_baseChangeIso [PreconnectedSpace T]
    (C : FiniteEtale T) (C₀ : FiniteEtale S) (e : (baseChange i).obj C ≅ C₀)
    (s : S) {n : ℕ} (hs : C₀.obj.hom.finrank s = n) (hn : 0 < n) :
    Surjective C.obj.hom := by
  apply (Scheme.Hom.one_le_finrank_iff_surjective _).mp
  intro t
  rw [finrank_eq_of_baseChangeIso i C C₀ e s hs t]
  exact hn

section Equivalence

variable [(baseChange i).IsEquivalence]

/-- A supplied actual finite-etale base-change equivalence preserves
connectedness of the underlying cover, over arbitrary base schemes. -/
theorem connectedSpace_obj (C : FiniteEtale T) [ConnectedSpace C.obj.left] :
    ConnectedSpace ((baseChange i).obj C).obj.left := by
  let : PreGaloisCategory.IsConnected C :=
    Connectedness.categoricalConnected_of_connectedSpace C
  let : PreGaloisCategory.IsConnected ((baseChange i).obj C) :=
    PreGaloisCategory.isConnected_obj_of_equivalence (baseChange i) C
  exact Connectedness.connectedSpace_of_categoricalConnected _

/-- The same chosen inverse cover has connected underlying scheme when the
supplied cover does. The equivalence remains an explicit pointwise input. -/
theorem connectedSpace_inv_obj (C₀ : FiniteEtale S) [ConnectedSpace C₀.obj.left] :
    ConnectedSpace ((baseChange i).inv.obj C₀).obj.left := by
  let : PreGaloisCategory.IsConnected C₀ :=
    Connectedness.categoricalConnected_of_connectedSpace C₀
  let : PreGaloisCategory.IsConnected ((baseChange i).inv.obj C₀) :=
    PreGaloisCategory.isConnected_obj_of_equivalence (baseChange i).inv C₀
  exact Connectedness.connectedSpace_of_categoricalConnected _

end Equivalence

end AlgebraicGeometry.Scheme.FiniteEtale.Lifting

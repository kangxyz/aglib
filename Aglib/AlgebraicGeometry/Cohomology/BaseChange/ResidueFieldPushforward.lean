/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.ResidueFieldConcentration
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback

/-!
# Locally free direct images from residue-field fibre vanishing

Let `f : X ⟶ S` be proper, flat and locally of finite presentation over a locally Noetherian
`S`, and `M` a finite locally free module sheaf on `X` whose higher cohomology vanishes on every
fibre `X_s`, `s ∈ S`. On an open `U ⊆ S` where `h^0(X_s, M_s) = r`, the direct image of `M`
along the base change `X_U ⟶ U` has rank `r` and its formation commutes with every base change
`T ⟶ U` (`sheafHasRank_and_isIso_moduleBaseChangeMap_of_modulePointFiberCohomology`). The level
sets of `h^0` are open and closed (`isClopen_setOf_modulePointFiberCohomologyDimension_zero_eq`),
so `S` is covered by such opens.

This is statement 15a of the Picard plan row F15, the locally free regime of Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, 3.10, pp. 24–25, as used in the proof of Thm 4.8, p. 30.
It assumes that all higher fibre cohomology vanishes ((4.8.3), p. 29, with `m = 0`), which is
stronger than 3.10 (v), and concludes that `E = f_*M` is locally free and commutes with base
change, so that `Q = E^∨` is locally free (3.10 (i)). The cohomology and base change input
is main's `localFreeCohomologyBaseChange_of_isLocallyNoetherian` (Stacks Project, Tag 0D4E for the
corresponding statement with vanishing higher direct images).
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)

/-- On an open of the base where `h^0(X_s, M_s) = r` and the higher fibre cohomology vanishes,
the direct image along the restricted family has rank `r` and commutes with every base change
(the locally free regime of Kleiman, 3.10, pp. 24–25, under the all-degree vanishing (4.8.3),
p. 29, with `m = 0`, which is stronger than 3.10 (v)). -/
theorem sheafHasRank_and_isIso_moduleBaseChangeMap_of_modulePointFiberCohomology
    [IsLocallyNoetherian S] [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
    [Modules.IsFiniteLocallyFree X M]
    (hpos : ∀ (s : S) (n : ℕ), 0 < n → Subsingleton (modulePointFiberCohomology f M n s))
    (r : ℕ) (U : S.Opens) (hU : ∀ s ∈ U, modulePointFiberCohomologyDimension f M 0 s = r) :
    Modules.SheafHasRank ((Modules.pushforward (Limits.pullback.snd f U.ι)).obj
        ((Modules.pullback (Limits.pullback.fst f U.ι)).obj M)) r ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ U.toScheme), IsIso (Modules.moduleBaseChangeMap
        (Limits.pullback.snd f U.ι) g
        ((Modules.pullback (Limits.pullback.fst f U.ι)).obj M)) := by
  have hc := fibreCohomologyConcentrated_pullback_of_range_subset f M U.ι r
    (by
      rintro s ⟨w, rfl⟩
      exact hU _ (by simp))
    (fun s _ => hpos s)
  exact localFreeCohomologyBaseChange_of_isLocallyNoetherian (Limits.pullback.snd f U.ι) _ r hc

end AlgebraicGeometry.Scheme.Cohomology

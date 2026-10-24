/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Representability
public import Aglib.AlgebraicGeometry.Modules.Invertible.RankOne

/-!
# `P(E)` classifies invertible quotients

A module sheaf is finite locally free of rank one (`SheafHasRank M 1`) exactly when it is an
actual line bundle in Aglib's sense (`Invertible.IsLocallyRankOne`, a local basis with singleton
index sets; `Scheme.Modules.Invertible.isLocallyRankOne_iff_sheafHasRank_one`, in
`Modules/Invertible/RankOne`). Hence morphisms `T ⟶ P(E)` over `S` correspond to epimorphisms
`E_T ⟶ L` onto line bundles, up to isomorphism under `E_T`, by
pulling back the universal quotient `E_{P(E)} ↠ O_{P(E)}(1)`
(`projectiveBundle_existsUnique_lineBundle`), and `O_{P(E)}(1)` is a line bundle
(`isLocallyRankOne_projectiveBundleTwistingSheaf`).

Sources: Stacks, Section 27.21 (Tag 01OA), the description of morphisms `T ⟶ P(E)` by
surjections `f^* E → L` onto invertible `L` after Definition 27.21.1 (Tag 01OB), for any `S`;
Nitsure, arXiv:math/0504590v1, §1, Exercises (1), p. 5 (`S` noetherian there). Premise:
`BaseChangeMkQFormula`, supplied by `Aglib.RingTheory.Grassmannian.BaseChangeFormula`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules LocallyFreeQuotientOf

variable {S : Scheme.{u}} (E : S.Modules) (n : ℕ)
variable [∀ R : CommRingCat.{u}, Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- `O_{P(E)}(1)` is a line bundle. -/
theorem isLocallyRankOne_projectiveBundleTwistingSheaf (h : SheafHasRank E n) :
    Invertible.IsLocallyRankOne (projectiveBundle E n h).left
      (projectiveBundleTwistingSheaf E n h) :=
  (Invertible.isLocallyRankOne_iff_sheafHasRank_one _).mpr
    (sheafHasRank_projectiveBundleTwistingSheaf E n h)

/-- **`P(E)` classifies invertible quotients of `E`.** For every scheme `T` over `S` and every
epimorphism `π : E_T ⟶ L` onto a line bundle `L`, there is exactly one morphism `g : T ⟶ P(E)`
over `S` with an isomorphism `g^* O_{P(E)}(1) ≅ L` carrying the pulled back universal quotient to
`π`.

Sources: Stacks, Section 27.21 (Tag 01OA), after Definition 27.21.1 (Tag 01OB); Nitsure,
arXiv:math/0504590v1, §1, Exercises (1), p. 5 (`S` noetherian there). Premise:
`BaseChangeMkQFormula`. -/
theorem projectiveBundle_existsUnique_lineBundle (h : SheafHasRank E n) {T : Over S}
    {L : T.left.Modules} (π : overPullback E T ⟶ L) [Epi π]
    (hL : Invertible.IsLocallyRankOne T.left L) :
    ∃! g : T ⟶ projectiveBundle E n h,
      ∃ e : ((projectiveBundleUniversalQuotient E n h).pullbackOver g).obj ≅ L,
        ((projectiveBundleUniversalQuotient E n h).pullbackOver g).π ≫ e.hom = π := by
  obtain ⟨g, ⟨e⟩, hg⟩ := projectiveBundle_existsUnique E n h
    ⟨L, π, inferInstance, (Invertible.isLocallyRankOne_iff_sheafHasRank_one L).mp hL⟩
  exact ⟨g, ⟨e.iso, e.comm⟩, fun g' ⟨e', he'⟩ ↦ hg g' ⟨⟨e', he'⟩⟩⟩

end AlgebraicGeometry.Grassmannian

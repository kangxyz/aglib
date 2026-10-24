/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Sheaf
public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Trivialization
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.BaseCover

/-!
# The Grassmannian `Gr(E, k)` of a finite locally free sheaf and `P(E) = Gr(E, 1)`

Let `E` be finite locally free of constant rank `n` on a scheme `S`. The functor
`quotBundleFunctor E k` of rank-`k` locally free quotients of `E_T` is a Zariski sheaf on
`Over S` (`isSheaf_quotBundleFunctor`), and its restrictions to the trivializing affine charts
`TrivializingChart.chartAt h x : Spec R_x ⟶ S`, which cover `S` (`exists_trivializingChart`), are
represented by F8's Grassmannians `schemeOver R_x k n` (`TrivializingChart.representableBy`).
Representability is local on the base
(`Scheme.LocalRepresentability.overZariskiLocalRepresentability`), so:

- `quotBundleFunctor_isRepresentable`: `Quot_k(E)` is representable;
- `grassmannianBundle E k n h : Over S`, the Grassmannian `Gr(E, k)`, with
  `grassmannianBundleRepresentableBy`, the universal quotient `universalBundleQuotient` and a
  representative `universalBundleQuotientRep`, and the classification
  `existsUnique_isoUnder_pullbackOver_universal`;
- `projectiveBundle E n h := grassmannianBundle E 1 n h`, `P(E)`, whose universal quotient
  `projectiveBundleUniversalQuotient : E_{P(E)} ↠ O_{P(E)}(1)` has the rank-one target
  `projectiveBundleTwistingSheaf`, `O_{P(E)}(1)`; maps `T ⟶ P(E)` over `S` correspond to rank-one
  locally free quotients of `E_T` (`projectiveBundle_existsUnique`).

Premise: as in F8, the instance `BaseChangeMkQFormula R (Fin n → R)` for every ring `R`, supplied
by `Aglib.RingTheory.Grassmannian.BaseChangeFormula`.

Sources: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1,
Elementary Examples, Exercises (2), pp. 5–6 (the relative Grassmannian `Grass(E, d)` of a locally
free `E`, rank-`d` quotients, representable, universal quotient `π^* E → F`) and Exercises (1),
p. 5 (`P(E)` represents `Quot^1_{E/S/S}` with universal quotient `π^* E → O_{P(E)}(1)`; `S`
noetherian there); for `E = O^n`, Stacks' `G(n − k, n)`: Tag 089S (eq. (27.22.0.1)), Tag 089T
(Lemma 27.22.1) and Tag 089U (Definition 27.22.2), TeX snapshot `a04446e5`; Stacks, Section 27.21
(Tag 01OA), Definition 27.21.1 (Tag 01OB) and the description of morphisms to `P(E)` after it
(rank-one quotients are invertible quotients, any `S`); Stacks, Tag 01JJ (Schemes,
Lemma 26.15.4: representability is Zariski local). Kleiman, arXiv:math/0504020v1, Thm 3.13,
p. 25 uses `P(Q)` with the same quotient convention. Convention: `k` is the rank of the quotient.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules LocallyFreeQuotientOf

variable {S : Scheme.{u}} (E : S.Modules) (k n : ℕ)
variable [∀ R : CommRingCat.{u}, Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-! ### The Grassmannian `Gr(E, k)` -/

/-- **`Quot_k(E)` is representable**, for `E` finite locally free of constant rank `n`: its
restrictions to the trivializing affine charts at the points of `S` are represented by F8's
Grassmannians, and representability is local on the base.

Sources: Nitsure, arXiv:math/0504590v1, §1, Exercises (2), pp. 5–6; Stacks, Tag 089T and
Tag 01JJ (Schemes, Lemma 26.15.4). Encoded subset: `E` with `SheafHasRank E n` on an arbitrary
scheme `S`, all `k`; convention: `k` is the rank of the quotient. Premise: `BaseChangeMkQFormula`,
supplied by `Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
theorem quotBundleFunctor_isRepresentable (h : SheafHasRank E n) :
    (quotBundleFunctor E k).IsRepresentable :=
  Scheme.LocalRepresentability.overZariskiLocalRepresentability S (quotBundleFunctor E k)
    (isSheaf_quotBundleFunctor E k) S (fun x ↦ Spec (TrivializingChart.chartAt h x).R)
    (fun x ↦ (TrivializingChart.chartAt h x).j) (fun _ ↦ inferInstance)
    (fun x ↦ ⟨x, TrivializingChart.mem_range_chartAt h x⟩)
    (fun x ↦ ((TrivializingChart.chartAt h x).representableBy k).isRepresentable)

/-- **The Grassmannian `Gr(E, k)`** of rank-`k` locally free quotients of `E` over `S`, the object
representing `Quot_k(E)`. -/
def grassmannianBundle (h : SheafHasRank E n) : Over S :=
  haveI := quotBundleFunctor_isRepresentable E k n h
  (quotBundleFunctor E k).reprX

/-- **`Gr(E, k)` represents `Quot_k(E)`** on all schemes over `S`.

Sources: Nitsure, arXiv:math/0504590v1, §1, Exercises (2), pp. 5–6; Stacks, Tag 089T. Premise:
`BaseChangeMkQFormula`. -/
def grassmannianBundleRepresentableBy (h : SheafHasRank E n) :
    (quotBundleFunctor E k).RepresentableBy (grassmannianBundle E k n h) :=
  haveI := quotBundleFunctor_isRepresentable E k n h
  (quotBundleFunctor E k).representableBy

/-- The universal rank-`k` locally free quotient of `E` on `Gr(E, k)`: the class corresponding to
the identity. -/
def universalBundleQuotient (h : SheafHasRank E n) :
    (quotBundleFunctor E k).obj (op (grassmannianBundle E k n h)) :=
  (grassmannianBundleRepresentableBy E k n h).homEquiv (𝟙 _)

/-- A representative of the universal quotient: an epimorphism `E_{Gr(E,k)} ⟶ Q_univ` with
`Q_univ` finite locally free of constant rank `k`. -/
def universalBundleQuotientRep (h : SheafHasRank E n) :
    LocallyFreeQuotientOf (overPullback E (grassmannianBundle E k n h)) k :=
  Quotient.out (s := LocallyFreeQuotientOf.setoid _ k) (universalBundleQuotient E k n h)

theorem mk_universalBundleQuotientRep (h : SheafHasRank E n) :
    (Quotient.mk _ (universalBundleQuotientRep E k n h) :
        (quotBundleFunctor E k).obj (op (grassmannianBundle E k n h))) =
      universalBundleQuotient E k n h :=
  Quotient.out_eq (s := LocallyFreeQuotientOf.setoid _ k) _

/-- Every class of quotients on `T` is the pullback of the universal quotient along the
corresponding morphism `T ⟶ Gr(E, k)` over `S`. -/
theorem grassmannianBundleRepresentableBy_homEquiv (h : SheafHasRank E n) {T : Over S}
    (g : T ⟶ grassmannianBundle E k n h) :
    (grassmannianBundleRepresentableBy E k n h).homEquiv g =
      (quotBundleFunctor E k).map g.op (universalBundleQuotient E k n h) := by
  rw [universalBundleQuotient, ← (grassmannianBundleRepresentableBy E k n h).homEquiv_comp,
    Category.comp_id]

/-- **`Gr(E, k)` classifies rank-`k` locally free quotients of `E`.** For every scheme `T` over
`S` and every rank-`k` locally free quotient `P` of `E_T` there is exactly one morphism
`g : T ⟶ Gr(E, k)` over `S` along which the universal quotient pulls back to `P` under `E_T`.

Sources: Nitsure, arXiv:math/0504590v1, §1, Exercises (2), pp. 5–6 (universal quotient
`π^* E → F` on `Grass(E, d)`); Stacks, Tag 089T. Premise: `BaseChangeMkQFormula`. -/
theorem existsUnique_isoUnder_pullbackOver_universal (h : SheafHasRank E n) {T : Over S}
    (P : LocallyFreeQuotientOf (overPullback E T) k) :
    ∃! g : T ⟶ grassmannianBundle E k n h,
      Nonempty (IsoUnder ((universalBundleQuotientRep E k n h).pullbackOver g) P) := by
  refine ⟨(grassmannianBundleRepresentableBy E k n h).homEquiv.symm (Quotient.mk _ P), ?_, ?_⟩
  · have hP := (grassmannianBundleRepresentableBy E k n h).homEquiv.apply_symm_apply
      (Quotient.mk _ P)
    rw [grassmannianBundleRepresentableBy_homEquiv, ← mk_universalBundleQuotientRep,
      quotBundleFunctor_map_mk] at hP
    exact Quotient.exact hP
  · rintro g ⟨e⟩
    apply (grassmannianBundleRepresentableBy E k n h).homEquiv.injective
    rw [Equiv.apply_symm_apply, grassmannianBundleRepresentableBy_homEquiv,
      ← mk_universalBundleQuotientRep, quotBundleFunctor_map_mk]
    exact Quotient.sound ⟨e⟩

/-! ### The projective bundle `P(E) = Gr(E, 1)` -/

/-- **The projective bundle `P(E) := Gr(E, 1)`** of a finite locally free `E` of constant rank
`n`: the object over `S` representing rank-one locally free quotients of `E`.

Sources: Stacks, Section 27.21 (Tag 01OA), Definition 27.21.1 (Tag 01OB) and the description of
morphisms to `P(E)` by invertible quotients after it (any `S`); Nitsure, arXiv:math/0504590v1,
§1, Exercises (1), p. 5 (`P(E)` represents `Quot^1_{E/S/S}`; `S` noetherian there). Here `P(E)` is
defined as the Grassmannian of rank-one quotients, not as `Proj_S(Sym E)`; Stacks' convention
(quotients, not lines). -/
def projectiveBundle (h : SheafHasRank E n) : Over S :=
  grassmannianBundle E 1 n h

/-- The universal rank-one quotient `E_{P(E)} ↠ O_{P(E)}(1)` on `P(E)`. -/
def projectiveBundleUniversalQuotient (h : SheafHasRank E n) :
    LocallyFreeQuotientOf (overPullback E (projectiveBundle E n h)) 1 :=
  universalBundleQuotientRep E 1 n h

/-- The twisting sheaf `O_{P(E)}(1)`: the target of the universal rank-one quotient. -/
def projectiveBundleTwistingSheaf (h : SheafHasRank E n) : (projectiveBundle E n h).left.Modules :=
  (projectiveBundleUniversalQuotient E n h).obj

/-- `O_{P(E)}(1)` is finite locally free of rank one. -/
theorem sheafHasRank_projectiveBundleTwistingSheaf (h : SheafHasRank E n) :
    SheafHasRank (projectiveBundleTwistingSheaf E n h) 1 :=
  (projectiveBundleUniversalQuotient E n h).hasRank

/-- **`P(E)` classifies rank-one locally free quotients of `E`.** For every scheme `T` over `S`
and every epimorphism `E_T ⟶ L` with `L` finite locally free of rank one there is exactly one
morphism `g : T ⟶ P(E)` over `S` along which `E_{P(E)} ↠ O_{P(E)}(1)` pulls back to it under
`E_T`.

Sources: Stacks, Section 27.21 (Tag 01OA), after Definition 27.21.1 (Tag 01OB); Nitsure,
arXiv:math/0504590v1, §1, Exercises (1), p. 5 (`S` noetherian there). Premise:
`BaseChangeMkQFormula`. -/
theorem projectiveBundle_existsUnique (h : SheafHasRank E n) {T : Over S}
    (P : LocallyFreeQuotientOf (overPullback E T) 1) :
    ∃! g : T ⟶ projectiveBundle E n h,
      Nonempty (IsoUnder ((projectiveBundleUniversalQuotient E n h).pullbackOver g) P) :=
  existsUnique_isoUnder_pullbackOver_universal E 1 n h P

end AlgebraicGeometry.Grassmannian

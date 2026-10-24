/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.Representability

/-!
# `Quot_k(E)` on a trivializing affine chart

Let `E` be a module sheaf on a scheme `S`. A `TrivializingChart E n` is an open immersion
`j : Spec R ⟶ S` with an isomorphism `φ : j^* E ≅ O^n` (`freeSheaf (Spec R) n`). For a scheme
`T` over `Spec R`, with image `j(T) = (Over.map j).obj T` over `S`, the composite
`E_{j(T)} = (T ⟶ Spec R ⟶ S)^* E ≅ (T ⟶ Spec R)^* j^* E ≅ (T ⟶ Spec R)^* O^n ≅ O_T^n` is
`TrivializingChart.freeIso`; it is compatible with pullback along morphisms over `Spec R`
(`TrivializingChart.freeIso_comp`, from the coherence of `Scheme.Modules.pullbackTriangleIso`).
Precomposition
with it identifies quotients of `E_{j(T)}` with F8's quotients of `O_T^n`
(`TrivializingChart.quotEquiv`), naturally in `T`, so the restriction of `Quot_k(E)` to schemes
over `Spec R` is F8's `quotFunctor R k n`:

- `TrivializingChart.quotIso : (Over.map j).op ⋙ quotBundleFunctor E k ≅ quotFunctor R k n`;
- `TrivializingChart.representableBy`: this restriction is represented by the Grassmannian
  `schemeOver R k n` (premise `BaseChangeMkQFormula` for `R`, as in F8, supplied by
  `Aglib.RingTheory.Grassmannian.BaseChangeFormula`).

The transport along `E|_U ≅ O^n` is the precomposition of quotient maps, as in F8's
`Quotient/Reindex` (`ofFree`). Sources: Nitsure, arXiv:math/0504590v1, §1, Exercises (2),
pp. 5–6 (`Grass(E, d)` for a locally free `E`, locally the Grassmannian of `O^r`); for `O^n`,
Stacks' `G(n − k, n)`: Tag 089S (eq. (27.22.0.1)), Tag 089T (Lemma 27.22.1) and Tag 089U
(Definition 27.22.2, the base change `G(n − k, n)_R`), TeX snapshot `a04446e5`. Convention: `k` is
the rank of the quotient.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules LocallyFreeQuotientOf

variable {S : Scheme.{u}} (E : S.Modules) (n : ℕ)

/-- The trivialization along a morphism `h : T ⟶ U` of a trivialization `φ : j^* E ≅ O_U^n`:
`(h ≫ j)^* E ≅ h^* j^* E ≅ h^* O_U^n ≅ O_T^n`. -/
def chartFreeIsoAux {U T : Scheme.{u}} (j : U ⟶ S)
    (φ : (Scheme.Modules.pullback j).obj E ≅ freeSheaf U n) (h : T ⟶ U) :
    (Scheme.Modules.pullback (h ≫ j)).obj E ≅ freeSheaf T n :=
  ((pullbackTriangleIso h j (h ≫ j) rfl).app E).symm ≪≫ (Scheme.Modules.pullback h).mapIso φ ≪≫
    pullbackFreeIso h (ULift.{u} (Fin n))

/-- The trivializations along `b` and along `c = a ≫ b` are compatible with pullback along `a`. -/
theorem chartFreeIsoAux_comp {U T T' : Scheme.{u}} (j : U ⟶ S)
    (φ : (Scheme.Modules.pullback j).obj E ≅ freeSheaf U n) (a : T' ⟶ T) (b : T ⟶ U)
    (c : T' ⟶ U) (hc : a ≫ b = c) :
    (pullbackTriangleIso a (b ≫ j) (c ≫ j) (by rw [← hc, Category.assoc])).inv.app E ≫
        (Scheme.Modules.pullback a).map (chartFreeIsoAux E n j φ b).hom ≫
          (pullbackFreeIso a (ULift.{u} (Fin n))).hom =
      (chartFreeIsoAux E n j φ c).hom := by
  subst hc
  have hn := (pullbackComp a b).inv.naturality φ.hom
  dsimp only [Functor.comp_map] at hn
  have H := (Iso.inv_eq_inv
    ((Scheme.Modules.pullback a).mapIso ((pullbackTriangleIso b j (b ≫ j) rfl).app E) ≪≫
      (pullbackTriangleIso a (b ≫ j) ((a ≫ b) ≫ j) (Category.assoc a b j).symm).app E)
    ((pullbackComp a b).app ((Scheme.Modules.pullback j).obj E) ≪≫
      (pullbackTriangleIso (a ≫ b) j ((a ≫ b) ≫ j) rfl).app E)).mpr
    (pullbackTriangleIso_assoc_hom b a j (b ≫ j) rfl ((a ≫ b) ≫ j) (Category.assoc a b j).symm E)
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at H
  simp only [chartFreeIsoAux, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% H, ← reassoc_of% hn, ← pullbackFreeIso_comp, Iso.inv_hom_id_app_assoc]

variable {E n}

/-- A trivializing affine chart of `E`: an open immersion `j : Spec R ⟶ S` with an isomorphism
`φ : j^* E ≅ O^n`. -/
structure TrivializingChart (E : S.Modules) (n : ℕ) : Type (u + 1) where
  /-- The coordinate ring of the chart. -/
  R : CommRingCat.{u}
  /-- The open immersion of the chart. -/
  j : Spec R ⟶ S
  isOpenImmersion : IsOpenImmersion j
  /-- The trivialization of `E` on the chart. -/
  φ : (Scheme.Modules.pullback j).obj E ≅ freeSheaf (Spec R) n

attribute [instance] TrivializingChart.isOpenImmersion

namespace TrivializingChart

variable (c : TrivializingChart E n)

/-- The trivialization of `E_{j(T)}` for a scheme `T` over the chart: `E_{j(T)} ≅ O_T^n`. -/
def freeIso (T : Over (Spec c.R)) :
    overPullback E ((Over.map c.j).obj T) ≅ freeSheaf T.left n :=
  chartFreeIsoAux E n c.j c.φ T.hom

/-- The trivializations of `E_{j(T)}` are compatible with pullback along morphisms over the
chart. -/
@[reassoc]
theorem freeIso_comp {T T' : Over (Spec c.R)} (t : T' ⟶ T) :
    (overPullbackIso E ((Over.map c.j).map t)).hom ≫
        (Scheme.Modules.pullback t.left).map (c.freeIso T).hom ≫
          (pullbackFreeIso t.left (ULift.{u} (Fin n))).hom =
      (c.freeIso T').hom :=
  chartFreeIsoAux_comp E n c.j c.φ t.left T.hom T'.hom (Over.w t)

/-- The inverse form of `freeIso_comp`. -/
theorem freeIso_inv_comp {T T' : Over (Spec c.R)} (t : T' ⟶ T) :
    (c.freeIso T').inv ≫ (overPullbackIso E ((Over.map c.j).map t)).hom =
      (pullbackFreeIso t.left (ULift.{u} (Fin n))).inv ≫
        (Scheme.Modules.pullback t.left).map (c.freeIso T).inv := by
  rw [Iso.inv_comp_eq, ← c.freeIso_comp t]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

variable (k : ℕ)

/-- A quotient of `E_{j(T)}`, as F8's quotient of `O_T^n`. -/
def toFreeQuotient {T : Over (Spec c.R)}
    (P : LocallyFreeQuotientOf (overPullback E ((Over.map c.j).obj T)) k) :
    LocallyFreeQuotient T.left k n :=
  (P.precomp (c.freeIso T).inv).toLocallyFreeQuotient

/-- F8's quotient of `O_T^n`, as a quotient of `E_{j(T)}`. -/
def ofFreeQuotient {T : Over (Spec c.R)} (P : LocallyFreeQuotient T.left k n) :
    LocallyFreeQuotientOf (overPullback E ((Over.map c.j).obj T)) k :=
  (LocallyFreeQuotientOf.ofLocallyFreeQuotient P).precomp (c.freeIso T).hom

variable {c k}

/-- `toFreeQuotient` respects isomorphisms of quotients. -/
def isoUnderToFreeQuotient {T : Over (Spec c.R)}
    {P Q : LocallyFreeQuotientOf (overPullback E ((Over.map c.j).obj T)) k} (e : IsoUnder P Q) :
    LocallyFreeQuotient.IsoUnder (c.toFreeQuotient k P) (c.toFreeQuotient k Q) where
  iso := e.iso
  comm := (e.precomp (c.freeIso T).inv).comm

/-- `ofFreeQuotient` respects isomorphisms of quotients. -/
def isoUnderOfFreeQuotient {T : Over (Spec c.R)} {P Q : LocallyFreeQuotient T.left k n}
    (e : LocallyFreeQuotient.IsoUnder P Q) :
    IsoUnder (c.ofFreeQuotient k P) (c.ofFreeQuotient k Q) where
  iso := e.iso
  comm := by
    change ((c.freeIso T).hom ≫ P.π) ≫ e.iso.hom = (c.freeIso T).hom ≫ Q.π
    rw [Category.assoc, e.comm]

variable (c k)

/-- **Quotients of `E_{j(T)}` are quotients of `O_T^n`**, by precomposition with the
trivialization `freeIso`. -/
def quotEquiv (T : Over (Spec c.R)) :
    (quotBundleFunctor E k).obj (op ((Over.map c.j).obj T)) ≃ (quotFunctor c.R k n).obj (op T) where
  toFun := Quotient.map (c.toFreeQuotient k) (fun _ _ ⟨e⟩ ↦ ⟨isoUnderToFreeQuotient e⟩)
  invFun := Quotient.map (c.ofFreeQuotient k) (fun _ _ ⟨e⟩ ↦ ⟨isoUnderOfFreeQuotient e⟩)
  left_inv x := by
    induction x using Quotient.inductionOn with | h P =>
    exact Quotient.sound ⟨precompInvHomIso (c.freeIso T) P⟩
  right_inv x := by
    induction x using Quotient.inductionOn with | h P =>
    refine Quotient.sound ⟨?_⟩
    let e := precompHomInvIso (c.freeIso T) (LocallyFreeQuotientOf.ofLocallyFreeQuotient P)
    exact ⟨e.iso, e.comm⟩

theorem quotEquiv_mk (T : Over (Spec c.R))
    (P : LocallyFreeQuotientOf (overPullback E ((Over.map c.j).obj T)) k) :
    c.quotEquiv k T (Quotient.mk _ P) = Quotient.mk _ (c.toFreeQuotient k P) := rfl

/-- **Naturality of `quotEquiv`** in the scheme over the chart. -/
theorem quotEquiv_naturality {T T' : Over (Spec c.R)} (t : T' ⟶ T)
    (x : (quotBundleFunctor E k).obj (op ((Over.map c.j).obj T))) :
    c.quotEquiv k T' ((quotBundleFunctor E k).map ((Over.map c.j).map t).op x) =
      (quotFunctor c.R k n).map t.op (c.quotEquiv k T x) := by
  induction x using Quotient.inductionOn with | h P =>
  refine Quotient.sound ⟨⟨CategoryTheory.Iso.refl _, ?_⟩⟩
  change ((c.freeIso T').inv ≫ (overPullbackIso E ((Over.map c.j).map t)).hom ≫
      (Scheme.Modules.pullback t.left).map P.π) ≫ 𝟙 _ =
    (pullbackFreeIso t.left (ULift.{u} (Fin n))).inv ≫
      (Scheme.Modules.pullback t.left).map ((c.freeIso T).inv ≫ P.π)
  rw [Category.comp_id, CategoryTheory.Functor.map_comp, ← Category.assoc, c.freeIso_inv_comp t,
    Category.assoc]

/-- **The restriction of `Quot_k(E)` to a trivializing chart is `Quot_k(O^n)`**:
`(Over.map j).op ⋙ quotBundleFunctor E k ≅ quotFunctor R k n`. -/
def quotIso : (Over.map c.j).op ⋙ quotBundleFunctor E k ≅ quotFunctor c.R k n :=
  NatIso.ofComponents (fun T ↦ (c.quotEquiv k T.unop).toIso) fun {T T'} t ↦ by
    ext x
    exact c.quotEquiv_naturality k t.unop x

/-- **Local representability**: on a trivializing chart `j : Spec R ⟶ S`, the restriction of
`Quot_k(E)` to schemes over `Spec R` is represented by the Grassmannian `schemeOver R k n`.

Sources: Stacks, Tag 089T (Lemma 27.22.1) and Tag 089U (Definition 27.22.2, base change to `R`)
for Stacks' `G(n − k, n)`, TeX snapshot `a04446e5`; Nitsure, arXiv:math/0504590v1, §1,
Exercises (2), pp. 5–6. Encoded
subset: an open immersion `j : Spec R ⟶ S` with `j^* E ≅ O^n`, all `k` and `n`; convention: `k`
is the rank of the quotient. Premise: `BaseChangeMkQFormula` for `R`, supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`. -/
def representableBy [Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} c.R (Fin n → c.R)] :
    ((Over.map c.j).op ⋙ quotBundleFunctor E k).RepresentableBy (schemeOver c.R k n) :=
  (quotFunctorRepresentableBy c.R k n).ofIso (c.quotIso k).symm

end TrivializingChart

end AlgebraicGeometry.Grassmannian

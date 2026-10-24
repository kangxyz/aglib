/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Representability

/-!
# `Gr(E, k) ⟶ S` is surjective when `k ≤ rank E`

Let `E` be finite locally free of constant rank `n` on a scheme `S`
(`Scheme.Modules.SheafHasRank E n`) and `k ≤ n`. Then the structure morphism of the Grassmannian
bundle `Gr(E, k)` of rank-`k` locally free quotients of `E` is surjective
(`surjective_grassmannianBundle_hom_of_le`). In terms of fibres: a vector space of dimension `n ≥ k`
has a quotient of dimension `k`.

The proof uses no fibre. Every point of `S` lies in a trivializing affine chart
`j : Spec R ⟶ S` with `j^* E ≅ O^n` (`exists_trivializingChart`). On `Spec R` the coordinate
projection `O^{k + m} ↠ O^k` onto the first `k` coordinates
(`LocallyFreeQuotient.coordinateProjection`, a split epimorphism, through Mathlib's
`SheafOfModules.freeSumIso`) is a rank-`k` locally free quotient of `O^{k + m}`
(`sheafHasRank_freeSheaf`), hence of `j^* E`. The morphism `Spec R ⟶ Gr(E, k)` over `S`
classifying it (`grassmannianBundleRepresentableBy`) lifts `j`, so the image of `j` lies in the
image of `Gr(E, k) ⟶ S`.

Source: plain mathematics, from the representability of `Quot_k(E)` by `Gr(E, k)` (Nitsure,
arXiv:math/0504590v1, §1, Exercises (2), pp. 5–6). Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30, needs this surjectivity for `P(Q)` over `T′`
(there implicit in the étale covering `T₁ → T′` with a `T′`-map `T₁ → P(Q)`, EGA IV₄ 17.16.3
(ii)). Premise: `BaseChangeMkQFormula` for `Fin n`, as for `Gr(E, k)` itself; it is supplied by
`Aglib.RingTheory.Grassmannian.BaseChangeFormula`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Grassmannian

open Scheme.Modules

/-- The free sheaf `O_X^k` has constant rank `k`: its own basis is a global basis. -/
theorem sheafHasRank_freeSheaf (X : Scheme.{u}) (k : ℕ) : SheafHasRank (freeSheaf X k) k :=
  ⟨(SheafOfModules.free.generatingSections (R := X.ringCatSheaf)
      (ULift.{u} (Fin k))).localGeneratorsData, inferInstance, fun _ => ⟨Equiv.ulift⟩⟩

/-- The basis `ULift (Fin k) ⊕ ULift (Fin m)` of `O^{k + m}`: the first `k` and the last `m`
coordinates. -/
def coordinateSumEquiv (k m : ℕ) :
    ULift.{u} (Fin k) ⊕ ULift.{u} (Fin m) ≃ ULift.{u} (Fin (k + m)) :=
  (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans (finSumFinEquiv.trans Equiv.ulift.symm)

/-- The projection `O^k ⨿ O^m ⟶ O^k` onto the first summand, on the free sheaf with basis
`ULift (Fin k) ⊕ ULift (Fin m)`: Mathlib's `SheafOfModules.freeSumIso` followed by
`coprod.desc (𝟙 _) 0`. -/
def coordinateProjectionMap (X : Scheme.{u}) (k m : ℕ) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin k) ⊕ ULift.{u} (Fin m)) ⟶
      freeSheaf X k :=
  (SheafOfModules.freeSumIso (R := X.ringCatSheaf) (ULift.{u} (Fin k)) (ULift.{u} (Fin m))).inv ≫
    coprod.desc (𝟙 _) 0

/-- The projection onto the first summand is an epimorphism, split by the first inclusion. -/
instance epi_coordinateProjectionMap (X : Scheme.{u}) (k m : ℕ) :
    Epi (coordinateProjectionMap X k m) :=
  haveI : IsSplitEpi (coordinateProjectionMap X k m) := IsSplitEpi.mk'
    ⟨coprod.inl ≫ (SheafOfModules.freeSumIso (R := X.ringCatSheaf) _ _).hom, by
      rw [coordinateProjectionMap, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]⟩
  inferInstance

namespace LocallyFreeQuotient

/-- **The coordinate projection `O_X^{k + m} ↠ O_X^k`** onto the first `k` coordinates, as a
rank-`k` locally free quotient of `O_X^{k + m}`: under `O^{k + m} ≅ O^k ⨿ O^m` (Mathlib's
`SheafOfModules.freeSumIso` and `coordinateSumEquiv`), the map `coprod.desc (𝟙 _) 0`
(`coordinateProjectionMap`), an epimorphism split by `coprod.inl`. -/
def coordinateProjection (X : Scheme.{u}) (k m : ℕ) : LocallyFreeQuotient X k (k + m) :=
  ofFree (coordinateSumEquiv k m) (coordinateProjectionMap X k m) (sheafHasRank_freeSheaf X k)

theorem coordinateProjection_obj (X : Scheme.{u}) (k m : ℕ) :
    (coordinateProjection X k m).obj = freeSheaf X k :=
  rfl

end LocallyFreeQuotient

variable {S : Scheme.{u}} (E : S.Modules) (k : ℕ) {n : ℕ}
variable [∀ R : CommRingCat.{u}, Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R)]

/-- **Trivializing charts lift to `Gr(E, k)`**: for `E` of constant rank `n ≥ k` and a
trivializing chart `j : Spec R ⟶ S`, `j^* E ≅ O^n`, some morphism `Spec R ⟶ Gr(E, k)` over `S`
lifts `j`; it classifies the coordinate projection `j^* E ≅ O^n ↠ O^k`. -/
theorem exists_comp_grassmannianBundle_hom_eq_trivializingChart (h : SheafHasRank E n)
    (hk : k ≤ n) (c : TrivializingChart E n) :
    ∃ g : Spec c.R ⟶ (grassmannianBundle E k n h).left,
      g ≫ (grassmannianBundle E k n h).hom = c.j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  let P : LocallyFreeQuotientOf (overPullback E (Over.mk c.j)) k :=
    (LocallyFreeQuotientOf.ofLocallyFreeQuotient
      (LocallyFreeQuotient.coordinateProjection (Spec c.R) k m)).precomp c.φ.hom
  let g := (grassmannianBundleRepresentableBy E k (k + m) h).homEquiv.symm (Quotient.mk _ P)
  exact ⟨g.left, Over.w g⟩

/-- **`Gr(E, k) ⟶ S` is surjective** for `E` finite locally free of constant rank `n ≥ k`: every
trivializing chart lifts to `Gr(E, k)` (`exists_comp_grassmannianBundle_hom_eq_trivializingChart`),
and these charts cover `S` (`exists_trivializingChart`). -/
theorem surjective_grassmannianBundle_hom_of_le (h : SheafHasRank E n) (hk : k ≤ n) :
    Surjective (grassmannianBundle E k n h).hom := by
  refine ⟨fun x => ?_⟩
  obtain ⟨c, y, rfl⟩ := exists_trivializingChart h x
  obtain ⟨g, hg⟩ := exists_comp_grassmannianBundle_hom_eq_trivializingChart E k h hk c
  exact ⟨g y, by rw [← Scheme.Hom.comp_apply, hg]⟩

end AlgebraicGeometry.Grassmannian

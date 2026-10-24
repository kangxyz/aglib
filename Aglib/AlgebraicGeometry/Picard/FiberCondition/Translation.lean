/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FiberCondition.OpenSubfunctor

/-!
# Translation of fiber-condition subsheaves by a compatible family of classes

Let `p : X ⟶ S` be a morphism of schemes and `c` a family of classes `c T ∈ Pic(X ×_S T)`, one
for every `S`-scheme `T`, compatible with pullback: `g^* (c T) = c T'` for every `g : T' ⟶ T`
over `S`. Write `γ_T` for the image of `c T` in `Pic_{X/S,(fppf)}(T)` (`translationSection`).

* Translation `ξ ↦ ξ + γ_T` is a natural bijection of `Pic_{X/S,(fppf)}`, with inverse
  `ξ ↦ ξ - γ_T` (`translationNatIso`).
* If two fiber conditions `C` and `D` satisfy `D(a + c T) ↔ C(a)` at every point of every
  `S`-scheme `T`, then `ξ` satisfies `C` at `t` exactly when `ξ + γ_T` satisfies `D` at `t`
  (`FiberCondition.holdsAt_add_translationSection_iff`), so translation carries `Pic^C` onto
  `Pic^D` (`FiberCondition.mem_subfunctor_iff_translation`), giving isomorphisms
  `Pic^C ≅ Pic^D` on all `S`-schemes (`FiberCondition.subfunctorTranslationIso`) and on locally
  Noetherian ones (`FiberCondition.locallyNoetherianSubfunctorTranslationIso`). A representation of
  `Pic^D` on locally Noetherian test schemes is thus one of `Pic^C`
  (`FiberCondition.representableByOfTranslation`, through Mathlib's `RepresentableBy.ofIso`).

The pointwise test runs on a flat representative through each point (`exists_flat_app_eq`): if
`a` represents `ξ` near `t`, then `a + c V` represents `ξ + γ_T` there. This is the shape of
Kleiman's twist `Pic^φ_m ≅ Pic^{φ₀}_0`, `L ↦ L(m)` (*The Picard scheme*, arXiv:math/0504020v1,
proof of Thm 4.8, pp. 29–30), with `c T` the class of `O_{X_T}(m)`; no hypothesis on `p` or `S` is
used here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {S X : Scheme.{u}} {p : X ⟶ S}
  (c : ∀ T : Over S, (familyPicardFunctor p).obj (op T))
  (hc : ∀ ⦃T T' : Over S⦄ (g : T' ⟶ T), (familyPicardFunctor p).map g.op (c T) = c T')

/-- The image `γ_T` of the class `c T` in `Pic_{X/S,(fppf)}(T)`. -/
def translationSection (T : Over S) : (fppfPicardSheaf p).obj.obj (op T) :=
  (quotientProjection p ≫ toFppfPicardSheaf p).app (op T) (c T)

include hc in
/-- The sections `γ_T` are compatible with pullback. -/
theorem map_translationSection {T T' : Over S} (g : T' ⟶ T) :
    (fppfPicardSheaf p).obj.map g.op (translationSection c T) = translationSection c T' := by
  rw [translationSection, ← NatTrans.naturality_apply]
  exact congrArg _ (hc g)

include hc in
/-- Translation commutes with pullback: `g^* (ξ + γ_T) = g^* ξ + γ_{T'}`. -/
theorem map_add_translationSection {T T' : Over S} (g : T' ⟶ T)
    (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    (fppfPicardSheaf p).obj.map g.op (ξ + translationSection c T) =
      (fppfPicardSheaf p).obj.map g.op ξ + translationSection c T' := by
  rw [map_add, map_translationSection c hc g]

/-- **Translation by `γ`**: the natural bijection `ξ ↦ ξ + γ_T` of `Pic_{X/S,(fppf)}`, with
inverse `ξ ↦ ξ - γ_T`. -/
def translationNatIso :
    (fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      (fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents (fun T => (Equiv.subRight (translationSection c T.unop)).symm.toIso)
    (fun {_ _} g => by
      ext ξ
      exact (map_add_translationSection c hc g.unop ξ).symm)

theorem translationNatIso_hom_app {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    (translationNatIso c hc).hom.app (op T) ξ = ξ + translationSection c T :=
  rfl

theorem translationNatIso_inv_app {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    (translationNatIso c hc).inv.app (op T) ξ = ξ - translationSection c T :=
  rfl

namespace FiberCondition

variable {c} {C D : FiberCondition p}
  (hCD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
    D.Holds T (a + c T) t ↔ C.Holds T a t)

include hc hCD in
/-- **Pointwise transport**: `ξ + γ_T` satisfies `D` at `t` exactly when `ξ` satisfies `C` at `t`.
-/
theorem holdsAt_add_translationSection_iff {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T))
    (t : T.left) : D.HoldsAt (ξ + translationSection c T) t ↔ C.HoldsAt ξ t := by
  obtain ⟨V, h, a, -, -, ⟨v, rfl⟩, ha⟩ := exists_flat_app_eq ξ t
  have hb : (quotientProjection p ≫ toFppfPicardSheaf p).app _ (a + c (Over.mk (h ≫ T.hom))) =
      (fppfPicardSheaf p).obj.map (Over.homMk h : Over.mk (h ≫ T.hom) ⟶ T).op
        (ξ + translationSection c T) := by
    rw [map_add, map_add, ha, map_translationSection c hc]
    rfl
  exact ((D.holdsAt_iff _ _ _ hb v).trans (hCD _ a v)).trans (C.holdsAt_iff ξ _ a ha v).symm

include hc hCD in
/-- **Translation carries `Pic^C` onto `Pic^D`**, on every `S`-scheme `T`. -/
theorem mem_subfunctor_iff_translation {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    ξ ∈ C.subfunctor.obj (op T) ↔
      (translationNatIso c hc).hom.app (op T) ξ ∈ D.subfunctor.obj (op T) := by
  rw [C.mem_subfunctor_iff, translationNatIso_hom_app, D.mem_subfunctor_iff]
  exact forall_congr' fun t => (holdsAt_add_translationSection_iff hc hCD ξ t).symm

/-- **The isomorphism `Pic^C ≅ Pic^D`** induced by translation, on all `S`-schemes. -/
def subfunctorTranslationIso : C.subfunctor.toFunctor ≅ D.subfunctor.toFunctor where
  hom := Subfunctor.lift (C.subfunctor.ι ≫ (translationNatIso c hc).hom) (by
    rintro T _ ⟨ξ, rfl⟩
    exact (mem_subfunctor_iff_translation hc hCD ξ.1).mp ξ.2)
  inv := Subfunctor.lift (D.subfunctor.ι ≫ (translationNatIso c hc).inv) (by
    rintro T _ ⟨ξ, rfl⟩
    refine (mem_subfunctor_iff_translation hc hCD _).mpr ?_
    change (_ - translationSection c T.unop) + translationSection c T.unop ∈ _
    rw [sub_add_cancel]
    exact ξ.2)
  hom_inv_id := by
    ext T ξ
    exact Subtype.ext (add_sub_cancel_right (show (fppfPicardSheaf p).obj.obj T from ξ.1) _)
  inv_hom_id := by
    ext T ξ
    exact Subtype.ext (sub_add_cancel (show (fppfPicardSheaf p).obj.obj T from ξ.1) _)

theorem subfunctorTranslationIso_hom_app_val {T : Over S}
    (ξ : C.subfunctor.toFunctor.obj (op T)) :
    ((subfunctorTranslationIso hc hCD).hom.app (op T) ξ).1 =
      (show (fppfPicardSheaf p).obj.obj (op T) from ξ.1) + translationSection c T :=
  rfl

theorem subfunctorTranslationIso_inv_app_val {T : Over S}
    (ξ : D.subfunctor.toFunctor.obj (op T)) :
    ((subfunctorTranslationIso hc hCD).inv.app (op T) ξ).1 =
      (show (fppfPicardSheaf p).obj.obj (op T) from ξ.1) - translationSection c T :=
  rfl

/-- **The isomorphism `Pic^C ≅ Pic^D`** induced by translation, on locally Noetherian test
schemes. -/
def locallyNoetherianSubfunctorTranslationIso :
    C.locallyNoetherianSubfunctor.toFunctor ≅ D.locallyNoetherianSubfunctor.toFunctor :=
  Functor.isoWhiskerLeft (Scheme.locallyNoetherianOverInclusion S).op
    (subfunctorTranslationIso hc hCD)

/-- **Transport of a representation along translation**: if `Pic^D` is represented by `Q` on
locally Noetherian test schemes, so is `Pic^C`, through `ξ ↦ ξ - γ_T` (Mathlib's
`RepresentableBy.ofIso`). -/
def representableByOfTranslation {Q : Scheme.LocallyNoetherianOver S}
    (R : D.locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q) :
    C.locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q :=
  R.ofIso (locallyNoetherianSubfunctorTranslationIso hc hCD).symm

theorem representableByOfTranslation_homEquiv_val {Q : Scheme.LocallyNoetherianOver S}
    (R : D.locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q)
    {Z : Scheme.LocallyNoetherianOver S} (g : Z ⟶ Q) :
    ((representableByOfTranslation hc hCD R).homEquiv g).1 =
      (show (fppfPicardSheaf p).obj.obj (op Z.obj) from (R.homEquiv g).1) -
        translationSection c Z.obj :=
  rfl

end FiberCondition

end AlgebraicGeometry.Scheme.RelativePicard

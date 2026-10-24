/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Conditions
public import Aglib.AlgebraicGeometry.Picard.FiberCondition.Translation

/-!
# The twist isomorphism of the Picard strata

Let `i : X ⟶ P^N_A = ProjectiveSpace A ι` be a closed immersion with `ι ≃ Fin (N + 1)` such that
`p = i ≫ toSpec A ι` is flat, and write `o_T(m) = twistClass i m T` for the class of `O_{X_T}(m)`
in `Pic(X_T)`, with image `twistSection i m T` in `Pic_{X/S,(fppf)}(T)`. Kleiman's twist
`L ↦ L(m)` (*The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, pp. 29–30) is the
translation `τ_m : ξ ↦ ξ + o_T(m)` of `Pic_{X/S,(fppf)}`, a natural bijection with inverse
`ξ ↦ ξ - o_T(m)` (`twistNatIso`). For `φ₀ = φ.comp (X - C m)`, that is `φ₀(n) = φ(n - m)`:

* `τ_m` carries the fine stratum `Pic^{φ,ψ,r}_m` onto `Pic^{φ₀,ψ,r}_0`, on every `S`-scheme `T`
  (`mem_fine_iff_twist`), and likewise `Pic^φ_m` onto `Pic^{φ₀}_0` (`mem_coarse_iff_twist`) and
  the subsheaf of `C_m` onto that of `C_0` (`mem_coarseLevel_iff_twist`);
* hence the isomorphisms `Pic^{φ,ψ,r}_m ≅ Pic^{φ₀,ψ,r}_0` (`fineTwistIso`, and on locally
  Noetherian test schemes `fineLocallyNoetherianTwistIso`) and `Pic^φ_m ≅ Pic^{φ₀}_0`
  (`coarseTwistIso`);
* a representation of `Pic^{φ₀,ψ,r}_0` on locally Noetherian test schemes by `Q` is one of
  `Pic^{φ,ψ,r}_m` by the same `Q`, through `τ_m` (`fineRepresentableByOfTwist`).

The fibre identities behind this are those of the fibre conditions:
`h^q(X_t, L(m)_t(n)) = h^q(X_t, L_t(n + m))` (`fiberTwistDim_pulledTwistLineBundle`) and
`χ(X_t, L(m)_t^{-1}(n)) = χ(X_t, L_t^{-1}(n - m))`
(`fiberDualTwistEulerChar_pulledTwistLineBundle`), with `[L(m)] = [L] + m • o_T(1)`
(`classOf_pulledTwistLineBundle`) and `o_T(m) = m • o_T(1)` (`twistClass_eq_zsmul`). Kleiman
prints the twisted polynomial as `φ(m + n)` (p. 29); the identity for the dual gives `φ(n - m)`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard.Strata

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι)

/-! ### The twist of `Pic_{X/S,(fppf)}` -/

/-- The image `o_T(m)` of the twisting class in `Pic_{X/S,(fppf)}(T)`. -/
abbrev twistSection (m : ℤ) (T : Over (Spec (.of A))) :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T) :=
  translationSection (twistClass i m) T

/-- The sections `o_T(m)` are compatible with pullback. -/
theorem map_twistSection (m : ℤ) {T T' : Over (Spec (.of A))} (g : T' ⟶ T) :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map g.op (twistSection i m T) = twistSection i m T' :=
  map_translationSection (twistClass i m)
    (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m) g

/-- `o_T(m) = m • o_T(1)` in `Pic_{X/S,(fppf)}(T)`. -/
theorem twistSection_eq_zsmul (m : ℤ) (T : Over (Spec (.of A))) :
    twistSection i m T = m • twistSection i 1 T := by
  change (quotientProjection _ ≫ toFppfPicardSheaf _).app (op T) (twistClass i m T) =
    m • (quotientProjection _ ≫ toFppfPicardSheaf _).app (op T) (twistClass i 1 T)
  rw [twistClass_eq_zsmul i m T, map_zsmul]

/-- **The twist `τ_m`** (Kleiman's `L ↦ L(m)`, arXiv:math/0504020v1, pp. 29–30): the natural
bijection `ξ ↦ ξ + o_T(m)` of `Pic_{X/S,(fppf)}`, with inverse `ξ ↦ ξ - o_T(m)`. -/
def twistNatIso (m : ℤ) :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  translationNatIso (twistClass i m) (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m)

theorem twistNatIso_hom_app (m : ℤ) {T : Over (Spec (.of A))}
    (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T)) :
    (twistNatIso i m).hom.app (op T) ξ = ξ + twistSection i m T :=
  rfl

theorem twistNatIso_inv_app (m : ℤ) {T : Over (Spec (.of A))}
    (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T)) :
    (twistNatIso i m).inv.app (op T) ξ = ξ - twistSection i m T :=
  rfl

/-! ### The twist on the conditions -/

section Strata

variable [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1))

variable {i N e}

/-- **Translation by `m • o_T(1)` shifts `C_{m'}`**: `C_{m'}` at `a + m • o_T(1)` is `C_{m'+m}` at
`a`. -/
theorem coarseLevelCondition_holds_add_twistClass (m' m : ℤ) (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (coarseLevelCondition i N e m').Holds T (a + m • twistClass i 1 T) t ↔
      (coarseLevelCondition i N e (m' + m)).Holds T a t := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep (a : PicardGroup _)
  rw [add_zsmul_twistClass_eq_classOf hL, ← hL]
  exact hasFiberTwistVanishingAndSections_pulledTwistLineBundle_iff i T.hom L t m' m

/-- **Translation by `m • o_T(1)` carries the coarse stratum at `(φ, m)` to the one at
`(φ₀, 0)`**, `φ₀(n) = φ(n - m)`. -/
theorem coarseCondition_holds_add_twistClass (φ : Polynomial ℚ) (m : ℤ) (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (coarseCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) 0).Holds T
        (a + m • twistClass i 1 T) t ↔ (coarseCondition i N e φ m).Holds T a t := by
  obtain ⟨L, hL⟩ := Quotient.exists_rep (a : PicardGroup _)
  rw [add_zsmul_twistClass_eq_classOf hL, ← hL]
  exact isFiberStratum_pulledTwistLineBundle_iff i T.hom L t φ m

/-- Translation by `o_T(m)` carries the fine condition at `(φ, ψ, m, r)` to the one at
`(φ₀, ψ, 0, r)`. -/
theorem fineCondition_zero_holds_add_twistClass_iff (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ)
    (T : Over (Spec (.of A))) (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T))
    (t : T.left) :
    (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0 r).Holds T
        (a + twistClass i m T) t ↔ (fineCondition i N e φ ψ m r).Holds T a t := by
  rw [twistClass_eq_zsmul]
  exact fineCondition_holds_add_twistClass φ ψ m r T a t

/-- Translation by `o_T(m)` carries the coarse condition at `(φ, m)` to the one at `(φ₀, 0)`. -/
theorem coarseCondition_zero_holds_add_twistClass_iff (φ : Polynomial ℚ) (m : ℤ)
    (T : Over (Spec (.of A))) (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T))
    (t : T.left) :
    (coarseCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) 0).Holds T
        (a + twistClass i m T) t ↔ (coarseCondition i N e φ m).Holds T a t := by
  rw [twistClass_eq_zsmul]
  exact coarseCondition_holds_add_twistClass φ m T a t

/-- Translation by `o_T(m)` carries `C_m` to `C_0`. -/
theorem coarseLevelCondition_zero_holds_add_twistClass_iff (m : ℤ) (T : Over (Spec (.of A)))
    (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left) :
    (coarseLevelCondition i N e 0).Holds T (a + twistClass i m T) t ↔
      (coarseLevelCondition i N e m).Holds T a t := by
  rw [twistClass_eq_zsmul, coarseLevelCondition_holds_add_twistClass, zero_add]

/-! ### The twist on the strata -/

/-- **The twist carries `Pic^{φ,ψ,r}_m` onto `Pic^{φ₀,ψ,r}_0`**, `φ₀(n) = φ(n - m)` (Kleiman,
arXiv:math/0504020v1, pp. 29–30, with the correction of the printed `φ(m + n)`), on every
`S`-scheme `T`. -/
theorem mem_fine_iff_twist (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ) {T : Over (Spec (.of A))}
    (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T)) :
    ξ ∈ (fineCondition i N e φ ψ m r).subfunctor.obj (op T) ↔
      (twistNatIso i m).hom.app (op T) ξ ∈
        (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0 r).subfunctor.obj
          (op T) :=
  FiberCondition.mem_subfunctor_iff_translation
    (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m)
    (fineCondition_zero_holds_add_twistClass_iff φ ψ m r) ξ

/-- **The twist carries `Pic^φ_m` onto `Pic^{φ₀}_0`**, on every `S`-scheme `T`. -/
theorem mem_coarse_iff_twist (φ : Polynomial ℚ) (m : ℤ) {T : Over (Spec (.of A))}
    (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T)) :
    ξ ∈ (coarseCondition i N e φ m).subfunctor.obj (op T) ↔
      (twistNatIso i m).hom.app (op T) ξ ∈
        (coarseCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) 0).subfunctor.obj
          (op T) :=
  FiberCondition.mem_subfunctor_iff_translation
    (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m)
    (coarseCondition_zero_holds_add_twistClass_iff φ m) ξ

/-- **The twist carries the locus of `C_m` onto that of `C_0`**, on every `S`-scheme `T`. -/
theorem mem_coarseLevel_iff_twist (m : ℤ) {T : Over (Spec (.of A))}
    (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T)) :
    ξ ∈ (coarseLevelCondition i N e m).subfunctor.obj (op T) ↔
      (twistNatIso i m).hom.app (op T) ξ ∈ (coarseLevelCondition i N e 0).subfunctor.obj (op T) :=
  FiberCondition.mem_subfunctor_iff_translation
    (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m)
    (coarseLevelCondition_zero_holds_add_twistClass_iff m) ξ

/-- **The twist isomorphism `Pic^{φ,ψ,r}_m ≅ Pic^{φ₀,ψ,r}_0`**, `ξ ↦ ξ + o_T(m)`, on all
`S`-schemes. -/
def fineTwistIso (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ) :
    (fineCondition i N e φ ψ m r).subfunctor.toFunctor ≅
      (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0
        r).subfunctor.toFunctor :=
  FiberCondition.subfunctorTranslationIso
    (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m)
    (fineCondition_zero_holds_add_twistClass_iff φ ψ m r)

theorem fineTwistIso_hom_app_val (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ) {T : Over (Spec (.of A))}
    (ξ : (fineCondition i N e φ ψ m r).subfunctor.toFunctor.obj (op T)) :
    ((fineTwistIso φ ψ m r).hom.app (op T) ξ).1 =
      (show (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T) from ξ.1) + twistSection i m T :=
  rfl

/-- **The twist isomorphism `Pic^φ_m ≅ Pic^{φ₀}_0`**, on all `S`-schemes. -/
def coarseTwistIso (φ : Polynomial ℚ) (m : ℤ) :
    (coarseCondition i N e φ m).subfunctor.toFunctor ≅
      (coarseCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ)))
        0).subfunctor.toFunctor :=
  FiberCondition.subfunctorTranslationIso
    (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m)
    (coarseCondition_zero_holds_add_twistClass_iff φ m)

/-- **The twist isomorphism `Pic^{φ,ψ,r}_m ≅ Pic^{φ₀,ψ,r}_0` on locally Noetherian test
schemes.** -/
def fineLocallyNoetherianTwistIso (φ ψ : Polynomial ℚ) (m : ℤ) (r : ℕ) :
    (fineCondition i N e φ ψ m r).locallyNoetherianSubfunctor.toFunctor ≅
      (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0
        r).locallyNoetherianSubfunctor.toFunctor :=
  FiberCondition.locallyNoetherianSubfunctorTranslationIso
    (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m)
    (fineCondition_zero_holds_add_twistClass_iff φ ψ m r)

/-- **Transport of a representation along the twist**, the fine form of Kleiman's reduction
(arXiv:math/0504020v1, p. 30: "Thus it suffices to represent `P^{φ₀}_0` by a quasi-projective
`S`-scheme"): if `Pic^{φ₀,ψ,r}_0` is represented by `Q` on locally Noetherian test schemes, so is
`Pic^{φ,ψ,r}_m`, through `ξ ↦ ξ - o_T(m)` (Mathlib's `RepresentableBy.ofIso`). -/
def fineRepresentableByOfTwist {φ ψ : Polynomial ℚ} {m : ℤ} {r : ℕ}
    {Q : Scheme.LocallyNoetherianOver (Spec (.of A))}
    (R : (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0
      r).locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q) :
    (fineCondition i N e φ ψ m r).locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q :=
  FiberCondition.representableByOfTranslation
    (fun ⦃_ _⦄ g => familyPicardFunctor_map_twistClass i g m)
    (fineCondition_zero_holds_add_twistClass_iff φ ψ m r) R

/-- The section of `Pic^{φ,ψ,r}_m` attached to `g : Z ⟶ Q` is the section of `Pic^{φ₀,ψ,r}_0`
attached to `g`, minus `o_Z(m)`. -/
theorem fineRepresentableByOfTwist_homEquiv_val {φ ψ : Polynomial ℚ} {m : ℤ} {r : ℕ}
    {Q : Scheme.LocallyNoetherianOver (Spec (.of A))}
    (R : (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0
      r).locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q)
    {Z : Scheme.LocallyNoetherianOver (Spec (.of A))} (g : Z ⟶ Q) :
    ((fineRepresentableByOfTwist R).homEquiv g).1 =
      (show (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op Z.obj) from (R.homEquiv g).1) -
        twistSection i m Z.obj :=
  rfl

end Strata

end AlgebraicGeometry.Scheme.RelativePicard.Strata

/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Strata.Twist

/-! Focused consumer of the twist isomorphism of the Picard strata (Kleiman,
arXiv:math/0504020v1, proof of Thm 4.8, pp. 29–30, with `φ₀(n) = φ(n - m)` in place of the
printed `φ(m + n)`): translation of fiber-condition subsheaves by a compatible family of classes
for any `p : X ⟶ S`, the fibre identities, the twist `τ_m` of `Pic_{X/S,(fppf)}`, the
correspondence of the strata, the induced isomorphisms and the transport of representations, with
axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata
open scoped Polynomial

universe u

/-! ### Translation for any `p : X ⟶ S` -/

section Translation

variable {S X : Scheme.{u}} {p : X ⟶ S} (c : ∀ T : Over S, (familyPicardFunctor p).obj (op T))
  (hc : ∀ ⦃T T' : Over S⦄ (g : T' ⟶ T), (familyPicardFunctor p).map g.op (c T) = c T')

/-- Translation is `ξ ↦ ξ + γ_T` with inverse `ξ ↦ ξ - γ_T`. -/
example {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    (translationNatIso c hc).hom.app (op T) ξ = ξ + translationSection c T ∧
      (translationNatIso c hc).inv.app (op T) ξ = ξ - translationSection c T :=
  ⟨rfl, rfl⟩

/-- If `D(a + c T) ↔ C(a)` pointwise, translation carries `Pic^C` onto `Pic^D`, and a
representation of `Pic^D` on locally Noetherian test schemes is one of `Pic^C`. -/
example {C D : FiberCondition p}
    (hCD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
      D.Holds T (a + c T) t ↔ C.Holds T a t)
    {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) {Q : Scheme.LocallyNoetherianOver S}
    (R : D.locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q) :
    (ξ ∈ C.subfunctor.obj (op T) ↔
        (translationNatIso c hc).hom.app (op T) ξ ∈ D.subfunctor.obj (op T)) ∧
      Nonempty (C.locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q) :=
  ⟨FiberCondition.mem_subfunctor_iff_translation hc hCD ξ,
    ⟨FiberCondition.representableByOfTranslation hc hCD R⟩⟩

end Translation

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι)

/-! ### The fibre identities -/

/-- The fibre identities of the twist `L ↦ L(m)`: `h^q(X_t, L(m)_t(n)) = h^q(X_t, L_t(n + m))`
and `χ(X_t, L(m)_t^{-1}(n)) = χ(X_t, L_t^{-1}(n - m))`, with `[L(m)] = [L] + m • o_T(1)`. -/
example [IsClosedImmersion i] {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of A))
    (L : LineBundle (pullback (i ≫ toSpec A ι) s)) (t : T) (m n : ℤ) (q : ℕ) :
    fiberTwistDim i s (pulledTwistLineBundle i s m L) t n q = fiberTwistDim i s L t (n + m) q ∧
      fiberDualTwistEulerChar i s (pulledTwistLineBundle i s m L) t n =
        fiberDualTwistEulerChar i s L t (n - m) ∧
      classOf _ (pulledTwistLineBundle i s m L) = classOf _ L + m • fiberTwistClass i s 1 :=
  ⟨fiberTwistDim_pulledTwistLineBundle i s L t m n q,
    fiberDualTwistEulerChar_pulledTwistLineBundle i s L t m n,
    classOf_pulledTwistLineBundle i s m L⟩

/-! ### The twist of `Pic_{X/S,(fppf)}` -/

/-- `τ_m` is `ξ ↦ ξ + o_T(m)`, with inverse `ξ ↦ ξ - o_T(m)`, and `o_T(m) = m • o_T(1)` is
compatible with pullback. -/
example (m : ℤ) {T T' : Over (Spec (CommRingCat.of A))} (g : T' ⟶ T)
    (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T)) :
    (twistNatIso i m).hom.app (op T) ξ = ξ + twistSection i m T ∧
      (twistNatIso i m).inv.app (op T) ξ = ξ - twistSection i m T ∧
      twistSection i m T = m • twistSection i 1 T ∧
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map g.op (twistSection i m T) =
        twistSection i m T' :=
  ⟨twistNatIso_hom_app i m ξ, twistNatIso_inv_app i m ξ, twistSection_eq_zsmul i m T,
    map_twistSection i m g⟩

section Strata

variable [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] (N : ℕ) (e : ι ≃ Fin (N + 1))

/-- **The strata correspond under `τ_m`**, on every `S`-scheme `T`: `Pic^{φ,ψ,r}_m` onto
`Pic^{φ₀,ψ,r}_0`, `Pic^φ_m` onto `Pic^{φ₀}_0` and the locus of `C_m` onto that of `C_0`. -/
example (φ ψ : ℚ[X]) (m : ℤ) (r : ℕ) {T : Over (Spec (CommRingCat.of A))}
    (ξ : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T)) :
    (ξ ∈ (fineCondition i N e φ ψ m r).subfunctor.obj (op T) ↔
        ξ + twistSection i m T ∈
          (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0 r).subfunctor.obj
            (op T)) ∧
      (ξ ∈ (coarseCondition i N e φ m).subfunctor.obj (op T) ↔
        ξ + twistSection i m T ∈
          (coarseCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) 0).subfunctor.obj
            (op T)) ∧
      (ξ ∈ (coarseLevelCondition i N e m).subfunctor.obj (op T) ↔
        ξ + twistSection i m T ∈ (coarseLevelCondition i N e 0).subfunctor.obj (op T)) :=
  ⟨mem_fine_iff_twist φ ψ m r ξ, mem_coarse_iff_twist φ m ξ, mem_coarseLevel_iff_twist m ξ⟩

/-- The induced isomorphism `Pic^{φ,ψ,r}_m ≅ Pic^{φ₀,ψ,r}_0` is `ξ ↦ ξ + o_T(m)`. -/
example (φ ψ : ℚ[X]) (m : ℤ) (r : ℕ) {T : Over (Spec (CommRingCat.of A))}
    (ξ : (fineCondition i N e φ ψ m r).subfunctor.toFunctor.obj (op T)) :
    ((fineTwistIso φ ψ m r).hom.app (op T) ξ).1 =
      (show (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op T) from ξ.1) + twistSection i m T :=
  fineTwistIso_hom_app_val φ ψ m r ξ

/-- **Transport of a representation**: a representation of `Pic^{φ₀,ψ,r}_0` on locally
Noetherian test schemes by `Q` is one of `Pic^{φ,ψ,r}_m` by `Q`, through `τ_m`. -/
example {φ ψ : ℚ[X]} {m : ℤ} {r : ℕ} {Q : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (R : (fineCondition i N e (φ.comp (Polynomial.X - Polynomial.C (m : ℚ))) ψ 0
      r).locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q)
    {Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (g : Z ⟶ Q) :
    ((fineRepresentableByOfTwist R).homEquiv g).1 =
      (show (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op Z.obj) from (R.homEquiv g).1) -
        twistSection i m Z.obj :=
  fineRepresentableByOfTwist_homEquiv_val R g

end Strata

/-! ### Axiom guards -/

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.translationNatIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms translationNatIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.holdsAt_add_translationSection_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.holdsAt_add_translationSection_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.mem_subfunctor_iff_translation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.mem_subfunctor_iff_translation

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.subfunctorTranslationIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.subfunctorTranslationIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.representableByOfTranslation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.representableByOfTranslation

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.twistNatIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms twistNatIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.twistSection_eq_zsmul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms twistSection_eq_zsmul

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.mem_fine_iff_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_fine_iff_twist

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.mem_coarse_iff_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_coarse_iff_twist

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.mem_coarseLevel_iff_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mem_coarseLevel_iff_twist

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fineTwistIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fineTwistIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.coarseTwistIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coarseTwistIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fineLocallyNoetherianTwistIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fineLocallyNoetherianTwistIso

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fineRepresentableByOfTwist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fineRepresentableByOfTwist

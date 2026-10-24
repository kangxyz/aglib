/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula
public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Representability

/-! Focused consumer of `LinSys_{L/X/S}` in the locally free regime (Kleiman,
arXiv:math/0504020v1, Def. 3.12 and Thm 3.13, pp. 25–26; Picard plan row F15, task 10): the
properness and flatness of `Gr(E, k) ⟶ S`, the divisor of a single point of `Gr(E, k)` and of a
line subbundle, the nonvanishing of sections, the bijection with `Gr(E, k)(T)`, its naturality,
and the representability of `LinSys` by `Gr(E, k)` with its universal divisor. The instance in
`Aglib.RingTheory.Grassmannian.BaseChangeFormula` supplies the premise `BaseChangeMkQFormula`.
Each main statement is guarded for the standard axioms. -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace AglibTest.PicardLinearSystem

open Scheme.Modules Scheme.Modules.Invertible Scheme.LinearSystem Grassmannian

/-- `Gr(E, k) ⟶ S` is proper, smooth, flat and separated for `E` of constant rank `n`. -/
example {S : Scheme.{u}} (E : S.Modules) (k n : ℕ) (h : SheafHasRank E n) :
    IsProper (grassmannianBundle E k n h).hom ∧ Smooth (grassmannianBundle E k n h).hom ∧
      Flat (grassmannianBundle E k n h).hom ∧ IsSeparated (grassmannianBundle E k n h).hom :=
  ⟨isProper_grassmannianBundle_hom E k n h, smooth_grassmannianBundle_hom E k n h,
    flat_grassmannianBundle_hom E k n h, isSeparated_grassmannianBundle_hom E k n h⟩

/-- The kernel of a point of `Gr(F, k)`, for `F` of rank `k + 1`, is a line bundle; conversely a
fibrewise nonzero map from a line bundle gives a point of `Gr(F, k)` whose kernel is that map. -/
example {X : Scheme.{u}} {F : X.Modules} {k : ℕ} (hF : SheafHasRank F (k + 1))
    (P : LocallyFreeQuotientOf F k) {N : X.Modules} (hN : IsLocallyRankOne X N) (u : N ⟶ F)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ X),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    IsLocallyRankOne X (kernel P.π) ∧
      ∃ e : N ≅ kernel (LocallyFreeQuotientOf.ofLineSubbundle hF hN u hu).π,
        e.hom ≫ kernel.ι (LocallyFreeQuotientOf.ofLineSubbundle hF hN u hu).π = u :=
  ⟨P.isLocallyRankOne_kernel hF,
    LocallyFreeQuotientOf.exists_iso_hom_kernel_ι_ofLineSubbundle hF hN u hu⟩

/-- A nonzero section of `E_T`, with the base-change map an isomorphism, is nonzero on `X_T`. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) (T : Over S)
    (hbc : IsIso (moduleBaseChangeMap p T.hom L.val)) {N : T.left.Modules}
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) (hu : u ≠ 0) :
    subbundleSection p L T u ≠ 0 :=
  subbundleSection_ne_zero p L T hbc u hu

/-- The divisor of a line subbundle `u : N ⟶ E_T` lies in the linear system, with ideal
`q_T^* N ⊗ g_T^* L^∨`. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) [Flat p]
    [LocallyOfFinitePresentation p] [GeometricallyIntegral p]
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) (N : LineBundle T.left) (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T)
    (hu : ∀ (K : Type u) [Field K] (t : Spec (.of K) ⟶ T.left),
      (Scheme.Modules.pullback t).map u ≠ 0) :
    IsLinearSystemDivisor p L T (subbundleDivisor p L T u) ∧
      (subbundleDivisorIdealIso p L hbc T N u hu).hom ≫
        Scheme.Hom.idealInclusion (subbundleDivisor p L T u).subschemeι =
          subbundlePairing p L T u :=
  ⟨isLinearSystemDivisor_subbundleDivisor p L hbc T N u hu,
    subbundleDivisorIdealIso_hom_idealInclusion p L hbc T N u hu⟩

/-- The divisor of a single point of `Gr(E, k)` over `T` lies in the linear system. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) [Flat p]
    [LocallyOfFinitePresentation p] [GeometricallyIntegral p]
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val)) {k : ℕ}
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S)
    (P : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k) :
    IsLinearSystemDivisor p L T (quotientDivisor p L T P) :=
  isLinearSystemDivisor_quotientDivisor p L hbc hE T P

/-- The divisor of a point of `Gr(E, k)` commutes with base change. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) {k : ℕ}
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) {T T' : Over S} (t : T' ⟶ T)
    (P : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k) :
    quotientDivisor p L T' (P.pullbackOver t) = (quotientDivisor p L T P).comap (familyMap p t) :=
  quotientDivisor_pullbackOver p L hE t P

/-- `Gr(E, k)(T) ≃ LinSys_{L/X/S}(T)`. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) [IsLocallyNoetherian S] [IsProper p]
    [Flat p] [GeometricallyIntegral p]
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val)) {k : ℕ}
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) (T : Over S) :
    (quotBundleFunctor ((pushforward p).obj L.val) k).obj (op T) ≃
      (linearSystemFunctor p L).obj (op T) :=
  quotientDivisorEquiv p L hbc hE T

/-- `LinSys_{L/X/S}` is represented by `Gr(E, k)`. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) [IsLocallyNoetherian S] [IsProper p]
    [Flat p] [GeometricallyIntegral p]
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val)) {k : ℕ}
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) :
    (linearSystemFunctor p L).RepresentableBy
      (grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE) :=
  linearSystemRepresentableBy p L hbc hE

/-- `LinSys_{L/X/S}` is representable by a scheme proper, smooth and flat over `S`. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) [IsLocallyNoetherian S] [IsProper p]
    [Flat p] [GeometricallyIntegral p]
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val)) {k : ℕ}
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) :
    ∃ R : Over S, Nonempty ((linearSystemFunctor p L).RepresentableBy R) ∧
      IsProper R.hom ∧ Smooth R.hom ∧ Flat R.hom :=
  exists_representableBy_linearSystemFunctor p L hbc hE

/-- Every divisor of the linear system is the pullback of the universal divisor along a unique
map to `Gr(E, k)`; the universal divisor is the divisor of the universal quotient. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) [IsLocallyNoetherian S] [IsProper p]
    [Flat p] [GeometricallyIntegral p]
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val)) {k : ℕ}
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) {T : Over S}
    (D : (linearSystemFunctor p L).obj (op T)) :
    (∃! g : T ⟶ grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE,
      D.1 = (universalLinearSystemDivisor p L hbc hE).1.comap (familyMap p g)) ∧
    (universalLinearSystemDivisor p L hbc hE).1 = quotientDivisor p L _
      (universalBundleQuotientRep ((pushforward p).obj L.val) k (k + 1) hE) :=
  ⟨existsUnique_comap_universalLinearSystemDivisor p L hbc hE D,
    universalLinearSystemDivisor_val p L hbc hE⟩

/-- On locally Noetherian test schemes, `LinSys_{L/X/S}` is represented by `Gr(E, k)`. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) [IsLocallyNoetherian S] [IsProper p]
    [Flat p] [GeometricallyIntegral p]
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val)) {k : ℕ}
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) :
    ((Scheme.locallyNoetherianOverInclusion S).op ⋙ linearSystemFunctor p L).RepresentableBy
      (grassmannianBundleLocallyNoetherianOver p L hE) :=
  locallyNoetherianLinearSystemRepresentableBy p L hbc hE

/-- Where `h^0 = 0` the linear system has no divisor over a nonempty base. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X) [GeometricallyIntegral p]
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) 0) (T : Over S)
    {D : (Limits.pullback p T.hom).IdealSheafData} (hD : IsLinearSystemDivisor p L T D) :
    IsEmpty T.left :=
  isEmpty_of_isLinearSystemDivisor_of_sheafHasRank_zero p L hbc hE T hD

/-- Pullback along the base change of the family is fully faithful on line bundles. -/
example {X S T : Scheme.{u}} (p : X ⟶ S) [IsLocallyNoetherian S] [IsProper p] [Flat p]
    [GeometricallyIntegral p] (g : T ⟶ S) (N N' : T.Modules) (hN' : IsLocallyRankOne T N') :
    Function.Bijective
      (fun φ : N ⟶ N' ↦ (Scheme.Modules.pullback (Limits.pullback.snd p g)).map φ) :=
  bijective_pullback_snd_map_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral p g N N' hN'

/--
info: 'AlgebraicGeometry.Grassmannian.isProper_grassmannianBundle_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Grassmannian.isProper_grassmannianBundle_hom

/--
info: 'AlgebraicGeometry.Grassmannian.flat_grassmannianBundle_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Grassmannian.flat_grassmannianBundle_hom

/--
info: 'AlgebraicGeometry.Grassmannian.smooth_grassmannianBundle_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Grassmannian.smooth_grassmannianBundle_hom

/--
info: 'AlgebraicGeometry.Grassmannian.isSeparated_grassmannianBundle_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Grassmannian.isSeparated_grassmannianBundle_hom

/--
info: 'AlgebraicGeometry.Grassmannian.LocallyFreeQuotientOf.isLocallyRankOne_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocallyFreeQuotientOf.isLocallyRankOne_kernel

/--
info: 'AlgebraicGeometry.Grassmannian.LocallyFreeQuotientOf.exists_iso_hom_kernel_ι_ofLineSubbundle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocallyFreeQuotientOf.exists_iso_hom_kernel_ι_ofLineSubbundle

/--
info: 'AlgebraicGeometry.Scheme.Modules.bijective_pullbackPairingOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Modules.bijective_pullbackPairingOf

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.bijective_pullback_snd_map_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.Modules.Invertible.bijective_pullback_snd_map_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.pullback_map_evaluationMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pullback_map_evaluationMap

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.pullback_fst_map_subbundleSection_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pullback_fst_map_subbundleSection_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.subbundleSection_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms subbundleSection_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.isLinearSystemDivisor_subbundleDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLinearSystemDivisor_subbundleDivisor

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.isLinearSystemDivisor_quotientDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isLinearSystemDivisor_quotientDivisor

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.exists_subbundle_of_isLinearSystemDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_subbundle_of_isLinearSystemDivisor

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.exists_comp_eq_of_subbundleDivisor_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_comp_eq_of_subbundleDivisor_eq

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.bijective_quotientDivisorMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bijective_quotientDivisorMap

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.quotientDivisor_pullbackOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms quotientDivisor_pullbackOver

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.linearSystemRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms linearSystemRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.exists_representableBy_linearSystemFunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_representableBy_linearSystemFunctor

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.existsUnique_comap_universalLinearSystemDivisor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms existsUnique_comap_universalLinearSystemDivisor

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.locallyNoetherianLinearSystemRepresentableBy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms locallyNoetherianLinearSystemRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.isEmpty_of_isLinearSystemDivisor_of_sheafHasRank_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isEmpty_of_isLinearSystemDivisor_of_sheafHasRank_zero

/--
info: 'AlgebraicGeometry.Scheme.LinearSystem.universalLinearSystemDivisor_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms universalLinearSystemDivisor_val

end AglibTest.PicardLinearSystem

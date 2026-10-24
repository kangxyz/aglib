/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Bijection
public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Representability
public import Aglib.AlgebraicGeometry.Grassmannian.LocallyFree.Proper
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.Pullback
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver

/-!
# `LinSys_{L/X/S}` is represented by `Gr(E, k)`

Let `p : X ⟶ S` be proper, flat and geometrically integral over a locally Noetherian `S`, and
`L` a line bundle on `X` such that `E = p_* L` is finite locally free of constant rank `k + 1`
and every base-change map of `L` is an isomorphism (statement 15a of the Picard plan, on a
piece of constant `h^0`). Then the linear-system functor `LinSys_{L/X/S}` is represented by the
Grassmannian bundle `Gr(E, k)` of rank-`k` locally free quotients of `E` (equivalently, of line
subbundles of `E` with locally free quotient), with universal divisor the divisor of the
universal quotient (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 3.13, pp. 25–26,
and Ex. 3.14, p. 26, there written `P(Q)` with `Q = E^∨` in the locally free case).

* `subbundleDivisor_comap`, `quotientDivisor_pullbackOver`: the divisor of a line subbundle,
  and of a point of `Gr(E, k)`, commutes with base change along `T' ⟶ T`
  (`pullback_map_evaluationMap`, `pullbackPairingOf_pullback`, `imageIdealData_pullback`).
* `quotientDivisorMap_naturality`: the divisor map `Gr(E, k)(T) ⟶ LinSys(T)` is natural.
* `linearSystemRepresentableBy`: `LinSys_{L/X/S}` is represented by `Gr(E, k)` on all schemes
  over `S`; `locallyNoetherianLinearSystemRepresentableBy`: the same on locally Noetherian test
  schemes (`Scheme.LocallyNoetherianOver S`, as for the Hilbert scheme), where `Gr(E, k)` is a
  locally Noetherian test scheme (`grassmannianBundleLocallyNoetherianOver`);
  `exists_representableBy_linearSystemFunctor`: by a scheme proper, smooth and flat over `S`
  (`Grassmannian/LocallyFree/Proper`).
* `universalLinearSystemDivisor`, `universalLinearSystemDivisor_val`,
  `existsUnique_comap_universalLinearSystemDivisor`: the universal divisor on
  `X ×_S Gr(E, k)` and its universal property.

Premise: `BaseChangeMkQFormula` for `Fin (k + 1)`, as for `Gr(E, k)` itself. The case
`h^0 = 0` and the gluing over the pieces of constant `h^0` are not treated here.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {X X' P : Scheme.{u}} (p : X ⟶ P) {N L : P.Modules}

/-- **The zero scheme of a pairing commutes with base change**: if `c : M' ≅ b^* M` carries
`j' : M' ⟶ p'^* N` to the pullback of `j : M ⟶ p^* N` along `b` (with `b ≫ p = p'`), the image
ideal of the pairing of `j'` is the pullback along `b` of the image ideal of the pairing of `j`.
Stated at variable data. -/
theorem imageIdealData_pullbackPairingOf_of_comp_eq (b : X' ⟶ X) (p' : X' ⟶ P)
    (hb : b ≫ p = p')
    (ε : (show P.Modules from tensorSheaf P N L) ⟶
      (show P.Modules from SheafOfModules.unit P.ringCatSheaf))
    {M : X.Modules} (j : M ⟶ (pullback p).obj N) {M' : X'.Modules}
    (c : M' ⟶ (pullback b).obj M) [IsIso c] (j' : M' ⟶ (pullback p').obj N)
    (hj : c ≫ (pullback b).map j =
      j' ≫ (pullbackCongr hb.symm).hom.app N ≫ (pullbackComp b p).inv.app N)
    (hM : SheafOfModules.IsQuasicoherent
      (show X.Modules from tensorSheaf X M ((pullback p).obj L))) :
    Hom.imageIdealData (pullbackPairingOf p' ε j') =
      (Hom.imageIdealData (pullbackPairingOf p ε j)).comap b := by
  have key := pullbackPairingOf_pullback p b p' hb ε j c j' hj
  have hkey : pullbackPairingOf p' ε j' =
      (tensorSheafIso X' (asIso c) ((pullbackCongr hb.symm).app L ≪≫
          ((pullbackComp b p).app L).symm) ≪≫
        (pullbackTensorMapIso b M ((pullback p).obj L)).symm).hom ≫
      Hom.pullbackToUnit b (pullbackPairingOf p ε j) := by
    rw [← key]
    simp only [Iso.trans_hom, Iso.symm_hom, tensorSheafIso_hom, asIso_hom, Iso.app_hom,
      Iso.app_inv, Category.assoc, Hom.pullbackToUnit]
  have := hM
  rw [hkey, Hom.imageIdealData_precomp_iso, Hom.imageIdealData_pullback]

end Modules

namespace LinearSystem

open Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard Grassmannian

/-- Reversing an equality of scheme maps inverts the pullback comparison. -/
theorem pullbackCongr_symm_hom_app {Y Z : Scheme.{u}} {f f' : Y ⟶ Z} (h : f = f')
    (M : Z.Modules) : (pullbackCongr h.symm).hom.app M = (pullbackCongr h).inv.app M := by
  subst h
  rfl

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)

/-- **Base change of the section of a map, at variable data**: for a commutative square
`b ≫ q = q' ≫ τ` with `b ≫ g = g'`, evaluation maps `ev : q^* E ⟶ g^* L` and
`ev' : q'^* E' ⟶ g'^* L` related through `E' ≅ τ^* E`, and maps `u : N ⟶ E`, `u' : N' ⟶ E'`
related through `κ : N' ≅ τ^* N`, the pullback along `b` of `q^* u ≫ ev` is `q'^* u' ≫ ev'`
under the canonical comparisons. -/
theorem pullback_map_comp_evaluation_of_square {Y Y' B B' Z : Scheme.{u}} {q : Y ⟶ B}
    {q' : Y' ⟶ B'} {g : Y ⟶ Z} {g' : Y' ⟶ Z} {b : Y' ⟶ Y} {τ : B' ⟶ B}
    (hq : b ≫ q = q' ≫ τ) (hg : b ≫ g = g') {E : B.Modules} {E' : B'.Modules}
    (eE : E' ≅ (Scheme.Modules.pullback τ).obj E) {M : Z.Modules}
    (ev : (Scheme.Modules.pullback q).obj E ⟶ (Scheme.Modules.pullback g).obj M)
    (ev' : (Scheme.Modules.pullback q').obj E' ⟶ (Scheme.Modules.pullback g').obj M)
    (hev : (Scheme.Modules.pullback q').map eE.hom ≫
        (pullbackSquareIso b q' q τ hq).hom.app E ≫ (Scheme.Modules.pullback b).map ev =
      ev' ≫ (pullbackTriangleIso b g g' hg).inv.app M)
    {N : B.Modules} (u : N ⟶ E) {N' : B'.Modules} (u' : N' ⟶ E')
    (κ : N' ≅ (Scheme.Modules.pullback τ).obj N)
    (hκ : κ.hom ≫ (Scheme.Modules.pullback τ).map u = u' ≫ eE.hom) :
    ((Scheme.Modules.pullback q').map κ.hom ≫ (pullbackSquareIso b q' q τ hq).hom.app N) ≫
        (Scheme.Modules.pullback b).map ((Scheme.Modules.pullback q).map u ≫ ev) =
      ((Scheme.Modules.pullback q').map u' ≫ ev') ≫ (pullbackCongr hg.symm).hom.app M ≫
        (pullbackComp b g).inv.app M := by
  have hnat := (pullbackSquareIso b q' q τ hq).hom.naturality u
  simp only [Functor.comp_map] at hnat
  rw [pullbackTriangleIso_inv_app] at hev
  rw [pullbackCongr_symm_hom_app hg]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnat, ← CategoryTheory.Functor.map_comp_assoc, hκ,
    CategoryTheory.Functor.map_comp_assoc, hev]

/-- **The section of a line subbundle commutes with base change**: for `t : T' ⟶ T` and
`u' : N' ⟶ E_{T'}` corresponding to `t^* u` under `κ : N' ≅ t^* N` and `E_{T'} ≅ t^* E_T`, the
pullback along `b : X_{T'} ⟶ X_T` of the section of `u` is the section of `u'`, under the
canonical comparisons (`pullback_map_evaluationMap`). -/
theorem subbundleSection_baseChange {T T' : Over S} (t : T' ⟶ T) {N : T.left.Modules}
    (u : N ⟶ overPullback ((pushforward p).obj L.val) T) {N' : T'.left.Modules}
    (u' : N' ⟶ overPullback ((pushforward p).obj L.val) T')
    (κ : N' ≅ (Scheme.Modules.pullback t.left).obj N)
    (hκ : κ.hom ≫ (Scheme.Modules.pullback t.left).map u =
      u' ≫ (overPullbackIso ((pushforward p).obj L.val) t).hom) :
    ((Scheme.Modules.pullback (Limits.pullback.snd p T'.hom)).map κ.hom ≫
      (pullbackSquareIso (familyMap p t) (Limits.pullback.snd p T'.hom)
        (Limits.pullback.snd p T.hom) t.left (familyMap_snd p t)).hom.app N) ≫
      (Scheme.Modules.pullback (familyMap p t)).map (subbundleSection p L T u) =
      subbundleSection p L T' u' ≫ (pullbackCongr (familyMap_fst p t).symm).hom.app L.val ≫
        (pullbackComp (familyMap p t) (Limits.pullback.fst p T.hom)).inv.app L.val :=
  pullback_map_comp_evaluation_of_square (familyMap_snd p t) (familyMap_fst p t)
    (overPullbackIso ((pushforward p).obj L.val) t) (evaluationMap p L T) (evaluationMap p L T')
    (pullback_map_evaluationMap p L t) u u' κ hκ

/-- **The divisor of a line subbundle commutes with base change**: for `t : T' ⟶ T`, a map
`u : N ⟶ E_T` from a line bundle and `u' : N' ⟶ E_{T'}` corresponding to `t^* u` under an
isomorphism `N' ≅ t^* N` and `E_{T'} ≅ t^* E_T`, the divisor of `u'` is the pullback of the
divisor of `u` along `X_{T'} ⟶ X_T`. -/
theorem subbundleDivisor_comap {T T' : Over S} (t : T' ⟶ T) (N : LineBundle T.left)
    (u : N.val ⟶ overPullback ((pushforward p).obj L.val) T) {N' : T'.left.Modules}
    (u' : N' ⟶ overPullback ((pushforward p).obj L.val) T')
    (κ : N' ≅ (Scheme.Modules.pullback t.left).obj N.val)
    (hκ : κ.hom ≫ (Scheme.Modules.pullback t.left).map u =
      u' ≫ (overPullbackIso ((pushforward p).obj L.val) t).hom) :
    subbundleDivisor p L T' u' = (subbundleDivisor p L T u).comap (familyMap p t) := by
  have hqc : (subbundlePairingSource p L T N).val.IsQuasicoherent := by
    have := lineBundle_isLocallyFree _ (subbundlePairingSource p L T N)
    infer_instance
  exact imageIdealData_pullbackPairingOf_of_comp_eq (Limits.pullback.fst p T.hom)
    (familyMap p t) (Limits.pullback.fst p T'.hom) (familyMap_fst p t)
    (evaluationPairing L) (subbundleSection p L T u) _ (subbundleSection p L T' u')
    (subbundleSection_baseChange p L t u u' κ hκ) hqc

variable {k : ℕ}

/-- **The divisor of a point of `Gr(E, k)` commutes with base change**: the divisor of the
pulled-back quotient is the pullback of the divisor along `X_{T'} ⟶ X_T`. The kernel of the
pulled-back quotient is the pullback of the kernel (`pullbackKernelIso`). -/
theorem quotientDivisor_pullbackOver (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1))
    {T T' : Over S} (t : T' ⟶ T)
    (P : LocallyFreeQuotientOf (overPullback ((pushforward p).obj L.val) T) k) :
    quotientDivisor p L T' (P.pullbackOver t) =
      (quotientDivisor p L T P).comap (familyMap p t) := by
  have : IsFiniteLocallyFree T.left P.obj := P.hasRank.isFiniteLocallyFree
  let κ₁ : kernel (P.pullbackOver t).π ≅ kernel ((Scheme.Modules.pullback t.left).map P.π) :=
    kernel.mapIso (P.pullbackOver t).π ((Scheme.Modules.pullback t.left).map P.π)
      (overPullbackIso ((pushforward p).obj L.val) t) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]; rfl)
  refine subbundleDivisor_comap p L t (quotientKernelLineBundle p L hE T P) (kernel.ι P.π)
    (kernel.ι (P.pullbackOver t).π) (κ₁ ≪≫ (pullbackKernelIso t.left P.π).symm) ?_
  simp [κ₁]

section Representability

variable [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- **The divisor map is natural in `T`**. -/
theorem quotientDivisorMap_naturality
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) {T T' : Over S} (t : T' ⟶ T)
    (x : (quotBundleFunctor ((pushforward p).obj L.val) k).obj (op T)) :
    quotientDivisorMap p L hbc hE T'
        ((quotBundleFunctor ((pushforward p).obj L.val) k).map t.op x) =
      (linearSystemFunctor p L).map t.op (quotientDivisorMap p L hbc hE T x) := by
  induction x using Quotient.inductionOn with | h P => ?_
  exact Subtype.ext (quotientDivisor_pullbackOver p L hE t P)

variable [∀ R : CommRingCat.{u}, Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R
  (Fin (k + 1) → R)]

/-- **`LinSys_{L/X/S}` is represented by `Gr(E, k)`** (Kleiman, Thm 3.13, pp. 25–26, and
Ex. 3.14, p. 26), on all schemes over `S`: for `p` proper, flat and geometrically integral over
a locally Noetherian `S`, `E = p_* L` of constant rank `k + 1` and every base-change map of `L`
an isomorphism, `T ⟶ Gr(E, k)` corresponds to the divisor of the pulled-back universal
quotient. -/
def linearSystemRepresentableBy
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) :
    (linearSystemFunctor p L).RepresentableBy
      (grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE) where
  homEquiv {T} := (grassmannianBundleRepresentableBy ((pushforward p).obj L.val) k (k + 1)
    hE).homEquiv.trans (quotientDivisorEquiv p L hbc hE T)
  homEquiv_comp {T T'} f g := by
    rw [Equiv.trans_apply, Equiv.trans_apply,
      (grassmannianBundleRepresentableBy ((pushforward p).obj L.val) k (k + 1) hE).homEquiv_comp,
      quotientDivisorEquiv_apply, quotientDivisorEquiv_apply]
    exact quotientDivisorMap_naturality p L hbc hE f _

theorem linearSystemRepresentableBy_homEquiv
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) {T : Over S}
    (g : T ⟶ grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE) :
    (linearSystemRepresentableBy p L hbc hE).homEquiv g = quotientDivisorMap p L hbc hE T
      ((grassmannianBundleRepresentableBy ((pushforward p).obj L.val) k (k + 1) hE).homEquiv g) :=
  rfl

/-- `Gr(E, k)` as a locally Noetherian test scheme over the locally Noetherian `S`: it is locally
of finite type over `S`. -/
def grassmannianBundleLocallyNoetherianOver
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) : Scheme.LocallyNoetherianOver S :=
  ⟨grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE, by
    have := locallyOfFiniteType_grassmannianBundle_hom ((pushforward p).obj L.val) k (k + 1) hE
    exact LocallyOfFiniteType.isLocallyNoetherian
      (grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE).hom⟩

/-- **`LinSys_{L/X/S}` on locally Noetherian test schemes is represented by `Gr(E, k)`** (the
convention of `HilbertScheme/Representability`): the restriction of
`linearSystemRepresentableBy` along the inclusion of `Scheme.LocallyNoetherianOver S`. -/
def locallyNoetherianLinearSystemRepresentableBy
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) :
    ((Scheme.locallyNoetherianOverInclusion S).op ⋙ linearSystemFunctor p L).RepresentableBy
      (grassmannianBundleLocallyNoetherianOver p L hE) where
  homEquiv {T} := (Scheme.locallyNoetherianOver S).fullyFaithfulι.homEquiv.trans
    (linearSystemRepresentableBy p L hbc hE).homEquiv
  homEquiv_comp {T T'} f g := by
    change (linearSystemRepresentableBy p L hbc hE).homEquiv
        ((Scheme.locallyNoetherianOverInclusion S).map (f ≫ g)) =
      (linearSystemFunctor p L).map ((Scheme.locallyNoetherianOverInclusion S).map f).op
        ((linearSystemRepresentableBy p L hbc hE).homEquiv
          ((Scheme.locallyNoetherianOverInclusion S).map g))
    rw [CategoryTheory.Functor.map_comp]
    exact (linearSystemRepresentableBy p L hbc hE).homEquiv_comp _ _

/-- **`LinSys_{L/X/S}` is representable by a scheme proper, smooth and flat over `S`** (the form
used for `R = Z ×_P Z` in the proof of Kleiman's Thm 4.8, p. 30). -/
theorem exists_representableBy_linearSystemFunctor
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) :
    ∃ R : Over S, Nonempty ((linearSystemFunctor p L).RepresentableBy R) ∧
      IsProper R.hom ∧ Smooth R.hom ∧ Flat R.hom :=
  ⟨_, ⟨linearSystemRepresentableBy p L hbc hE⟩,
    isProper_grassmannianBundle_hom _ k (k + 1) hE, smooth_grassmannianBundle_hom _ k (k + 1) hE,
    flat_grassmannianBundle_hom _ k (k + 1) hE⟩

/-- **The universal divisor** of the linear system, on `X ×_S Gr(E, k)`. -/
def universalLinearSystemDivisor
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) :
    (linearSystemFunctor p L).obj
      (op (grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE)) :=
  (linearSystemRepresentableBy p L hbc hE).homEquiv (𝟙 _)

/-- The universal divisor is the divisor of the universal quotient. -/
theorem universalLinearSystemDivisor_val
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) :
    (universalLinearSystemDivisor p L hbc hE).1 =
      quotientDivisor p L _
        (universalBundleQuotientRep ((pushforward p).obj L.val) k (k + 1) hE) := by
  rw [universalLinearSystemDivisor, linearSystemRepresentableBy_homEquiv]
  change (quotientDivisorMap p L hbc hE _
    (universalBundleQuotient ((pushforward p).obj L.val) k (k + 1) hE)).1 = _
  rw [← mk_universalBundleQuotientRep]
  rfl

/-- **The universal property of the universal divisor**: every divisor of the linear system over
`T` is the pullback of the universal divisor along a unique `T ⟶ Gr(E, k)` over `S`. -/
theorem existsUnique_comap_universalLinearSystemDivisor
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (hE : SheafHasRank ((pushforward p).obj L.val) (k + 1)) {T : Over S}
    (D : (linearSystemFunctor p L).obj (op T)) :
    ∃! g : T ⟶ grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE,
      D.1 = (universalLinearSystemDivisor p L hbc hE).1.comap (familyMap p g) := by
  have hcomp (g : T ⟶ grassmannianBundle ((pushforward p).obj L.val) k (k + 1) hE) :
      (linearSystemRepresentableBy p L hbc hE).homEquiv g =
        (linearSystemFunctor p L).map g.op (universalLinearSystemDivisor p L hbc hE) := by
    rw [universalLinearSystemDivisor, ← (linearSystemRepresentableBy p L hbc hE).homEquiv_comp,
      Category.comp_id]
  refine ⟨(linearSystemRepresentableBy p L hbc hE).homEquiv.symm D, ?_, fun g hg ↦ ?_⟩
  · have h := hcomp ((linearSystemRepresentableBy p L hbc hE).homEquiv.symm D)
    rw [Equiv.apply_symm_apply] at h
    exact congrArg Subtype.val h
  · apply (linearSystemRepresentableBy p L hbc hE).homEquiv.injective
    rw [Equiv.apply_symm_apply, hcomp]
    exact Subtype.ext hg.symm

end Representability

end LinearSystem

end AlgebraicGeometry.Scheme

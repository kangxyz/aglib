/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.Comap
public import Aglib.AlgebraicGeometry.Limits.FibreProductBaseChange
public import Aglib.AlgebraicGeometry.Picard.Fppf
public import Aglib.AlgebraicGeometry.Picard.Presheaf

/-!
# The Abel class of a relative effective Cartier divisor

For an effective Cartier divisor `i : D ⟶ X` the ideal `I_D = idealModule i` is invertible
(Kleiman, *The Picard scheme*, arXiv:math/0504020v1, 3.1, p. 22), and
`IsEffectiveCartier.idealLineBundle` is `I_D` as a line bundle. For a relative effective Cartier
divisor of `p : X ⟶ S` (Def. 3.3, p. 22) and a cartesian square of the base, the canonical
comparison `b^* I_D ⟶ I_{D'}` is an isomorphism because `D` is flat over `S`
(`IsRelativeEffectiveCartier.pullbackIdealLineBundleIso`, from
`Scheme.Hom.flatQuotient_idealPullbackMap_isIso`); this is Kleiman's remark after Def. 3.6,
p. 23 ("since `D` is `T`-flat, `p_{X_T}^* I` is equal to the ideal of `D_{T'}`"). In `Pic(Y)` it
reads `b^* [I_D] = [I_{D'}]` (`IsRelativeEffectiveCartier.pullbackClass_classOf_idealLineBundle`).

For `p : X ⟶ S`, an `S`-scheme `T` and a relative effective Cartier divisor `D ⊆ X ×_S T` over
`T` (a closed subscheme `D : (pullback p T.hom).IdealSheafData` with
`IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)`):

* `RelativePicard.abelClass p D hD = −[I_D] ∈ Pic(X ×_S T)`. Since `I_D = 𝒪(−D)` (3.1, p. 22),
  this is the class of `𝒪_{X_T}(D) = I_D^∨` (`abelClass_eq_classOf_dualLineBundle`), the value of
  Kleiman's Abel map on `D` (Def. 4.6, p. 27). No dual is needed to define it or to prove its
  naturality.
* Naturality in `T` (`familyPicardFunctor_map_abelClass`): for `g : T' ⟶ T` over `S`, the
  pullback of `abelClass p D hD` along `familyPicardFunctor p` is the Abel class of the pullback
  `D.comap ((familyScheme p).map g)` of `D` to `X ×_S T'`. The general form
  (`pullbackClass_abelClass`) holds for every cartesian square
  `X ×_S T' ⟶ X ×_S T` over `T' ⟶ T` with the literal fibre products, so it applies to any
  presentation of the base-change map (for example `pullback.map p _ p _ (𝟙 X) g.left (𝟙 S)`).
* The class of the Abel class in `Pic_{X/S,(fppf)}(T)` (`fppfAbelClass`, the image under
  `quotientProjection p ≫ toFppfPicardSheaf p`) is natural in the same sense
  (`fppfPicardSheaf_map_fppfAbelClass`).

All module sheaves on `X ×_S T` are typed over the literal fibre product `pullback p T.hom`, and
the naturality is stated with the base-change maps `(familyScheme p).map g` that
`familyPicardFunctor p` uses. No hypothesis on `p`, `S` or the test schemes is used. The natural
transformation from the divisor functor `Div_{X/S}` (Def. 3.6, p. 23) is not formed here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

open Modules.Invertible Modules.Invertible.PullbackTensor.Local

namespace Hom

variable {D X : Scheme.{u}}

/-- The ideal sheaf `I_D` of an effective Cartier divisor `i : D ⟶ X`, as a line bundle on `X`
(Kleiman, arXiv:math/0504020v1, 3.1, p. 22). -/
def IsEffectiveCartier.idealLineBundle {i : D ⟶ X} (h : IsEffectiveCartier i) : LineBundle X :=
  ⟨idealModule i, h.isLocallyRankOne⟩

@[simp]
theorem IsEffectiveCartier.idealLineBundle_val {i : D ⟶ X} (h : IsEffectiveCartier i) :
    h.idealLineBundle.val = idealModule i :=
  rfl

variable {S T Y D' : Scheme.{u}} {p : X ⟶ S} {q : T ⟶ S} {p' : Y ⟶ T} {b : Y ⟶ X}
  {i : D ⟶ X} {i' : D' ⟶ Y} {a : D' ⟶ D}

/-- **Base change of the ideal line bundle** of a relative effective Cartier divisor
(Kleiman, arXiv:math/0504020v1, remark after Def. 3.6, p. 23): for a cartesian square of the
base and the cartesian square of the divisor over it, the canonical comparison
`b^* I_D ⟶ I_{D'}` (`idealPullbackMap`) is an isomorphism, because `D` is flat over `S`
(`flatQuotient_idealPullbackMap_isIso`). -/
def IsRelativeEffectiveCartier.pullbackIdealLineBundleIso (H : IsPullback b p' p q)
    (H' : IsPullback a i' i b) (hD : IsRelativeEffectiveCartier i p) :
    (pullbackLineBundle b hD.idealLineBundle).val ≅
      (hD.of_isPullback H H').idealLineBundle.val :=
  @asIso _ _ _ _ (idealPullbackMap i i' b a H'.w)
    (@flatQuotient_idealPullbackMap_isIso S T X Y D D' p q p' b i i' a H'.w H H'
      hD.isClosedImmersion hD.flat)

/-- The class form of `pullbackIdealLineBundleIso`: `b^* [I_D] = [I_{D'}]` in `Pic(Y)`. -/
theorem IsRelativeEffectiveCartier.pullbackClass_classOf_idealLineBundle (H : IsPullback b p' p q)
    (H' : IsPullback a i' i b) (hD : IsRelativeEffectiveCartier i p) :
    pullbackClass b (classOf X hD.idealLineBundle) =
      classOf Y (hD.of_isPullback H H').idealLineBundle :=
  Quotient.sound ⟨hD.pullbackIdealLineBundleIso H H'⟩

end Hom

namespace RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- The base-change square of `X ×_S T' ⟶ X ×_S T` over `g : T' ⟶ T` is cartesian
(`Scheme.isPullback_pullbackMap_snd`). -/
theorem isPullback_familyScheme_map {T T' : Over S} (g : T' ⟶ T) :
    IsPullback ((familyScheme p).map g) (pullback.snd p T'.hom) (pullback.snd p T.hom) g.left :=
  isPullback_pullbackMap_snd p T.hom T'.hom g.left (Over.w g)

/-- **The Abel class** of a relative effective Cartier divisor `D ⊆ X ×_S T` over `T`: the class
`−[I_D] = [𝒪_{X_T}(D)]` in `Pic(X ×_S T)` (Kleiman, arXiv:math/0504020v1, Def. 4.6, p. 27, with
`I_D = 𝒪(−D)` by 3.1, p. 22). -/
def abelClass {T : Over S} (D : (pullback p T.hom).IdealSheafData)
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)) :
    PicardGroup (pullback p T.hom) :=
  -classOf _ hD.idealLineBundle

/-- The Abel class is the class of the dual `I_D^∨ = 𝒪_{X_T}(D)` of the ideal. -/
theorem abelClass_eq_classOf_dualLineBundle {T : Over S} (D : (pullback p T.hom).IdealSheafData)
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)) :
    abelClass p D hD = classOf _ (dualLineBundle _ hD.idealLineBundle) :=
  rfl

/-- **Base change of the Abel class along a cartesian square** (variable form): for any
`b : X ×_S T' ⟶ X ×_S T` forming a cartesian square with the second projections over
`f : T' ⟶ T`, the pullback of the Abel class of `D` is the Abel class of `D.comap b`. -/
theorem pullbackClass_abelClass {T T' : Over S} {b : pullback p T'.hom ⟶ pullback p T.hom}
    {f : T'.left ⟶ T.left}
    (H : IsPullback b (pullback.snd p T'.hom) (pullback.snd p T.hom) f)
    (D : (pullback p T.hom).IdealSheafData)
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)) :
    pullbackClass b (abelClass p D hD) =
      abelClass p (D.comap b) (hD.of_isPullback H (D.isPullback_subschemeMap_comap b)) := by
  rw [abelClass, abelClass, pullbackClass_neg,
    hD.pullbackClass_classOf_idealLineBundle H (D.isPullback_subschemeMap_comap b)]

/-- The pullback of a relative effective Cartier divisor along `(familyScheme p).map g` is a
relative effective Cartier divisor (Kleiman, arXiv:math/0504020v1, remark after Def. 3.6,
p. 23). -/
theorem isRelativeEffectiveCartier_comap_familyScheme_map {T T' : Over S} (g : T' ⟶ T)
    {D : (pullback p T.hom).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)) :
    Hom.IsRelativeEffectiveCartier (D.comap ((familyScheme p).map g)).subschemeι
      (pullback.snd p T'.hom) :=
  hD.of_isPullback (isPullback_familyScheme_map p g) (D.isPullback_subschemeMap_comap _)

/-- **Naturality of the Abel class in `T`**: for `g : T' ⟶ T` over `S`, the restriction along
`familyPicardFunctor p` of the Abel class of `D ⊆ X ×_S T` is the Abel class of the pulled-back
divisor `D.comap ((familyScheme p).map g) ⊆ X ×_S T'`. -/
theorem familyPicardFunctor_map_abelClass {T T' : Over S} (g : T' ⟶ T)
    (D : (pullback p T.hom).IdealSheafData)
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)) :
    ((familyPicardFunctor p).map g.op).hom (abelClass p D hD) =
      abelClass p (T := T') (D.comap ((familyScheme p).map g))
        (isRelativeEffectiveCartier_comap_familyScheme_map p g hD) :=
  pullbackClass_abelClass p (isPullback_familyScheme_map p g) D hD

/-- The Abel class as a section of `Pic_{X/S,(fppf)}` over `T`: the image of `abelClass p D hD`
under `Pic(X ×_S T) ⟶ P_{X/S}(T) ⟶ Pic_{X/S,(fppf)}(T)`. -/
def fppfAbelClass {T : Over S} (D : (pullback p T.hom).IdealSheafData)
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)) :
    (fppfPicardSheaf p).obj.obj (op T) :=
  (quotientProjection p ≫ toFppfPicardSheaf p).app (op T) (abelClass p D hD)

/-- **Naturality of the fppf Abel class in `T`**: for `g : T' ⟶ T` over `S`, the restriction of
`fppfAbelClass p D hD` along `g` is the fppf Abel class of `D.comap ((familyScheme p).map g)`. -/
theorem fppfPicardSheaf_map_fppfAbelClass {T T' : Over S} (g : T' ⟶ T)
    (D : (pullback p T.hom).IdealSheafData)
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p T.hom)) :
    (fppfPicardSheaf p).obj.map g.op (fppfAbelClass p D hD) =
      fppfAbelClass p (T := T') (D.comap ((familyScheme p).map g))
        (isRelativeEffectiveCartier_comap_familyScheme_map p g hD) := by
  unfold fppfAbelClass
  rw [← familyPicardFunctor_map_abelClass]
  exact (NatTrans.naturality_apply (quotientProjection p ≫ toFppfPicardSheaf p) g.op
    (abelClass p D hD)).symm

end RelativePicard

end AlgebraicGeometry.Scheme

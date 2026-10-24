/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Basic
public import Aglib.AlgebraicGeometry.Picard.Abel.Basic

/-!
# Abel classes of linear-system divisors and their transport to `X ×_S U`

Let `p : X ⟶ S` be a morphism of schemes, `L` a line bundle on `X`, `T` an `S`-scheme, and
`D ⊆ X_T = X ×_S T` a relative effective Cartier divisor over `T`, with Abel class
`abelClass p D hD = −[I_D] = [𝒪_{X_T}(D)]` (`Picard/Abel/Basic`). Write `g_T : X_T ⟶ X` and
`p_T : X_T ⟶ T` for the projections.

* `RelativePicard.quotientProjection_app_eq_iff`: two classes on `X_T` have the same image in
  `P_{X/S}(T) = Pic(X_T) / Pic(T)` if and only if they differ by a class pulled back from `T`.
* `LinearSystem.isLinearSystemDivisor_iff_exists_abelClass_eq`,
  `LinearSystem.isLinearSystemDivisor_iff_abelClass_sub_mem_baseImage`: `D` is a divisor of the
  linear system `LinSys_{L/X/S}(T)` (`IsLinearSystemDivisor`, the ideal form
  `I_D ≅ p_T^* N ⊗ g_T^* L^∨`) if and only if `abelClass D − g_T^*[L]` is pulled back from `T`.
  This is Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Def. 3.12, p. 25
  ("`O_{X_T}(D) ≃ L_T ⊗ f_T^* N` for some invertible sheaf `N` on `T`", with `f_T = p_T`), read in
  `Pic(X_T)` with `I_D = 𝒪(−D)` (3.1, p. 22).
  `LinearSystem.fppfAbelClass_eq_of_isLinearSystemDivisor` is its image in
  `Pic_{X/S,(fppf)}(T)`: the fppf Abel class of a divisor of the linear system is the class of
  `g_T^* L`.

For `g : U ⟶ V` over `S` the base-change square of `X ×_S U ⟶ X ×_S V` over `g` is cartesian
(`LinearSystem.isPullback_familyMap`), so `e := (isPullback_familyMap p g).isoPullback` is an
isomorphism `X ×_S U ≅ X_V ×_V U` over `U`, where `X_V = X ×_S V ⟶ V` is the family over `V` and
`U` is a `V`-scheme through `g`. Divisors of the family `X_V ⟶ V` over `U` are thereby divisors of
`X ⟶ S` over `U`:

* `RelativePicard.isRelativeEffectiveCartier_comap_isoPullback_hom`,
  `RelativePicard.abelClass_comap_isoPullback_hom`: pulling back along `e` preserves relative
  effective Cartier divisors and Abel classes; `isRelativeEffectiveCartier_comap_isoPullback_inv`
  is the inverse direction, and `comap_isoPullback_hom_comap_inv`,
  `comap_isoPullback_inv_comap_hom` are the two round trips;
* `RelativePicard.pullbackClass_isoPullback_hom_mem_baseImage_iff`: `e` identifies the classes
  pulled back from `U`;
* `LinearSystem.isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage`:
  for a line bundle `L` on `X_V`, a divisor `D ⊆ X_V ×_V U` lies in `LinSys_{L/X_V/V}(U)` if and
  only if the Abel class of its transport to `X ×_S U` differs from `g^*[L]` by a class pulled
  back from `U`; `LinearSystem.fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor` is
  the fppf form.

All statements are typed with the literal fibre products `pullback p T.hom` and the base-change
maps `LinearSystem.familyMap p g` between them; `(familyPicardFunctor p).map g.op` acts on classes
as `pullbackClass (familyMap p g)` by definition. No hypothesis on `p`, `S` or the test schemes is
used. Consumers: the proof of Kleiman's Thm 4.8 (p. 30), where `R = Z ×_P Z` is identified with a
linear system over `Z`, and the local sections of the Abel map on a Picard stratum, where
linear-system divisors over a chart of `Gr(E, k)` are transported to `X ×_S U`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

open Modules.Invertible Modules.Invertible.PullbackTensor.Local

namespace RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- If two classes on `X ×_S T` differ by a class pulled back from `T`, they have the same image in
`P_{X/S}(T)`. -/
theorem quotientProjection_app_eq_of_eq_add {T : Over S} {x y : PicardGroup (pullback p T.hom)}
    (n : PicardGroup T.left) (h : x = y + pullbackClass (pullback.snd p T.hom) n) :
    ((quotientProjection p).app (op T)).hom x = ((quotientProjection p).app (op T)).hom y := by
  subst h
  calc ((quotientProjection p).app (op T)).hom (y + pullbackClass (pullback.snd p T.hom) n)
      = ((quotientProjection p).app (op T)).hom y +
          ((quotientProjection p).app (op T)).hom (((basePullback p).app (op T)).hom n) :=
        map_add _ _ _
    _ = ((quotientProjection p).app (op T)).hom y := by
        rw [quotientProjection_basePullback_apply, add_zero]

/-- **Classes with the same image in `P_{X/S}(T)`** (Kleiman, arXiv:math/0504020v1, Def. 2.2,
p. 17): two classes on `X ×_S T` have the same image in `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)` if
and only if they differ by a class pulled back from `T`. -/
theorem quotientProjection_app_eq_iff {T : Over S} (x y : PicardGroup (pullback p T.hom)) :
    ((quotientProjection p).app (op T)).hom x = ((quotientProjection p).app (op T)).hom y ↔
      ∃ n : PicardGroup T.left, x = y + pullbackClass (pullback.snd p T.hom) n := by
  refine ⟨fun h => ?_, fun ⟨n, h⟩ => quotientProjection_app_eq_of_eq_add p n h⟩
  have h' : (QuotientAddGroup.mk x : (familyPicardFunctor p).obj (op T) ⧸ baseImage p (op T)) =
      QuotientAddGroup.mk y := h
  obtain ⟨n, hn⟩ : ∃ n : PicardGroup T.left, pullbackClass (pullback.snd p T.hom) n = -x + y :=
    QuotientAddGroup.eq.mp h'
  refine ⟨-n, ?_⟩
  rw [pullbackClass_neg, hn]
  abel

end RelativePicard

namespace LinearSystem

open RelativePicard

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)

/-- **Linear-system divisors through their Abel classes** (Kleiman, arXiv:math/0504020v1,
Def. 3.12, p. 25): a relative effective Cartier divisor `D ⊆ X ×_S T` over `T` is a divisor of
the linear system `LinSys_{L/X/S}(T)` if and only if its Abel class `−[I_D] = [𝒪(D)]` is
`g_T^*[L] + p_T^* n` for some class `n` on `T`. -/
theorem isLinearSystemDivisor_iff_exists_abelClass_eq {T : Over S}
    {D : (Limits.pullback p T.hom).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (Limits.pullback.snd p T.hom)) :
    IsLinearSystemDivisor p L T D ↔ ∃ n : PicardGroup T.left,
      abelClass p D hD = pullbackClass (Limits.pullback.fst p T.hom) (classOf X L) +
        pullbackClass (Limits.pullback.snd p T.hom) n := by
  have key : ∀ N : LineBundle T.left,
      Nonempty (Hom.idealModule D.subschemeι ≅
        (show (Limits.pullback p T.hom).Modules from Modules.tensorSheaf (Limits.pullback p T.hom)
          ((Modules.pullback (Limits.pullback.snd p T.hom)).obj N.val)
          ((Modules.pullback (Limits.pullback.fst p T.hom)).obj (dualLineBundle X L).val))) ↔
        abelClass p D hD = pullbackClass (Limits.pullback.fst p T.hom) (classOf X L) +
          pullbackClass (Limits.pullback.snd p T.hom) (-classOf T.left N) := by
    intro N
    have h : pullbackClass (Limits.pullback.fst p T.hom) (classOf X L) +
        pullbackClass (Limits.pullback.snd p T.hom) (-classOf T.left N) =
          -classOf _ (tensorLineBundle _ (pullbackLineBundle (Limits.pullback.snd p T.hom) N)
            (pullbackLineBundle (Limits.pullback.fst p T.hom) (dualLineBundle X L))) := by
      rw [classOf_tensor, ← pullbackClass_classOf, ← pullbackClass_classOf, classOf_dual,
        pullbackClass_neg, pullbackClass_neg]
      abel
    rw [h, abelClass, neg_inj]
    exact (class_eq_iff _ hD.idealLineBundle
      (tensorLineBundle _ (pullbackLineBundle (Limits.pullback.snd p T.hom) N)
        (pullbackLineBundle (Limits.pullback.fst p T.hom) (dualLineBundle X L)))).symm
  constructor
  · rintro ⟨_, N, hN⟩
    exact ⟨-classOf T.left N, (key N).mp hN⟩
  · rintro ⟨n, hn⟩
    obtain ⟨N, hN⟩ := Quotient.exists_rep (-n)
    refine ⟨hD, N, (key N).mpr ?_⟩
    have hNn : -classOf T.left N = n := neg_eq_iff_eq_neg.mpr hN
    rw [hNn]
    exact hn

/-- **Linear-system divisors through their Abel classes, subgroup form**: a relative effective
Cartier divisor `D ⊆ X ×_S T` over `T` is a divisor of `LinSys_{L/X/S}(T)` if and only if
`abelClass D − g_T^*[L]` lies in the image of `Pic(T)` (Kleiman, arXiv:math/0504020v1, Def. 3.12,
p. 25). -/
theorem isLinearSystemDivisor_iff_abelClass_sub_mem_baseImage {T : Over S}
    {D : (Limits.pullback p T.hom).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (Limits.pullback.snd p T.hom)) :
    IsLinearSystemDivisor p L T D ↔
      abelClass p D hD - pullbackClass (Limits.pullback.fst p T.hom) (classOf X L) ∈
        baseImage p (op T) := by
  rw [isLinearSystemDivisor_iff_exists_abelClass_eq p L hD]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change pullbackClass (Limits.pullback.snd p T.hom) n =
      abelClass p D hD - pullbackClass (Limits.pullback.fst p T.hom) (classOf X L)
    rw [hn]
    abel
  · intro h
    obtain ⟨n, hn⟩ : ∃ n : PicardGroup T.left, pullbackClass (Limits.pullback.snd p T.hom) n =
        abelClass p D hD - pullbackClass (Limits.pullback.fst p T.hom) (classOf X L) := h
    refine ⟨n, ?_⟩
    rw [hn]
    abel

/-- **The fppf Abel class of a linear-system divisor**: for a divisor `D` of `LinSys_{L/X/S}(T)`,
the class of `𝒪_{X_T}(D)` in `Pic_{X/S,(fppf)}(T)` is the class of `g_T^* L`, since the two differ
by a class pulled back from `T`. -/
theorem fppfAbelClass_eq_of_isLinearSystemDivisor {T : Over S}
    {D : (Limits.pullback p T.hom).IdealSheafData} (hD : IsLinearSystemDivisor p L T D) :
    fppfAbelClass p D hD.1 =
      (quotientProjection p ≫ toFppfPicardSheaf p).app (op T)
        (pullbackClass (Limits.pullback.fst p T.hom) (classOf X L)) := by
  obtain ⟨n, hn⟩ := (isLinearSystemDivisor_iff_exists_abelClass_eq p L hD.1).mp hD
  exact congrArg (fun x => (toFppfPicardSheaf p).app (op T) x)
    (quotientProjection_app_eq_of_eq_add p n hn)

end LinearSystem

namespace RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S)

section IsoPullback

open LinearSystem

variable {U V : Over S} (g : U ⟶ V)

/-- The square of the comparison `X ×_S U ≅ X_V ×_V U` over `𝟙 U` is cartesian. -/
theorem isPullback_isoPullback_hom :
    IsPullback (isPullback_familyMap p g).isoPullback.hom (pullback.snd p U.hom)
      (pullback.snd (pullback.snd p V.hom) g.left) (𝟙 U.left) :=
  IsPullback.of_horiz_isIso ⟨by rw [IsPullback.isoPullback_hom_snd, Category.comp_id]⟩

/-- The square of the comparison `X_V ×_V U ≅ X ×_S U` over `𝟙 U` is cartesian. -/
theorem isPullback_isoPullback_inv :
    IsPullback (isPullback_familyMap p g).isoPullback.inv
      (pullback.snd (pullback.snd p V.hom) g.left) (pullback.snd p U.hom) (𝟙 U.left) :=
  IsPullback.of_horiz_isIso ⟨by rw [IsPullback.isoPullback_inv_snd, Category.comp_id]⟩

/-- **Transport of relative effective Cartier divisors to `X ×_S U`**: for `g : U ⟶ V` over `S`,
the pullback of a relative effective Cartier divisor of `X_V ×_V U ⟶ U` along the comparison
`X ×_S U ≅ X_V ×_V U` is a relative effective Cartier divisor of `X ×_S U ⟶ U`. -/
theorem isRelativeEffectiveCartier_comap_isoPullback_hom
    {D : (pullback (pullback.snd p V.hom) g.left).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι
      (pullback.snd (pullback.snd p V.hom) g.left)) :
    Hom.IsRelativeEffectiveCartier (D.comap (isPullback_familyMap p g).isoPullback.hom).subschemeι
      (pullback.snd p U.hom) :=
  hD.of_isPullback (isPullback_isoPullback_hom p g) (D.isPullback_subschemeMap_comap _)

/-- **Transport of relative effective Cartier divisors to `X_V ×_V U`**: the inverse direction of
`isRelativeEffectiveCartier_comap_isoPullback_hom`. -/
theorem isRelativeEffectiveCartier_comap_isoPullback_inv
    {D : (pullback p U.hom).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd p U.hom)) :
    Hom.IsRelativeEffectiveCartier (D.comap (isPullback_familyMap p g).isoPullback.inv).subschemeι
      (pullback.snd (pullback.snd p V.hom) g.left) :=
  hD.of_isPullback (isPullback_isoPullback_inv p g) (D.isPullback_subschemeMap_comap _)

/-- Pulling a closed subscheme of `X ×_S U` back to `X_V ×_V U` and then to `X ×_S U` returns
it. -/
theorem comap_isoPullback_inv_comap_hom (D : (pullback p U.hom).IdealSheafData) :
    (D.comap (isPullback_familyMap p g).isoPullback.inv).comap
      (isPullback_familyMap p g).isoPullback.hom = D := by
  rw [← IdealSheafData.comap_comp, Iso.hom_inv_id, IdealSheafData.comap_id]

/-- Pulling a closed subscheme of `X_V ×_V U` back to `X ×_S U` and then to `X_V ×_V U` returns
it. -/
theorem comap_isoPullback_hom_comap_inv
    (D : (pullback (pullback.snd p V.hom) g.left).IdealSheafData) :
    (D.comap (isPullback_familyMap p g).isoPullback.hom).comap
      (isPullback_familyMap p g).isoPullback.inv = D := by
  rw [← IdealSheafData.comap_comp, Iso.inv_hom_id, IdealSheafData.comap_id]

/-- **Transport of Abel classes to `X ×_S U`**: the Abel class of the transported divisor is the
pullback of the Abel class along the comparison `X ×_S U ≅ X_V ×_V U`. -/
theorem abelClass_comap_isoPullback_hom
    {D : (pullback (pullback.snd p V.hom) g.left).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι
      (pullback.snd (pullback.snd p V.hom) g.left)) :
    abelClass p (T := U) (D.comap (isPullback_familyMap p g).isoPullback.hom)
        (isRelativeEffectiveCartier_comap_isoPullback_hom p g hD) =
      pullbackClass (isPullback_familyMap p g).isoPullback.hom
        (abelClass (pullback.snd p V.hom) (T := Over.mk g.left) D hD) := by
  have h := hD.pullbackClass_classOf_idealLineBundle (isPullback_isoPullback_hom p g)
    (D.isPullback_subschemeMap_comap _)
  rw [abelClass, abelClass, pullbackClass_neg]
  exact congrArg Neg.neg h.symm

/-- The comparison `X ×_S U ≅ X_V ×_V U` followed by the projection to `X_V` is the base-change
map `familyMap p g` of the family, the map along which `familyPicardFunctor p` pulls classes
back. -/
theorem pullbackClass_isoPullback_hom_pullbackClass_fst (a : PicardGroup (pullback p V.hom)) :
    pullbackClass (isPullback_familyMap p g).isoPullback.hom
        (pullbackClass (pullback.fst (pullback.snd p V.hom) g.left) a) =
      pullbackClass (familyMap p g) a := by
  rw [← pullbackClass_comp, IsPullback.isoPullback_hom_fst]

/-- **The comparison identifies classes pulled back from `U`**: a class on `X_V ×_V U` is pulled
back from `U` if and only if its pullback to `X ×_S U` is. -/
theorem pullbackClass_isoPullback_hom_mem_baseImage_iff
    (x : PicardGroup (pullback (pullback.snd p V.hom) g.left)) :
    pullbackClass (isPullback_familyMap p g).isoPullback.hom x ∈ baseImage p (op U) ↔
      x ∈ baseImage (pullback.snd p V.hom) (op (Over.mk g.left)) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ : ∃ n : PicardGroup U.left, pullbackClass (pullback.snd p U.hom) n =
        pullbackClass (isPullback_familyMap p g).isoPullback.hom x := h
    have hx : pullbackClass (pullback.snd (pullback.snd p V.hom) g.left) n = x := by
      rw [← IsPullback.isoPullback_inv_snd (isPullback_familyMap p g), pullbackClass_comp, hn,
        ← pullbackClass_comp, Iso.inv_hom_id, pullbackClass_id]
    exact ⟨n, hx⟩
  · intro h
    obtain ⟨n, hn⟩ : ∃ n : PicardGroup U.left,
        pullbackClass (pullback.snd (pullback.snd p V.hom) g.left) n = x := h
    refine ⟨n, ?_⟩
    change pullbackClass (pullback.snd p U.hom) n =
      pullbackClass (isPullback_familyMap p g).isoPullback.hom x
    rw [← hn, ← pullbackClass_comp, IsPullback.isoPullback_hom_snd]

end IsoPullback

end RelativePicard

namespace LinearSystem

open RelativePicard

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **Linear-system divisors over `V`, transported to `X ×_S U`**: for `g : U ⟶ V` over `S`, a
line bundle `L` on `X_V = X ×_S V` and a relative effective Cartier divisor `D` of
`X_V ×_V U ⟶ U`, `D` lies in `LinSys_{L/X_V/V}(U)` if and only if the Abel class of its
transport to `X ×_S U` differs from `g^*[L]` by a class pulled back from `U`. -/
theorem isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage
    {U V : Over S} (g : U ⟶ V) (L : LineBundle (pullback p V.hom))
    {D : (pullback (pullback.snd p V.hom) g.left).IdealSheafData}
    (hD : Hom.IsRelativeEffectiveCartier D.subschemeι
      (pullback.snd (pullback.snd p V.hom) g.left)) :
    IsLinearSystemDivisor (pullback.snd p V.hom) L (Over.mk g.left) D ↔
      abelClass p (T := U) (D.comap (isPullback_familyMap p g).isoPullback.hom)
          (isRelativeEffectiveCartier_comap_isoPullback_hom p g hD) -
        pullbackClass (familyMap p g) (classOf _ L) ∈ baseImage p (op U) := by
  have hsub : ∀ a b : PicardGroup (pullback (pullback.snd p V.hom) g.left),
      pullbackClass (isPullback_familyMap p g).isoPullback.hom (a - b) =
        pullbackClass (isPullback_familyMap p g).isoPullback.hom a -
          pullbackClass (isPullback_familyMap p g).isoPullback.hom b :=
    fun a b => map_sub (pullbackHom (isPullback_familyMap p g).isoPullback.hom) a b
  rw [isLinearSystemDivisor_iff_abelClass_sub_mem_baseImage (pullback.snd p V.hom) L
      (T := Over.mk g.left) hD,
    ← pullbackClass_isoPullback_hom_mem_baseImage_iff p g, abelClass_comap_isoPullback_hom p g hD,
    ← pullbackClass_isoPullback_hom_pullbackClass_fst p g, ← hsub]
  exact Iff.rfl

/-- **The fppf Abel class of a transported linear-system divisor**: for a divisor `D` of
`LinSys_{L/X_V/V}(U)`, the class of its transport to `X ×_S U` in `Pic_{X/S,(fppf)}(U)` is the
pullback along `g` of the class of `L`. -/
theorem fppfAbelClass_comap_isoPullback_hom_eq_of_isLinearSystemDivisor
    {U V : Over S} (g : U ⟶ V) (L : LineBundle (pullback p V.hom))
    {D : (pullback (pullback.snd p V.hom) g.left).IdealSheafData}
    (hD : IsLinearSystemDivisor (pullback.snd p V.hom) L (Over.mk g.left) D) :
    fppfAbelClass p (T := U) (D.comap (isPullback_familyMap p g).isoPullback.hom)
        (isRelativeEffectiveCartier_comap_isoPullback_hom p g hD.1) =
      (fppfPicardSheaf p).obj.map g.op
        ((quotientProjection p ≫ toFppfPicardSheaf p).app (op V) (classOf _ L)) := by
  obtain ⟨n, hn⟩ : ∃ n : PicardGroup U.left, pullbackClass (pullback.snd p U.hom) n =
      abelClass p (T := U) (D.comap (isPullback_familyMap p g).isoPullback.hom)
          (isRelativeEffectiveCartier_comap_isoPullback_hom p g hD.1) -
        pullbackClass (familyMap p g) (classOf _ L) :=
    (isLinearSystemDivisor_iff_abelClass_comap_isoPullback_hom_sub_mem_baseImage p g L hD.1).mp hD
  have hq := quotientProjection_app_eq_of_eq_add p n (eq_add_of_sub_eq' hn.symm)
  exact (congrArg (fun x => (toFppfPicardSheaf p).app (op U) x) hq).trans
    (NatTrans.naturality_apply (quotientProjection p ≫ toFppfPicardSheaf p) g.op (classOf _ L))

end LinearSystem

end AlgebraicGeometry.Scheme

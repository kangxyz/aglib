/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Descent.Pullback
public import Aglib.RingTheory.Descent.Ideal

/-!
# Faithfully flat descent of closed subschemes

Let `f : X ⟶ Y` be flat, surjective and quasi-compact, and let `Z` be an ideal sheaf on `X`
(a closed subscheme) whose two pullbacks to `X ×_Y X` agree. Then `Z` is the pullback of a unique
ideal sheaf on `Y`, namely its pushforward `Z.map f`, the ideal of the scheme-theoretic image of
`Z` in `Y`. This is Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
Lemma 6.7(2), which Nitsure attributes to SGA 1, Exposé VIII, Corollaire 1.9 (not checked here);
compare the Stacks Project, Tag 03I0 (Lemma 35.37.2: descent data of closed immersions relative to
an fpqc covering are effective). Faithful flatness is encoded as `Flat` plus `Surjective`, for a
single morphism; the covering families of Tag 03I0 are not treated here. Pullback of ideal sheaves
is Mathlib's `Scheme.IdealSheafData.comap`, the ideal of the schematic inverse image.

* `Scheme.IdealSheafData.comap_map_eq_self_of_flat_of_surjective`: `(Z.map f).comap f = Z`.
* `Scheme.IdealSheafData.existsUnique_comap_eq_of_flat_of_surjective`: the descended ideal sheaf
  exists and is unique.
* `Scheme.IdealSheafData.exists_comap_eq_iff_of_flat_of_surjective`: `Z` descends if and only if
  its two pullbacks to `X ×_Y X` agree.
* `isPullback_lift_ker_comp_of_flat_of_surjective`: the closed-immersion form; a closed immersion
  `i : T ⟶ X` with equal pullbacks is the base change of the scheme-theoretic image of `i ≫ f`,
  and the induced morphism to that image is flat, surjective and quasi-compact
  (`flat_surjective_quasiCompact_lift_ker_comp_of_flat_of_surjective`).
* `ker_eq_ker_comp_of_isPullback_of_flat_of_surjective`: any closed subscheme of `Y` with base
  change `i` is that scheme-theoretic image.

The proof reduces to the affine case through a finite affine cover of the preimage of an affine
open (the disjoint union is affine and faithfully flat over the base) and an affine open cover of
the target. The affine case is the ring statement `Ideal.map_comap_eq_self_of_isPushout`, applied
to the pushout square of global sections of `X ×_Y X`.

The coequalizer half of Lemma 6.7, that `f` is the coequalizer of the two projections
`X ×_Y X ⟶ X`, is Mathlib's `EffectiveEpi` instance for flat surjective quasi-compact morphisms
(`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`) together with
`CategoryTheory.isColimitCoforkOfEffectiveEpi`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The descent condition transfers along a commutative square: if the two pullbacks of `Z` to
`X ×_Y X` agree and `c ≫ f = f' ≫ h`, then the two pullbacks of `Z.comap c` to `X' ×_{Y'} X'`
agree. -/
lemma comap_comap_fst_eq_comap_comap_snd_of_comp_eq {X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : X' ⟶ X) (h : Y' ⟶ Y) (w : c ≫ f = f' ≫ h) {Z : X.IdealSheafData}
    (hZ : Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f)) :
    (Z.comap c).comap (pullback.fst f' f') = (Z.comap c).comap (pullback.snd f' f') := by
  have hw : (pullback.fst f' f' ≫ c) ≫ f = (pullback.snd f' f' ≫ c) ≫ f := by
    rw [Category.assoc, Category.assoc, w, pullback.condition_assoc]
  obtain ⟨g, h₁, h₂⟩ : ∃ g : pullback f' f' ⟶ pullback f f,
      pullback.fst f' f' ≫ c = g ≫ pullback.fst f f ∧
        pullback.snd f' f' ≫ c = g ≫ pullback.snd f f :=
    ⟨pullback.lift _ _ hw, (pullback.lift_fst _ _ _).symm, (pullback.lift_snd _ _ _).symm⟩
  rw [← comap_comp, ← comap_comp, h₁, h₂, comap_comp, comap_comp, hZ]

/-- The pullback of an ideal sheaf on `Y` has equal pullbacks to `X ×_Y X`. -/
lemma comap_comap_fst_eq_comap_comap_snd (f : X ⟶ Y) (Q : Y.IdealSheafData) :
    (Q.comap f).comap (pullback.fst f f) = (Q.comap f).comap (pullback.snd f f) := by
  rw [← comap_comp, ← comap_comp, pullback.condition]

/-- Affine case of faithfully flat descent of closed subschemes. -/
private lemma comap_map_eq_self_of_isAffine [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Flat f]
    [Surjective f] (Z : X.IdealSheafData)
    (hZ : Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f)) :
    (Z.map f).comap f = Z := by
  apply ext_of_isAffine
  rw [ideal_comap_top_of_isAffine, ideal_map_top_of_isAffine]
  refine Ideal.map_comap_eq_self_of_isPushout
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩)
    (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f f)) _ ?_
  rw [← ideal_comap_top_of_isAffine, ← ideal_comap_top_of_isAffine, hZ]

/-- Faithfully flat descent of closed subschemes over an affine target: the source is covered by
finitely many affine opens, whose disjoint union is affine and faithfully flat over `Y`. -/
private lemma comap_map_eq_self_of_isAffine_of_flat_of_surjective [IsAffine Y] (f : X ⟶ Y) [Flat f]
    [Surjective f] [QuasiCompact f] (Z : X.IdealSheafData)
    (hZ : Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f)) :
    (Z.map f).comap f = Z := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  let c : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ X := Sigma.desc (fun i ↦ 𝒰.f i)
  have : Surjective c := Surjective.sigmaDesc_of_union_range_eq_univ 𝒰.iUnion_range
  have key := comap_map_eq_self_of_isAffine (c ≫ f) (Z.comap c)
    (comap_comap_fst_eq_comap_comap_snd_of_comp_eq c (𝟙 Y) (by simp) hZ)
  rw [map_comp, map_comap_of_flat_of_surjective, comap_comp] at key
  exact comap_injective_of_flat_of_surjective c key

/-- **Faithfully flat descent of closed subschemes** (Nitsure, arXiv:math/0504590v1,
Lemma 6.7(2)). If `f` is flat, surjective and quasi-compact and the two pullbacks of the ideal
sheaf `Z` to `X ×_Y X` agree, then `Z` is the pullback of its pushforward `Z.map f`. -/
theorem comap_map_eq_self_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f]
    [QuasiCompact f] (Z : X.IdealSheafData)
    (hZ : Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f)) :
    (Z.map f).comap f = Z := by
  let 𝒱 := Y.affineCover
  refine ext_of_comap_eq (fun i ↦ pullback.fst f (𝒱.f i)) ?_ fun i ↦ ?_
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, y, hy⟩ := 𝒱.exists_eq (f x)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    exact Set.mem_iUnion.mpr ⟨i, z, hz⟩
  · let c := pullback.fst f (𝒱.f i)
    have key := comap_map_eq_self_of_isAffine_of_flat_of_surjective (pullback.snd f (𝒱.f i))
      (Z.comap c) (comap_comap_fst_eq_comap_comap_snd_of_comp_eq c (𝒱.f i) pullback.condition hZ)
    have hsq : IsPullback ((Z.comap c).subschemeι ≫ pullback.snd f (𝒱.f i))
        ((Z.comapIso c).hom ≫ pullback.snd c Z.subschemeι) (𝒱.f i) (Z.subschemeι ≫ f) := by
      refine IsPullback.paste_horiz ?_ (IsPullback.of_hasPullback f (𝒱.f i)).flip
      refine IsPullback.of_iso_pullback ⟨?_⟩ (Z.comapIso c) (comapIso_hom_fst Z c) rfl
      rw [← comapIso_hom_fst, Category.assoc, pullback.condition, Category.assoc]
    have hmap : (Z.comap c).map (pullback.snd f (𝒱.f i)) = (Z.map f).comap (𝒱.f i) :=
      Scheme.Hom.ker_eq_comap_of_isPullback_of_isOpenImmersion hsq
    rw [hmap, ← comap_comp, ← pullback.condition, comap_comp] at key
    exact key

/-- **Faithfully flat descent of closed subschemes**, existence and uniqueness: an ideal sheaf on
`X` with equal pullbacks to `X ×_Y X` is the pullback of a unique ideal sheaf on `Y`. -/
theorem existsUnique_comap_eq_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f]
    [QuasiCompact f] (Z : X.IdealSheafData)
    (hZ : Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f)) :
    ∃! Q : Y.IdealSheafData, Q.comap f = Z :=
  ⟨Z.map f, comap_map_eq_self_of_flat_of_surjective f Z hZ, fun Q hQ ↦ by
    rw [← hQ, map_comap_of_flat_of_surjective]⟩

/-- Along a flat, surjective and quasi-compact morphism, an ideal sheaf on `X` is pulled back from
`Y` if and only if its two pullbacks to `X ×_Y X` agree. -/
theorem exists_comap_eq_iff_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f]
    [QuasiCompact f] (Z : X.IdealSheafData) :
    (∃ Q : Y.IdealSheafData, Q.comap f = Z) ↔
      Z.comap (pullback.fst f f) = Z.comap (pullback.snd f f) := by
  refine ⟨?_, fun hZ ↦ ⟨_, comap_map_eq_self_of_flat_of_surjective f Z hZ⟩⟩
  rintro ⟨Q, rfl⟩
  exact comap_comap_fst_eq_comap_comap_snd f Q

end Scheme.IdealSheafData

open Scheme.IdealSheafData in
/-- **Faithfully flat descent of closed subschemes**, closed-immersion form (Nitsure,
arXiv:math/0504590v1, Lemma 6.7(2)). Let `f` be flat, surjective and quasi-compact and let
`i : T ⟶ X` be a closed immersion whose two pullbacks to `X ×_Y X` agree. Then the square formed by
`i`, `f`, the scheme-theoretic image `(i ≫ f).ker` of `T` in `Y` and the induced morphism to it is
cartesian. -/
theorem isPullback_lift_ker_comp_of_flat_of_surjective {X Y T : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f] (i : T ⟶ X) [IsClosedImmersion i]
    (hi : i.ker.comap (pullback.fst f f) = i.ker.comap (pullback.snd f f)) :
    IsPullback i
      (IsClosedImmersion.lift (i ≫ f).ker.subschemeι (i ≫ f) (ker_subschemeι _).le) f
      (i ≫ f).ker.subschemeι := by
  refine isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ _).symm ?_
  rw [ker_subschemeι, Scheme.Hom.ker_comp]
  exact comap_map_eq_self_of_flat_of_surjective f i.ker hi

/-- Uniqueness in the closed-immersion form of descent: along a flat surjective `f`, a closed
subscheme `j : Q ⟶ Y` whose base change along `f` is `i : T ⟶ X` is the scheme-theoretic image of
`i ≫ f`. -/
theorem ker_eq_ker_comp_of_isPullback_of_flat_of_surjective {X Y T Q : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] {i : T ⟶ X} {q : T ⟶ Q} {j : Q ⟶ Y} [IsClosedImmersion j]
    (H : IsPullback i q f j) : j.ker = (i ≫ f).ker := by
  have h : j.ker.comap f = i.ker := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion j f, ← H.isoPullback_hom_fst,
      Scheme.Hom.ker_comp_of_isIso]
  rw [Scheme.Hom.ker_comp, ← h, Scheme.IdealSheafData.map_comap_of_flat_of_surjective]

/-- In the closed-immersion form of descent, the induced morphism to the scheme-theoretic image is
flat, surjective and quasi-compact, by base change from `f`. -/
theorem flat_surjective_quasiCompact_lift_ker_comp_of_flat_of_surjective {X Y T : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] (i : T ⟶ X) [IsClosedImmersion i]
    (hi : i.ker.comap (pullback.fst f f) = i.ker.comap (pullback.snd f f)) :
    Flat (IsClosedImmersion.lift (i ≫ f).ker.subschemeι (i ≫ f)
        (Scheme.IdealSheafData.ker_subschemeι _).le) ∧
      Surjective (IsClosedImmersion.lift (i ≫ f).ker.subschemeι (i ≫ f)
        (Scheme.IdealSheafData.ker_subschemeι _).le) ∧
      QuasiCompact (IsClosedImmersion.lift (i ≫ f).ker.subschemeι (i ≫ f)
        (Scheme.IdealSheafData.ker_subschemeι _).le) := by
  have H := isPullback_lift_ker_comp_of_flat_of_surjective f i hi
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) H ‹_›,
    MorphismProperty.of_isPullback (P := @Surjective) H ‹_›,
    MorphismProperty.of_isPullback (P := @QuasiCompact) H ‹_›⟩

end AlgebraicGeometry

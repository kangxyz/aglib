/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Aglib.CategoryTheory.ObjectProperty.Yoneda
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Limits.EpiMono

/-!
# Yoneda on locally Noetherian test schemes

Hilbert, Quot and Picard functors are represented on locally Noetherian test schemes only
(`Scheme.LocallyNoetherianOver`). Equalities, isomorphisms and monomorphisms between locally
Noetherian schemes can still be tested on such points, by the Yoneda lemma in the full subcategory
of locally Noetherian schemes.

* **Isomorphisms.** A morphism of locally Noetherian schemes that is bijective on `T`-points for
  every locally Noetherian scheme `T` is an isomorphism
  (`Scheme.isIso_of_locallyNoetherian_yoneda_map_bijective`); over a base `S`, with `T`-points over
  `S` for `T : LocallyNoetherianOver S`
  (`Scheme.LocallyNoetherianOver.isIso_of_yoneda_map_bijective`, and `isIso_left_…` for the
  underlying morphism of schemes).
* **Monomorphisms.** A morphism `f : X ⟶ Y` that is injective on locally Noetherian points is a
  monomorphism of schemes, provided `X ×_Y X` is locally Noetherian: the two projections of
  `X ×_Y X` agree, and the diagonal is an isomorphism
  (`Scheme.fst_eq_snd_of_locallyNoetherian_yoneda_map_injective`,
  `Scheme.isIso_diagonal_of_locallyNoetherian_yoneda_map_injective`,
  `Scheme.mono_of_locallyNoetherian_yoneda_map_injective`). The condition holds if `Y` is locally
  Noetherian and `f` is locally of finite type (`…_of_locallyOfFiniteType`); a proper such `f` is
  then a closed immersion
  (`Scheme.isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective`, Nitsure's
  exercise on p. 33). Over a base `S`, the same holds for injectivity on `T`-points over `S`
  (`Scheme.LocallyNoetherianOver.mono_left_of_yoneda_map_injective`).
* **Closed subschemes.** A morphism factors through a closed immersion `i` exactly when its kernel
  contains `ker i` (`Scheme.Hom.exists_lift_iff_ker_le_ker`, from Mathlib's
  `IsClosedImmersion.lift`), and through the closed subscheme of an ideal sheaf `I` exactly when it
  contains `I` (`Scheme.IdealSheafData.exists_lift_subschemeι_iff_le_ker`); it factors through the
  pullback `I.comap f` exactly when its composite with `f` factors through `I`
  (`Scheme.IdealSheafData.exists_lift_comap_subschemeι_iff`). Hence two closed subschemes of a
  locally Noetherian scheme with the same locally Noetherian points are equal
  (`Scheme.Hom.ker_eq_of_locallyNoetherian_exists_lift_iff`,
  `Scheme.IdealSheafData.eq_of_locallyNoetherian_exists_lift_iff`): the closed subschemes are
  themselves locally Noetherian test schemes. For pullbacks along `q₁ q₂ : X ⟶ Y` this gives
  `Z.comap q₁ = Z.comap q₂` from a comparison of points
  (`Scheme.IdealSheafData.comap_eq_comap_of_locallyNoetherian_exists_lift_iff`).

The categorical cores are `ObjectProperty.isIso_of_yoneda_map_bijective` and
`ObjectProperty.mono_of_yoneda_map_injective` (`Aglib.CategoryTheory.ObjectProperty.Yoneda`), the
Yoneda lemma (Stacks, Lemma 4.3.5, Tag 001P) in the full subcategory of locally Noetherian schemes,
and Stacks, Lemma 26.23.2 (Tag 01L3: a morphism of schemes is a monomorphism if and only if its
diagonal is an isomorphism). The factorization criterion is the scheme form of Stacks, Lemma 26.4.6
(Tag 01HP), stated there for locally ringed spaces; closed immersions into a locally Noetherian
scheme have locally Noetherian source by Stacks, Lemma 29.15.6 (Tag 01T6).

These tests replace the quantification over all test schemes in Nitsure, *Construction of Hilbert
and Quot schemes*, arXiv:math/0504590v1, proof of Theorem 6.8: there `(***)` (p. 34), the equality
`p₁⁻¹Γ_φ = p₂⁻¹Γ_φ` (pp. 34–35) and the isomorphism `R ≅ X ×_Q X` (p. 35, (iii)) are checked on
`T`-points for all `S`-schemes `T`, while the Hilbert scheme represents its functor on locally
Noetherian schemes only (§1, p. 2).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-! ### Isomorphisms -/

/-- **Locally Noetherian Yoneda for isomorphisms**: a morphism of locally Noetherian schemes that is
bijective on `T`-points for every locally Noetherian scheme `T` is an isomorphism. -/
theorem isIso_of_locallyNoetherian_yoneda_map_bijective {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Bijective fun x : T ⟶ X => x ≫ f) :
    IsIso f :=
  ObjectProperty.isIso_of_yoneda_map_bijective (fun T : Scheme.{u} => IsLocallyNoetherian T)
    (show IsLocallyNoetherian X from inferInstance) (show IsLocallyNoetherian Y from inferInstance)
    f fun T hT => @hf T hT

namespace LocallyNoetherianOver

variable {S : Scheme.{u}}

/-- **Locally Noetherian Yoneda for isomorphisms over a base**: a morphism `f : X ⟶ Y` of locally
Noetherian schemes over `S` that is bijective on `T`-points over `S` for every locally Noetherian
`T` over `S` is an isomorphism over `S`. -/
theorem isIso_of_yoneda_map_bijective {X Y : Over S} [IsLocallyNoetherian X.left]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y)
    (hf : ∀ T : LocallyNoetherianOver S, Function.Bijective fun x : T.obj ⟶ X => x ≫ f) :
    IsIso f :=
  ObjectProperty.isIso_of_yoneda_map_bijective (locallyNoetherianOver S)
    (show IsLocallyNoetherian X.left from inferInstance)
    (show IsLocallyNoetherian Y.left from inferInstance) f fun T hT => hf ⟨T, hT⟩

/-- The underlying morphism of schemes of a morphism of locally Noetherian schemes over `S` that is
bijective on locally Noetherian `T`-points over `S` is an isomorphism. -/
theorem isIso_left_of_yoneda_map_bijective {X Y : Over S} [IsLocallyNoetherian X.left]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y)
    (hf : ∀ T : LocallyNoetherianOver S, Function.Bijective fun x : T.obj ⟶ X => x ≫ f) :
    IsIso f.left :=
  have := isIso_of_yoneda_map_bijective f hf
  (Over.forget S).map_isIso f

end LocallyNoetherianOver

/-! ### Monomorphisms -/

/-- **Injective on locally Noetherian points, the projections agree**: if `f : X ⟶ Y` is injective
on `T`-points for every locally Noetherian `T`, and `X ×_Y X` is locally Noetherian, the two
projections `X ×_Y X ⟶ X` are equal. -/
theorem fst_eq_snd_of_locallyNoetherian_yoneda_map_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian (pullback f f)]
    (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Injective fun x : T ⟶ X => x ≫ f) :
    pullback.fst f f = pullback.snd f f :=
  ObjectProperty.fst_eq_snd_of_yoneda_map_injective
    (P := fun T : Scheme.{u} => IsLocallyNoetherian T) f
    (show IsLocallyNoetherian (pullback f f) from inferInstance) fun T hT => @hf T hT

/-- **The diagonal from locally Noetherian points**: if `f : X ⟶ Y` is injective on `T`-points for
every locally Noetherian `T`, and `X ×_Y X` is locally Noetherian, the diagonal
`X ⟶ X ×_Y X` is an isomorphism. -/
theorem isIso_diagonal_of_locallyNoetherian_yoneda_map_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian (pullback f f)]
    (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Injective fun x : T ⟶ X => x ≫ f) :
    IsIso (pullback.diagonal f) :=
  ObjectProperty.isIso_diagonal_of_yoneda_map_injective
    (P := fun T : Scheme.{u} => IsLocallyNoetherian T) f
    (show IsLocallyNoetherian (pullback f f) from inferInstance) fun T hT => @hf T hT

/-- **Locally Noetherian Yoneda for monomorphisms**, through the diagonal: a morphism
`f : X ⟶ Y` that is injective on `T`-points for every locally Noetherian `T` is a monomorphism of
schemes, provided `X ×_Y X` is locally Noetherian. -/
theorem mono_of_locallyNoetherian_yoneda_map_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian (pullback f f)]
    (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Injective fun x : T ⟶ X => x ≫ f) :
    Mono f :=
  (pullback.isIso_diagonal_iff f).mp (isIso_diagonal_of_locallyNoetherian_yoneda_map_injective f hf)

/-- **Locally Noetherian Yoneda for monomorphisms of finite type**: over a locally Noetherian `Y`,
a morphism `f : X ⟶ Y` locally of finite type that is injective on `T`-points for every locally
Noetherian `T` is a monomorphism of schemes (`X ×_Y X` is then locally Noetherian). -/
theorem mono_of_locallyNoetherian_yoneda_map_injective_of_locallyOfFiniteType {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Injective fun x : T ⟶ X => x ≫ f) :
    Mono f :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  mono_of_locallyNoetherian_yoneda_map_injective f hf

/-- **Proper and injective on locally Noetherian points implies closed immersion**: a proper
morphism into a locally Noetherian scheme that is injective on `T`-points for every locally
Noetherian `T` is a closed immersion (a proper monomorphism, Mathlib's
`IsClosedImmersion.iff_isProper_and_mono`; Stacks, Lemma 41.7.2, Tag 04XV). This is the exercise
in step 1 of Nitsure's proof of Theorem 6.8 (p. 33). -/
theorem isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Injective fun x : T ⟶ X => x ≫ f) :
    IsClosedImmersion f :=
  (IsClosedImmersion.iff_isProper_and_mono f).mpr
    ⟨inferInstance, mono_of_locallyNoetherian_yoneda_map_injective_of_locallyOfFiniteType f hf⟩

/-- **Locally Noetherian Yoneda for monomorphisms over a base**: if `f : X ⟶ Y` over `S` is
injective on `T`-points over `S` for every locally Noetherian `T` over `S`, and `X ×_Y X` is
locally Noetherian, the underlying morphism of schemes is a monomorphism. The test object is
`X ×_Y X` over `S` with its two projections. -/
theorem LocallyNoetherianOver.mono_left_of_yoneda_map_injective {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [IsLocallyNoetherian (pullback f.left f.left)]
    (hf : ∀ T : LocallyNoetherianOver S, Function.Injective fun x : T.obj ⟶ X => x ≫ f) :
    Mono f.left := by
  let T : LocallyNoetherianOver S :=
    ⟨Over.mk (pullback.fst f.left f.left ≫ X.hom),
      show IsLocallyNoetherian (pullback f.left f.left) from inferInstance⟩
  have hsnd : pullback.snd f.left f.left ≫ X.hom = pullback.fst f.left f.left ≫ X.hom := by
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, pullback.condition]
  let a : T.obj ⟶ X := Over.homMk (pullback.fst f.left f.left) rfl
  let b : T.obj ⟶ X := Over.homMk (pullback.snd f.left f.left) hsnd
  have hab : a = b := hf T (show a ≫ f = b ≫ f from Over.OverMorphism.ext (by
    change pullback.fst f.left f.left ≫ f.left = pullback.snd f.left f.left ≫ f.left
    exact pullback.condition))
  have h : pullback.fst f.left f.left = pullback.snd f.left f.left :=
    congrArg CommaMorphism.left hab
  exact (CategoryTheory.mono_iff_fst_eq_snd (pullbackIsPullback f.left f.left)).mpr h

/-- **Locally Noetherian Yoneda for monomorphisms in `Over S`**: the same conclusion for the
morphism over `S`. -/
theorem LocallyNoetherianOver.mono_of_yoneda_map_injective {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [IsLocallyNoetherian (pullback f.left f.left)]
    (hf : ∀ T : LocallyNoetherianOver S, Function.Injective fun x : T.obj ⟶ X => x ≫ f) :
    Mono f :=
  have := mono_left_of_yoneda_map_injective f hf
  Over.mono_of_mono_left f

/-! ### Closed subschemes -/

/-- **The universal property of a closed immersion**: a morphism `g` factors through a closed
immersion `i` if and only if `ker i ≤ ker g` (Mathlib's `IsClosedImmersion.lift`). -/
theorem Hom.exists_lift_iff_ker_le_ker {X Z T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (g : T ⟶ X) : (∃ a : T ⟶ Z, a ≫ i = g) ↔ i.ker ≤ g.ker := by
  constructor
  · rintro ⟨a, rfl⟩
    exact Hom.le_ker_comp a i
  · intro h
    exact ⟨IsClosedImmersion.lift i g h, IsClosedImmersion.lift_fac i g h⟩

/-- A morphism `g` factors through the closed subscheme of an ideal sheaf `I` if and only if
`I ≤ ker g`. -/
theorem IdealSheafData.exists_lift_subschemeι_iff_le_ker {X T : Scheme.{u}}
    (I : X.IdealSheafData) (g : T ⟶ X) :
    (∃ a : T ⟶ I.subscheme, a ≫ I.subschemeι = g) ↔ I ≤ g.ker := by
  rw [Hom.exists_lift_iff_ker_le_ker, I.ker_subschemeι]

/-- **Points of a pulled-back closed subscheme**: `g : T ⟶ X` factors through the pullback
`I.comap f` of a closed subscheme `I` of `Y` along `f : X ⟶ Y` if and only if `g ≫ f` factors
through `I`. -/
theorem IdealSheafData.exists_lift_comap_subschemeι_iff {X Y T : Scheme.{u}}
    (I : Y.IdealSheafData) (f : X ⟶ Y) (g : T ⟶ X) :
    (∃ a : T ⟶ (I.comap f).subscheme, a ≫ (I.comap f).subschemeι = g) ↔
      ∃ b : T ⟶ I.subscheme, b ≫ I.subschemeι = g ≫ f := by
  rw [exists_lift_subschemeι_iff_le_ker, exists_lift_subschemeι_iff_le_ker, ← map_ker,
    le_map_iff_comap_le]

/-- **Closed immersions are determined by their locally Noetherian points**: two closed
immersions into a locally Noetherian scheme through which the same morphisms from locally
Noetherian schemes factor have the same kernel. Mathlib's `IsClosedImmersion.isIso_lift` then
identifies the two closed subschemes. -/
theorem Hom.ker_eq_of_locallyNoetherian_exists_lift_iff {X Z₁ Z₂ : Scheme.{u}}
    [IsLocallyNoetherian X] (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₁]
    [IsClosedImmersion i₂]
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ X),
      (∃ a : T ⟶ Z₁, a ≫ i₁ = g) ↔ ∃ b : T ⟶ Z₂, b ≫ i₂ = g) :
    i₁.ker = i₂.ker := by
  have : IsLocallyNoetherian Z₁ := LocallyOfFiniteType.isLocallyNoetherian i₁
  have : IsLocallyNoetherian Z₂ := LocallyOfFiniteType.isLocallyNoetherian i₂
  refine le_antisymm ?_ ?_
  · exact (Hom.exists_lift_iff_ker_le_ker i₁ i₂).mp ((h Z₂ i₂).mpr ⟨𝟙 _, Category.id_comp _⟩)
  · exact (Hom.exists_lift_iff_ker_le_ker i₂ i₁).mp ((h Z₁ i₁).mp ⟨𝟙 _, Category.id_comp _⟩)

/-- **Closed subschemes are determined by their locally Noetherian points**: two closed subschemes
of a locally Noetherian scheme through which the same morphisms from locally Noetherian schemes
factor are equal. -/
theorem IdealSheafData.eq_of_locallyNoetherian_exists_lift_iff {X : Scheme.{u}}
    [IsLocallyNoetherian X] {I J : X.IdealSheafData}
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ X),
      (∃ a : T ⟶ I.subscheme, a ≫ I.subschemeι = g) ↔
        ∃ b : T ⟶ J.subscheme, b ≫ J.subschemeι = g) :
    I = J := by
  rw [← I.ker_subschemeι, ← J.ker_subschemeι]
  exact Hom.ker_eq_of_locallyNoetherian_exists_lift_iff I.subschemeι J.subschemeι h

/-- **Pulled-back closed subschemes are compared on locally Noetherian points**: for a closed
subscheme `Z` of `Y` and `q₁ q₂ : X ⟶ Y` with `X` locally Noetherian, `Z.comap q₁ = Z.comap q₂`
as soon as, for every locally Noetherian `T` and `g : T ⟶ X`, `g ≫ q₁` factors through `Z` exactly
when `g ≫ q₂` does. This is the shape of the equality `p₁⁻¹Γ_φ = p₂⁻¹Γ_φ` in Nitsure's proof of
Theorem 6.8 (pp. 34–35). -/
theorem IdealSheafData.comap_eq_comap_of_locallyNoetherian_exists_lift_iff {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (Z : Y.IdealSheafData) (q₁ q₂ : X ⟶ Y)
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ X),
      (∃ a : T ⟶ Z.subscheme, a ≫ Z.subschemeι = g ≫ q₁) ↔
        ∃ b : T ⟶ Z.subscheme, b ≫ Z.subschemeι = g ≫ q₂) :
    Z.comap q₁ = Z.comap q₂ :=
  eq_of_locallyNoetherian_exists_lift_iff fun T _ g => by
    rw [exists_lift_comap_subschemeι_iff, exists_lift_comap_subschemeι_iff]
    exact h T g

end AlgebraicGeometry.Scheme

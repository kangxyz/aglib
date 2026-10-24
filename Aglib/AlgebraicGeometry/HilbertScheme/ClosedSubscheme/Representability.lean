/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.ClosedSubscheme.Generation
public import Aglib.AlgebraicGeometry.HilbertScheme.Representability
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.LocallyFree
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability

/-!
# The Hilbert scheme of a closed subscheme of projective space

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)`, `C ⊆ P^n_A` a closed subscheme and `Φ ∈ ℚ[X]`.
The **Hilbert subfunctor of `C`** (`closedHilbertSubfunctor ι Φ C`, a Mathlib `Subfunctor` of
`hilbertFunctor ι Φ` on all schemes `T` over `Spec A`) consists of the points `V` of `Hilb^Φ` of
`P^n_A` contained in `C_T`: the closed
subschemes `V ⊆ P^n_A ×_{Spec A} T`, flat over `T` with fibre Hilbert polynomials `Φ`, with
`C.comap p ≤ V` for `p : P^n_A ×_{Spec A} T ⟶ P^n_A` (inclusion of ideals, so `V ⊆ C_T`).
`C` need not be flat over `A`; `C_T` is the closed subscheme cut out by the image of
`p^* I_C ⟶ 𝒪`.

**Representability.** Fix a natural `r ≥ hilbertRegularityBound n Φ` and a family of global
sections `φ : 𝒪^J ⟶ 𝒪(r)` whose section pairing cuts out `C`
(`imageIdealData (sectionPairing ι r φ) = C`; such `φ` exist for all large `r`,
`exists_sectionPairing_imageIdealData_eq`). Over the Hilbert scheme `H = hilbertScheme ι n e A Φ r`
with universal family `W` (F13, `HilbertScheme/Representability`), the images of the sections of
`φ` in the finite locally free sheaf `π_* 𝒪_W(r)` of constant rank `k = ⌊Φ(r)⌋₊`
(`IsHilbertFamily.sheafHasRank_directImageSheaf`) form `closedHilbertSectionMap`, and its zero
scheme (`Scheme.Modules.Hom.zeroLocusIdeal`, `Modules/ZeroLocus/LocallyFree`) is the closed
subscheme `closedHilbertScheme ι n e A Φ r hr φ ⊆ H` (`closedHilbertSchemeι`, a closed
immersion; Noetherian, `isNoetherian_closedHilbertScheme`). It represents the Hilbert subfunctor
of `C` on locally Noetherian test schemes
(`locallyNoetherianClosedHilbertSubfunctorRepresentableBy`, for
`locallyNoetherianClosedHilbertSubfunctor`, the restriction through
`Scheme.LocalRepresentability.restrictSubfunctor`), with universal family the restriction of `W`
(`locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_id_coe`,
`universalClosedHilbertPoint`), compatibly with the representation of `Hilb^Φ`
(`locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_coe`).

The proof: `a : T ⟶ H` factors through the zero scheme iff the pulled-back sections vanish
(`Hom.exists_lift_zeroLocusSchemeι_iff`); by base change of `π_* 𝒪_W(r)`, invertible for Hilbert
families (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 25),
iff the images of the sections in `π_* 𝒪_{W_T}(r)` vanish
(`IsHilbertFamily.pullback_map_directImageSectionMap_eq_zero_iff`); and that holds iff
`W_T ⊆ C_T` (`comap_le_iff_directImageSectionMap_eq_zero`).

Source: Nitsure, arXiv:math/0504590v1, Theorem 5.3, p. 24 (Theorem 5.2 with `V` and `W`
trivial), for `X = C` and `E = 𝒪_C`, that is, Theorem 6.1, p. 28, for a closed `X = C`, on the
locally Noetherian test schemes of §1, pp. 3–4 (the functor `Hilb_{X/S}` on `Sch_S`). The route
is Nitsure's: Lemma 5.4 (ii), p. 25, in the proof of Theorem 5.2, applied to `𝒪_{P^n_A} ↠ 𝒪_C`,
makes `Hilb^Φ_C` the closed subfunctor of `Hilb^Φ` of `P^n_A` cut out by the vanishing of
`p^* I_C ⟶ 𝒪 ⟶ 𝒪_V`, that is, by `V ⊆ C_T`. Nitsure takes this vanishing scheme from
Remark 3.6, p. 17 (the linear scheme of Theorem 3.5, p. 16). Here it is the zero scheme of
`closedHilbertSectionMap` in the finite locally free `π_* 𝒪_W(r)`
(`Modules/ZeroLocus/LocallyFree`), a construction not in the source. Projectivity and
quasi-projectivity are not part of this file.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

section Functor

variable (ι : Type u) {A : Type u} [CommRing A]

/-- The points of the Hilbert functor of `P^n_A` contained in `C_T` are stable under pullback:
`C_{T'} = (C_T).comap b ≤ V.comap b` for the base-changed map `b`. -/
theorem comap_le_comap_baseChangeMap (C : (ProjectiveSpace A ι).IdealSheafData) {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (h : f ≫ g = g') {V : (pullback (toSpec A ι) g).IdealSheafData}
    (hV : C.comap (pullback.fst (toSpec A ι) g) ≤ V) :
    C.comap (pullback.fst (toSpec A ι) g') ≤ V.comap (baseChangeMap ι g g' f h) := by
  rw [← baseChangeMap_fst ι g g' f h, Scheme.IdealSheafData.comap_comp]
  exact Scheme.IdealSheafData.comap_mono _ hV

/-- **The Hilbert subfunctor of a closed subscheme** `C ⊆ P^n_A` (`Hilb^Φ_C`; Nitsure,
arXiv:math/0504590v1, §1, pp. 3–4, for `X = C`): the points `V` of `Hilb^Φ(T)` of `P^n_A` with
`C_T ≤ V` as ideal sheaves, that is, `V ⊆ C_T` as closed subschemes, for `C_T = C.comap p` and
`p : P^n_A ×_{Spec A} T ⟶ P^n_A`. It is defined on all schemes over `Spec A`; morphisms act by
pullback, as in `hilbertFunctor`. -/
def closedHilbertSubfunctor (Φ : ℚ[X]) (C : (ProjectiveSpace A ι).IdealSheafData) :
    Subfunctor (hilbertFunctor (A := A) ι Φ) where
  obj T := {Z | C.comap (pullback.fst (toSpec A ι) T.unop.hom) ≤ Z.1}
  map {T T'} f _ hZ :=
    comap_le_comap_baseChangeMap ι C T.unop.hom T'.unop.hom f.unop.left (Over.w f.unop) hZ

theorem mem_closedHilbertSubfunctor_obj (Φ : ℚ[X]) (C : (ProjectiveSpace A ι).IdealSheafData)
    {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (Z : (hilbertFunctor ι Φ).obj T) :
    Z ∈ (closedHilbertSubfunctor ι Φ C).obj T ↔
      C.comap (pullback.fst (toSpec A ι) T.unop.hom) ≤ Z.1 :=
  Iff.rfl

variable (A) in
/-- **`Hilb^Φ_C` on locally Noetherian test schemes**: the restriction of
`closedHilbertSubfunctor ι Φ C`, a subfunctor of `locallyNoetherianHilbertFunctor ι A Φ`. -/
abbrev locallyNoetherianClosedHilbertSubfunctor (Φ : ℚ[X])
    (C : (ProjectiveSpace A ι).IdealSheafData) :
    Subfunctor (locallyNoetherianHilbertFunctor ι A Φ) :=
  Scheme.LocalRepresentability.restrictSubfunctor (Scheme.locallyNoetherianOver _)
    (closedHilbertSubfunctor ι Φ C)

end Functor

section Scheme

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))

/-- The images of the sections of `φ` in `π_* 𝒪_W(r)` over the Hilbert scheme, for the universal
family `W`. -/
def closedHilbertSectionMap :
    SheafOfModules.free J ⟶
      directImageSheaf ι (hilbertSchemeOver ι n e A Φ r).obj.hom
        (universalHilbertFamily ι n e A Φ r) r :=
  directImageSectionMap ι (hilbertSchemeOver ι n e A Φ r).obj.hom r φ
    (universalHilbertFamily ι n e A Φ r)

include hr in
/-- `π_* 𝒪_W(r)` is finite locally free of constant rank `⌊Φ(r)⌋₊` over the Hilbert scheme. -/
theorem sheafHasRank_directImageSheaf_universalHilbertFamily :
    SheafHasRank (directImageSheaf ι (hilbertSchemeOver ι n e A Φ r).obj.hom
      (universalHilbertFamily ι n e A Φ r) r) ⌊Φ.eval (r : ℚ)⌋₊ :=
  haveI : IsLocallyNoetherian (hilbertSchemeOver ι n e A Φ r).obj.left :=
    (hilbertSchemeOver ι n e A Φ r).property
  (isHilbertFamily_universalHilbertFamily ι n e A Φ r).sheafHasRank_directImageSheaf ι n e r hr

/-- **The ideal of the Hilbert scheme of `C`** in the Hilbert scheme of `P^n_A`: the zero scheme
of `closedHilbertSectionMap` (`Scheme.Modules.Hom.zeroLocusIdeal`, rank `⌊Φ(r)⌋₊`). -/
def closedHilbertIdeal : (hilbertScheme ι n e A Φ r).IdealSheafData :=
  haveI : IsFiniteLocallyFree (hilbertScheme ι n e A Φ r)
      (directImageSheaf ι (hilbertSchemeOver ι n e A Φ r).obj.hom
        (universalHilbertFamily ι n e A Φ r) r) :=
    (sheafHasRank_directImageSheaf_universalHilbertFamily ι n e A Φ r hr).isFiniteLocallyFree
  Hom.zeroLocusIdeal (closedHilbertSectionMap ι n e A Φ r φ) ⌊Φ.eval (r : ℚ)⌋₊

/-- **The Hilbert scheme of a closed subscheme `C ⊆ P^n_A`**, a closed subscheme of the Hilbert
scheme of `P^n_A`. -/
abbrev closedHilbertScheme : Scheme.{u} :=
  (closedHilbertIdeal ι n e A Φ r hr φ).subscheme

/-- The closed immersion of the Hilbert scheme of `C` into the Hilbert scheme of `P^n_A`. -/
abbrev closedHilbertSchemeι : closedHilbertScheme ι n e A Φ r hr φ ⟶ hilbertScheme ι n e A Φ r :=
  (closedHilbertIdeal ι n e A Φ r hr φ).subschemeι

/-- **The Hilbert scheme of `C` is a closed subscheme of the Hilbert scheme of `P^n_A`.** -/
instance isClosedImmersion_closedHilbertSchemeι :
    IsClosedImmersion (closedHilbertSchemeι ι n e A Φ r hr φ) :=
  inferInstanceAs (IsClosedImmersion (closedHilbertIdeal ι n e A Φ r hr φ).subschemeι)

/-- The Hilbert scheme of `C` is locally Noetherian, as a closed subscheme of a locally Noetherian
scheme. -/
instance isLocallyNoetherian_closedHilbertScheme :
    IsLocallyNoetherian (closedHilbertScheme ι n e A Φ r hr φ) :=
  LocallyOfFiniteType.isLocallyNoetherian (closedHilbertSchemeι ι n e A Φ r hr φ)

/-- The Hilbert scheme of `C` is Noetherian, as a closed subscheme of the Noetherian Hilbert
scheme. -/
instance isNoetherian_closedHilbertScheme : IsNoetherian (closedHilbertScheme ι n e A Φ r hr φ) :=
  haveI : TopologicalSpace.NoetherianSpace (closedHilbertScheme ι n e A Φ r hr φ) :=
    (closedHilbertSchemeι ι n e A Φ r hr φ).isEmbedding.isInducing.noetherianSpace
  {}

/-- The Hilbert scheme of `C` as a locally Noetherian test scheme over `Spec A`. -/
def closedHilbertSchemeOver : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) where
  obj := Over.mk (closedHilbertSchemeι ι n e A Φ r hr φ ≫ (hilbertSchemeOver ι n e A Φ r).obj.hom)
  property := isLocallyNoetherian_closedHilbertScheme ι n e A Φ r hr φ

/-- The closed immersion into the Hilbert scheme of `P^n_A`, as a morphism of locally Noetherian
test schemes over `Spec A`. -/
def closedHilbertSchemeToHilbertScheme :
    closedHilbertSchemeOver ι n e A Φ r hr φ ⟶ hilbertSchemeOver ι n e A Φ r :=
  ObjectProperty.homMk (Over.homMk (closedHilbertSchemeι ι n e A Φ r hr φ) rfl)

theorem closedHilbertSchemeToHilbertScheme_hom_left :
    (closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ).hom.left =
      closedHilbertSchemeι ι n e A Φ r hr φ :=
  rfl

variable {ι n e A Φ r φ}

/-- **The closed condition**: for a closed `C ⊆ P^n_A` cut out by the sections of `φ`, a morphism
`a : T ⟶ H` from a locally Noetherian test scheme factors through the Hilbert scheme of `C` if
and only if the point of `Hilb^Φ(T)` given by `a` is contained in `C_T`. -/
theorem exists_lift_closedHilbertSchemeι_iff {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r) :
    (∃ a' : T.obj.left ⟶ closedHilbertScheme ι n e A Φ r hr φ,
        a' ≫ closedHilbertSchemeι ι n e A Φ r hr φ = a.hom.left) ↔
      C.comap (pullback.fst (toSpec A ι) T.obj.hom) ≤
        ((locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a).1 := by
  have : IsLocallyNoetherian (hilbertSchemeOver ι n e A Φ r).obj.left :=
    (hilbertSchemeOver ι n e A Φ r).property
  have hrank := sheafHasRank_directImageSheaf_universalHilbertFamily ι n e A Φ r hr
  have := hrank.isFiniteLocallyFree
  refine (Scheme.IdealSheafData.exists_lift_subschemeι_iff
    (closedHilbertIdeal ι n e A Φ r hr φ) a.hom.left).trans ?_
  rw [closedHilbertIdeal, Hom.zeroLocusIdeal_comap_eq_bot_iff _ hrank, closedHilbertSectionMap,
    IsHilbertFamily.pullback_map_directImageSectionMap_eq_zero_iff ι n e
      (isHilbertFamily_universalHilbertFamily ι n e A Φ r) r hr φ T.obj.hom a.hom.left
      (Over.w a.hom),
    ← comap_le_iff_directImageSectionMap_eq_zero ι T.obj.hom r φ hC]
  rfl

variable (ι n e A Φ r φ)

/-- **The Hilbert scheme of a closed subscheme represents its Hilbert subfunctor** (Nitsure,
arXiv:math/0504590v1, Theorem 5.3, p. 24, for `X = C` and `E = 𝒪_C`, that is, Theorem 6.1, p. 28,
for a closed `X = C ⊆ P^n_A`, through Lemma 5.4 (ii), p. 25, with the vanishing scheme of
Remark 3.6 replaced by a Fitting zero scheme): for a Noetherian ring `A`, `ι ≃ Fin (n + 1)`,
`Φ ∈ ℚ[X]`, a natural `r ≥ hilbertRegularityBound n Φ` and sections `φ : 𝒪^J ⟶ 𝒪(r)` whose
section pairing cuts out `C`, the Hilbert subfunctor of `C` on locally Noetherian test schemes
over `Spec A` is represented by the closed subscheme `closedHilbertScheme` of the Hilbert scheme
of `P^n_A`. A morphism `a` corresponds to the pullback of the universal family along
`a ≫ closedHilbertSchemeToHilbertScheme`. -/
def locallyNoetherianClosedHilbertSubfunctorRepresentableBy
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C) :
    (locallyNoetherianClosedHilbertSubfunctor ι A Φ C).toFunctor.RepresentableBy
      (closedHilbertSchemeOver ι n e A Φ r hr φ) where
  homEquiv {T} := Equiv.ofBijective
    (fun a => ⟨(locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
        (a ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ),
      (exists_lift_closedHilbertSchemeι_iff hr hC
        (a ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ)).mp ⟨a.hom.left, rfl⟩⟩)
    ⟨fun a b hab => by
      have h₁ := (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv.injective
        (congrArg Subtype.val hab)
      have h₂ : a.hom.left ≫ closedHilbertSchemeι ι n e A Φ r hr φ =
          b.hom.left ≫ closedHilbertSchemeι ι n e A Φ r hr φ :=
        congrArg (fun c => c.hom.left) h₁
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact (cancel_mono (closedHilbertSchemeι ι n e A Φ r hr φ)).mp h₂,
    fun Z => by
      let a₀ := (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv.symm Z.1
      have hZ : C.comap (pullback.fst (toSpec A ι) T.obj.hom) ≤
          ((locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a₀).1 := by
        rw [Equiv.apply_symm_apply]
        exact Z.2
      obtain ⟨a', ha'⟩ := (exists_lift_closedHilbertSchemeι_iff hr hC a₀).mpr hZ
      let a : T ⟶ closedHilbertSchemeOver ι n e A Φ r hr φ := ObjectProperty.homMk (Over.homMk a'
        (by
          change a' ≫ closedHilbertSchemeι ι n e A Φ r hr φ ≫ _ = _
          rw [← Category.assoc, ha']
          exact Over.w a₀.hom))
      have ha : a ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ = a₀ := by
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact ha'
      refine ⟨a, Subtype.ext ?_⟩
      change (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
        (a ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ) = Z.1
      rw [ha, Equiv.apply_symm_apply]⟩
  homEquiv_comp {T T'} f a := Subtype.ext (by
    change (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
        ((f ≫ a) ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ) =
      (locallyNoetherianHilbertFunctor ι A Φ).map f.op
        ((locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
          (a ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ))
    rw [Category.assoc, Functor.RepresentableBy.homEquiv_comp])

/-- **Compatibility with the Hilbert scheme of `P^n_A`**: the representing equivalence sends
`a : T ⟶ closedHilbertSchemeOver …` to the pullback of the universal family of `H` along
`T ⟶ closedHilbertScheme ⟶ H`. -/
theorem locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_coe
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ closedHilbertSchemeOver ι n e A Φ r hr φ) :
    ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ hC).homEquiv a :
        (locallyNoetherianHilbertFunctor ι A Φ).obj (op T)) =
      (locallyNoetherianHilbertFunctor ι A Φ).map
        (a ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ).op
        (universalHilbertPoint ι n e A Φ r) :=
  rfl

/-- **The universal family of `Hilb^Φ_C`** is the restriction of the universal family of the
Hilbert scheme `H` to `closedHilbertScheme`: its pullback along
`P^n_A ×_{Spec A} closedHilbertScheme ⟶ P^n_A ×_{Spec A} H`. -/
theorem locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_id_coe
    {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C) :
    ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ hC).homEquiv (𝟙 _) :
        (locallyNoetherianHilbertFunctor ι A Φ).obj
          (op (closedHilbertSchemeOver ι n e A Φ r hr φ))).1 =
      (universalHilbertFamily ι n e A Φ r).comap
        (baseChangeMap ι (hilbertSchemeOver ι n e A Φ r).obj.hom
          (closedHilbertSchemeOver ι n e A Φ r hr φ).obj.hom (closedHilbertSchemeι ι n e A Φ r hr φ)
          rfl) := by
  rw [locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_coe, Category.id_comp]
  rfl

/-- **The universal family of the Hilbert scheme of `C`**: the point of `Hilb^Φ_C` corresponding to
the identity (`locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_id_coe`). -/
def universalClosedHilbertPoint {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C) :
    (locallyNoetherianClosedHilbertSubfunctor ι A Φ C).toFunctor.obj
      (op (closedHilbertSchemeOver ι n e A Φ r hr φ)) :=
  (locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ hC).homEquiv (𝟙 _)

/-- The universal family of the Hilbert scheme of `C` is the pullback of the universal family of
the Hilbert scheme of `P^n_A` along the closed immersion. -/
theorem universalClosedHilbertPoint_coe {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C) :
    (universalClosedHilbertPoint ι n e A Φ r hr φ hC).1 =
      (locallyNoetherianHilbertFunctor ι A Φ).map
        (closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ).op
        (universalHilbertPoint ι n e A Φ r) := by
  change (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
    (𝟙 _ ≫ closedHilbertSchemeToHilbertScheme ι n e A Φ r hr φ) = _
  rw [Category.id_comp, locallyNoetherianHilbertFunctorRepresentableBy_homEquiv]

end Scheme

section Existence

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X])

/-- **Existence of the Hilbert scheme of a closed subscheme** (Nitsure, arXiv:math/0504590v1,
Theorem 6.1, p. 28, for a closed `X = C ⊆ P^n_A`, on locally Noetherian test schemes): for a
Noetherian ring `A` and a closed subscheme `C ⊆ P^n_A`, for every large enough natural `r` there
are sections `φ` of `𝒪(r)` cutting out `C`, and then the closed subscheme
`closedHilbertScheme ι n e A Φ r hr φ` of the Hilbert scheme of `P^n_A` represents the Hilbert
subfunctor of `C`. -/
theorem exists_closedHilbertScheme_representableBy (C : (ProjectiveSpace A ι).IdealSheafData) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ (hr : hilbertRegularityBound n Φ ≤ r) (J : Type u)
      (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
        twistingSheaf A ι (r : ℤ)),
      Nonempty ((locallyNoetherianClosedHilbertSubfunctor ι A Φ C).toFunctor.RepresentableBy
        (closedHilbertSchemeOver ι n e A Φ r hr φ)) := by
  obtain ⟨m, hm⟩ := exists_sectionPairing_imageIdealData_eq ι n e C
  refine ⟨max (hilbertRegularityBound n Φ).toNat m.toNat, fun r hr₀ => ?_⟩
  have hr : hilbertRegularityBound n Φ ≤ r :=
    (Int.self_le_toNat _).trans (by exact_mod_cast le_trans (le_max_left _ _) hr₀)
  have hmr : m ≤ (r : ℤ) :=
    (Int.self_le_toNat m).trans (by exact_mod_cast le_trans (le_max_right _ _) hr₀)
  obtain ⟨J, φ, hC⟩ := hm r hmr
  exact ⟨hr, J, φ, ⟨locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A Φ r hr φ hC⟩⟩

end Existence

end ProjectiveSpace

end AlgebraicGeometry

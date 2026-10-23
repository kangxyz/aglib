/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.PulledBackGrassmannianPoint
public import Aglib.AlgebraicGeometry.HilbertScheme.FlatteningStratum
public import Aglib.AlgebraicGeometry.HilbertScheme.LocallyNoetherianFunctor
public import Aglib.AlgebraicGeometry.Grassmannian.Finiteness

/-!
# The Hilbert scheme of projective space over a Noetherian ring

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)`, `Φ ∈ ℚ[X]`, `r ≥ hilbertRegularityBound n Φ` a
natural number, `k = ⌊Φ(r)⌋₊`, `N = (n + r).choose r`, and `G` the Grassmannian of rank-`k`
quotients of `𝒪^N` (`Grassmannian.schemeOver (CommRingCat.of A) k N`), a Noetherian scheme over
`Spec A`. The
**Hilbert scheme** `G_Φ = hilbertScheme ι n e A Φ r` is the flattening stratum with Hilbert
polynomial `Φ` of the structure module of the universal subscheme `Z_univ ⊆ P^n_A ×_{Spec A} G`
(`universalHilbertSubscheme`), a locally closed subscheme of `G` (`hilbertSchemeι` is an immersion).
It represents the Hilbert functor of `P^n_A` on locally Noetherian test schemes
(`locallyNoetherianHilbertFunctorRepresentableBy`), with universal family the restriction of
`Z_univ` to `G_Φ` (`universalHilbertFamily`).

This is Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 27,
Theorem 5.3 for `X = P^n_A` and `E = 𝒪` (trivial `V` and `W`), through the proof of Theorem 5.2
(p. 24, pp. 25–27), with the test schemes of §1, pp. 3–4, the Grassmannian and the
flattening stratification of §4 (Theorem 4.3, `FlatteningStratification/Global`) over the
Noetherian base `G`, and with locally Noetherian test schemes:

* by property (F) (p. 26, `exists_lift_flatteningStratumι_iff_isHilbertFamily`), `φ : T ⟶ G`
  factors through `G_Φ` exactly when `Z_univ.comap P^n_φ ∈ Hilb^Φ(T)`
  (`exists_lift_hilbertSchemeι_iff`);
* "⇒": a point `Z` of `Hilb^Φ(T)` is the pullback of `Z_univ` along its Grassmannian point
  (`IsHilbertFamily.universalHilbertSubscheme_comap_grassmannianMap`), which therefore factors
  through `G_Φ`;
* "⇐": if `Z_univ.comap P^n_φ ∈ Hilb^Φ(T)`, its Grassmannian point is `φ`
  (`IsHilbertFamily.grassmannianMap_eq_of_comap_universalHilbertSubscheme`), so the factorization
  is unique.

As a corollary the Grassmannian points of `Hilb^Φ` are injective
(`locallyNoetherianGrassmannianNatTrans_app_injective`): the natural transformation of
`HilbertScheme/LocallyNoetherianFunctor` is an embedding of functors, through `G_Φ ⟶ G`.
Projectivity of `G_Φ` (Nitsure's valuative-criterion step) is not part of this file.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry

/-- Base-changed maps along equal morphisms agree. -/
theorem ProjectiveSpace.baseChangeMap_congr (ι : Type u) {A : Type u} [CommRing A]
    {T T' : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A))
    {f₁ f₂ : T' ⟶ T} (hf : f₁ = f₂) (h₁ : f₁ ≫ g = g') (h₂ : f₂ ≫ g = g') :
    baseChangeMap ι g g' f₁ h₁ = baseChangeMap ι g g' f₂ h₂ := by
  subst hf
  rfl

namespace ProjectiveSpace

/-- The Grassmannian point depends only on the closed subscheme. -/
theorem IsHilbertFamily.grassmannianMap_congr (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {A : Type u} [CommRing A] {Φ : ℚ[X]} {T : Scheme.{u}} [IsLocallyNoetherian T]
    {g : T ⟶ Spec (CommRingCat.of A)} {Z₁ Z₂ : (pullback (toSpec A ι) g).IdealSheafData}
    (h : Z₁ = Z₂) (h₁ : IsHilbertFamily ι Φ g Z₁) (h₂ : IsHilbertFamily ι Φ g Z₂) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    h₁.grassmannianMap ι n e r hr = h₂.grassmannianMap ι n e r hr := by
  subst h
  rfl

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X]) (r : ℕ)

include e in
/-- The structure module of the universal subscheme is coherent: `P^n` over the Noetherian
Grassmannian is locally Noetherian. -/
theorem affineLocallyFiniteType_universalHilbertSubscheme :
    Scheme.Modules.QuasiCoherent.affineLocallyFiniteType
      (pullback (toSpec A ι)
        (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom)
      (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).quotientModule :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).affineLocallyFiniteType_quotientModule

/-- **The Hilbert scheme** `G_Φ` of `P^n_A` (Nitsure, arXiv:math/0504590v1, §5, pp. 26–27): the
flattening stratum with Hilbert polynomial `Φ` of `𝒪_{Z_univ}` over the Grassmannian `G` of
rank-`⌊Φ(r)⌋₊` quotients of `𝒪^N`, `N = (n + r).choose r`. -/
def hilbertScheme : Scheme.{u} :=
  Scheme.Cohomology.flatteningStratum ι
    (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom n e
    (affineLocallyFiniteType_universalHilbertSubscheme ι n e A Φ r) Φ

/-- The locally closed immersion `G_Φ ⟶ G` of the Hilbert scheme into the Grassmannian. -/
def hilbertSchemeι :
    hilbertScheme ι n e A Φ r ⟶
      (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).left :=
  Scheme.Cohomology.flatteningStratumι ι
    (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom n e
    (affineLocallyFiniteType_universalHilbertSubscheme ι n e A Φ r) Φ

/-- **The Hilbert scheme is a locally closed subscheme of the Grassmannian.** -/
instance isImmersion_hilbertSchemeι : IsImmersion (hilbertSchemeι ι n e A Φ r) :=
  inferInstanceAs (IsImmersion (Scheme.Cohomology.flatteningStratumι ι
    (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom n e
    (affineLocallyFiniteType_universalHilbertSubscheme ι n e A Φ r) Φ))

/-- The Hilbert scheme is locally Noetherian, as a locally closed subscheme of the Noetherian
Grassmannian. -/
instance isLocallyNoetherian_hilbertScheme : IsLocallyNoetherian (hilbertScheme ι n e A Φ r) :=
  inferInstanceAs (IsLocallyNoetherian (Scheme.Cohomology.flatteningStratum ι
    (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom n e
    (affineLocallyFiniteType_universalHilbertSubscheme ι n e A Φ r) Φ))

/-- The Hilbert scheme is Noetherian: its underlying space embeds into the Noetherian space of
the Grassmannian (`hilbertSchemeι` is an immersion). -/
instance isNoetherian_hilbertScheme : IsNoetherian (hilbertScheme ι n e A Φ r) :=
  haveI : TopologicalSpace.NoetherianSpace (hilbertScheme ι n e A Φ r) :=
    (hilbertSchemeι ι n e A Φ r).isEmbedding.isInducing.noetherianSpace
  {}

/-- The Hilbert scheme as a locally Noetherian test scheme over `Spec A`. -/
def hilbertSchemeOver : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) where
  obj := Over.mk (hilbertSchemeι ι n e A Φ r ≫
    (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom)
  property := isLocallyNoetherian_hilbertScheme ι n e A Φ r

/-- The immersion `G_Φ ⟶ G` as a morphism over `Spec A`. -/
def hilbertSchemeToGrassmannian :
    (hilbertSchemeOver ι n e A Φ r).obj ⟶
      Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r) :=
  Over.homMk (hilbertSchemeι ι n e A Φ r) rfl

theorem hilbertSchemeToGrassmannian_left :
    (hilbertSchemeToGrassmannian ι n e A Φ r).left = hilbertSchemeι ι n e A Φ r :=
  rfl

/-- **Property (F) for the universal subscheme** (Nitsure, arXiv:math/0504590v1, §5, p. 26): a
morphism `f : T ⟶ G` from a locally Noetherian `T` over `Spec A` factors through the Hilbert
scheme if and only if the pullback of the universal subscheme along `P^n_f` is a point of
`Hilb^Φ(T)`. -/
theorem exists_lift_hilbertSchemeι_iff {T : Scheme.{u}} [IsLocallyNoetherian T]
    (gT : T ⟶ Spec (CommRingCat.of A))
    (f : T ⟶ (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊
      ((n + r).choose r)).left)
    (hf : f ≫ (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊
      ((n + r).choose r)).hom = gT) :
    (∃ h : T ⟶ hilbertScheme ι n e A Φ r, h ≫ hilbertSchemeι ι n e A Φ r = f) ↔
      IsHilbertFamily ι Φ gT ((universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
        (baseChangeMap ι
          (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom
          gT f hf)) := by
  subst hf
  exact exists_lift_flatteningStratumι_iff_isHilbertFamily ι _
    (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e) n e
    (affineLocallyFiniteType_universalHilbertSubscheme ι n e A Φ r) Φ f

/-- **The universal family** over the Hilbert scheme: the pullback of the universal subscheme
`Z_univ` along `P^n_A ×_{Spec A} G_Φ ⟶ P^n_A ×_{Spec A} G`. -/
def universalHilbertFamily :
    (pullback (toSpec A ι) (hilbertSchemeOver ι n e A Φ r).obj.hom).IdealSheafData :=
  (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
    (pullbackBaseChange ι
      (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom
      (hilbertSchemeι ι n e A Φ r))

/-- The universal family is a point of `Hilb^Φ(G_Φ)`. -/
theorem isHilbertFamily_universalHilbertFamily :
    IsHilbertFamily ι Φ (hilbertSchemeOver ι n e A Φ r).obj.hom
      (universalHilbertFamily ι n e A Φ r) :=
  (exists_lift_flatteningStratumι_iff_isHilbertFamily ι _
    (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e) n e
    (affineLocallyFiniteType_universalHilbertSubscheme ι n e A Φ r) Φ
    (hilbertSchemeι ι n e A Φ r)).mp ⟨𝟙 _, Category.id_comp _⟩

/-- The universal family as an element of the Hilbert functor at `G_Φ`. -/
def universalHilbertPoint :
    (locallyNoetherianHilbertFunctor ι A Φ).obj (op (hilbertSchemeOver ι n e A Φ r)) :=
  ⟨universalHilbertFamily ι n e A Φ r, isHilbertFamily_universalHilbertFamily ι n e A Φ r⟩

variable {ι n e A Φ r}

/-- The pullback of the universal family along `a : T ⟶ G_Φ` is the pullback of the universal
subscheme along `P^n` of `T ⟶ G_Φ ⟶ G`. -/
theorem map_universalHilbertPoint_coe {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r) :
    ((locallyNoetherianHilbertFunctor ι A Φ).map a.op (universalHilbertPoint ι n e A Φ r)).1 =
      (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
        (baseChangeMap ι
          (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom
          T.obj.hom (a.hom ≫ hilbertSchemeToGrassmannian ι n e A Φ r).left
          (Over.w (a.hom ≫ hilbertSchemeToGrassmannian ι n e A Φ r))) := by
  change ((universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
      (pullbackBaseChange ι _ (hilbertSchemeι ι n e A Φ r))).comap
        (baseChangeMap ι _ T.obj.hom a.hom.left (Over.w a.hom)) = _
  rw [← Scheme.IdealSheafData.comap_comp]
  congr 1
  exact (baseChangeMap_comp ι _ _ _ _ _ rfl (Over.w a.hom) _).symm

variable (ι n e A Φ r)

section Representability

variable (hr : hilbertRegularityBound n Φ ≤ r)

include hr in
/-- **The Grassmannian point of a pulled-back universal family is the given map**: for
`a : T ⟶ G_Φ`, the pullback of the universal family along `a` is a point of `Hilb^Φ(T)` whose
Grassmannian point is `T ⟶ G_Φ ⟶ G` ("⇐",
`grassmannianMap_eq_of_comap_universalHilbertSubscheme`). -/
theorem grassmannianMap_map_universalHilbertPoint
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r)
    (hZ : IsHilbertFamily ι Φ T.obj.hom
      ((locallyNoetherianHilbertFunctor ι A Φ).map a.op (universalHilbertPoint ι n e A Φ r)).1) :
    hZ.grassmannianMap ι n e r hr = a.hom ≫ hilbertSchemeToGrassmannian ι n e A Φ r := by
  have hx : IsHilbertFamily ι Φ T.obj.hom
      ((universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
        (baseChangeMap ι
          (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom
          T.obj.hom (a.hom ≫ hilbertSchemeToGrassmannian ι n e A Φ r).left
          (Over.w (a.hom ≫ hilbertSchemeToGrassmannian ι n e A Φ r)))) := by
    rw [← map_universalHilbertPoint_coe a]
    exact hZ
  rw [IsHilbertFamily.grassmannianMap_congr ι n e (T := T.obj.left) (g := T.obj.hom)
    (map_universalHilbertPoint_coe a) hZ hx r hr]
  exact IsHilbertFamily.grassmannianMap_eq_of_comap_universalHilbertSubscheme ι n e r hr _ hx

include hr in
/-- **Uniqueness of the factorization**: two morphisms to `G_Φ` with the same pullback of the
universal family are equal. -/
theorem map_universalHilbertPoint_injective
    (T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))) :
    Function.Injective fun a : T ⟶ hilbertSchemeOver ι n e A Φ r =>
      (locallyNoetherianHilbertFunctor ι A Φ).map a.op (universalHilbertPoint ι n e A Φ r) := by
  intro a b hab
  have ha := grassmannianMap_map_universalHilbertPoint ι n e A Φ r hr a
    ((locallyNoetherianHilbertFunctor ι A Φ).map a.op (universalHilbertPoint ι n e A Φ r)).2
  have hb := grassmannianMap_map_universalHilbertPoint ι n e A Φ r hr b
    ((locallyNoetherianHilbertFunctor ι A Φ).map b.op (universalHilbertPoint ι n e A Φ r)).2
  have hφ : a.hom ≫ hilbertSchemeToGrassmannian ι n e A Φ r =
      b.hom ≫ hilbertSchemeToGrassmannian ι n e A Φ r :=
    ha.symm.trans ((IsHilbertFamily.grassmannianMap_congr ι n e (T := T.obj.left)
      (g := T.obj.hom) (congrArg Subtype.val hab) _ _ r hr).trans hb)
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_mono (hilbertSchemeι ι n e A Φ r)).mp (congrArg CommaMorphism.left hφ)

include hr in
/-- **Existence of the factorization**: every point of `Hilb^Φ(T)` is the pullback of the
universal family along a morphism `T ⟶ G_Φ` ("⇒" and property (F)). -/
theorem map_universalHilbertPoint_surjective
    (T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))) :
    Function.Surjective fun a : T ⟶ hilbertSchemeOver ι n e A Φ r =>
      (locallyNoetherianHilbertFunctor ι A Φ).map a.op (universalHilbertPoint ι n e A Φ r) := by
  intro Z
  have hZ : IsHilbertFamily ι Φ T.obj.hom Z.1 := Z.2
  have h2 := hZ.universalHilbertSubscheme_comap_grassmannianMap ι n e r hr
  have hH : IsHilbertFamily ι Φ T.obj.hom
      ((universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
        (baseChangeMap ι
          (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom
          T.obj.hom (hZ.grassmannianMap ι n e r hr).left
          (Over.w (hZ.grassmannianMap ι n e r hr)))) := by
    rw [h2]
    exact hZ
  obtain ⟨h, hh⟩ := (exists_lift_hilbertSchemeι_iff ι n e A Φ r T.obj.hom
    (hZ.grassmannianMap ι n e r hr).left (Over.w (hZ.grassmannianMap ι n e r hr))).mpr hH
  let a : T ⟶ hilbertSchemeOver ι n e A Φ r := ObjectProperty.homMk (Over.homMk h (by
    change h ≫ hilbertSchemeι ι n e A Φ r ≫ _ = _
    rw [← Category.assoc, hh]
    exact Over.w (hZ.grassmannianMap ι n e r hr)))
  refine ⟨a, Subtype.ext ?_⟩
  refine (map_universalHilbertPoint_coe a).trans (Eq.trans ?_ h2)
  exact congrArg (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
    (baseChangeMap_congr ι _ _ hh _ _)

/-- **Representability of the Hilbert functor** (Nitsure, arXiv:math/0504590v1, §5, p. 27,
Theorem 5.3 for `X = P^n_A` and `E = 𝒪`, through the proof of Theorem 5.2, up to projectivity):
for a Noetherian ring `A`,
`ι ≃ Fin (n + 1)`, `Φ ∈ ℚ[X]` and a natural `r ≥ hilbertRegularityBound n Φ`, the Hilbert functor
of `P^n_A` on locally Noetherian test schemes over `Spec A` is represented by the Hilbert scheme
`G_Φ`, a locally closed subscheme of the Grassmannian of rank-`⌊Φ(r)⌋₊` quotients of `𝒪^N`,
`N = (n + r).choose r` (`isImmersion_hilbertSchemeι`), with universal family
`universalHilbertFamily`. -/
def locallyNoetherianHilbertFunctorRepresentableBy :
    (locallyNoetherianHilbertFunctor ι A Φ).RepresentableBy (hilbertSchemeOver ι n e A Φ r) where
  homEquiv {T} := Equiv.ofBijective
    (fun a => (locallyNoetherianHilbertFunctor ι A Φ).map a.op (universalHilbertPoint ι n e A Φ r))
    ⟨map_universalHilbertPoint_injective ι n e A Φ r hr T,
      map_universalHilbertPoint_surjective ι n e A Φ r hr T⟩
  homEquiv_comp {T T'} f a := by
    change (locallyNoetherianHilbertFunctor ι A Φ).map (f ≫ a).op _ =
      (locallyNoetherianHilbertFunctor ι A Φ).map f.op
        ((locallyNoetherianHilbertFunctor ι A Φ).map a.op _)
    rw [op_comp, Functor.map_comp_apply]

/-- The representing equivalence sends `a : T ⟶ G_Φ` to the pullback of the universal family. -/
theorem locallyNoetherianHilbertFunctorRepresentableBy_homEquiv
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r) :
    (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a =
      (locallyNoetherianHilbertFunctor ι A Φ).map a.op (universalHilbertPoint ι n e A Φ r) :=
  rfl

omit [IsNoetherianRing A] in
include hr in
/-- **The Grassmannian points of `Hilb^Φ` are injective** (Nitsure, arXiv:math/0504590v1, §5,
p. 26, the embedding `Hilb^Φ → Grass`): a point `Z` of `Hilb^Φ(T)` is the pullback of the universal
subscheme along its Grassmannian point (`universalHilbertSubscheme_comap_grassmannianMap`), so
points with the same Grassmannian point are equal. -/
theorem locallyNoetherianGrassmannianNatTrans_app_injective
    (T : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ) :
    Function.Injective ((locallyNoetherianGrassmannianNatTrans ι n e A Φ r hr).app T) := by
  intro Z₁ Z₂ h
  have : IsLocallyNoetherian T.unop.obj.left := T.unop.property
  have h₁ : IsHilbertFamily ι Φ T.unop.obj.hom Z₁.1 := Z₁.2
  have h₂ : IsHilbertFamily ι Φ T.unop.obj.hom Z₂.1 := Z₂.2
  have h' : h₁.grassmannianMap ι n e r hr = h₂.grassmannianMap ι n e r hr := h
  apply Subtype.ext
  rw [← h₁.universalHilbertSubscheme_comap_grassmannianMap ι n e r hr,
    ← h₂.universalHilbertSubscheme_comap_grassmannianMap ι n e r hr]
  exact congrArg (fun φ : Over.mk T.unop.obj.hom ⟶
      Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r) =>
    (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
      (baseChangeMap ι
        (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom
        T.unop.obj.hom φ.left (Over.w φ))) h'

include hr in
/-- **The representing isomorphism is compatible with the Grassmannian embedding**: under
`locallyNoetherianHilbertFunctorRepresentableBy`, the Grassmannian point of the point of
`Hilb^Φ(T)` given by `a : T ⟶ G_Φ` is `T ⟶ G_Φ ⟶ G`. -/
theorem locallyNoetherianGrassmannianNatTrans_app_homEquiv
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r) :
    (locallyNoetherianGrassmannianNatTrans ι n e A Φ r hr).app (op T)
        ((locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv a) =
      a.hom ≫ hilbertSchemeToGrassmannian ι n e A Φ r :=
  grassmannianMap_map_universalHilbertPoint ι n e A Φ r hr a _

/-- The universal family corresponds to the identity of `G_Φ`. -/
theorem locallyNoetherianHilbertFunctorRepresentableBy_homEquiv_id :
    (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr).homEquiv
        (𝟙 (hilbertSchemeOver ι n e A Φ r)) =
      universalHilbertPoint ι n e A Φ r := by
  rw [locallyNoetherianHilbertFunctorRepresentableBy_homEquiv, op_id, Functor.map_id_apply]

end Representability

end ProjectiveSpace

end AlgebraicGeometry

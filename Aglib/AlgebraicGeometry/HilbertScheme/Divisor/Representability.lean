/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.BaseChange
public import Aglib.AlgebraicGeometry.HilbertScheme.Divisor.Functor
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.PointPullback
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.LocallyNoetherian
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.OpenSubscheme

/-!
# `Div^θ_X` is an open subscheme of `Hilb^θ_X`

Let `A` be a ring, `ι` a finite coordinate type, `i : X ⟶ P^n_A = ProjectiveSpace A ι` a closed
immersion over `Spec A` (`hi : i ≫ toSpec A ι = πX`) with `X` flat over `A` (`[Flat πX]`), and
`θ ∈ ℚ[X]`. Write `Hilb^θ_X` for the Hilbert functor of `X` with polynomial `θ` on locally
Noetherian test schemes over `Spec A` (X-first, `locallyNoetherianImmersedHilbertFunctor i hi θ`)
and `Div^θ_X ⊆ Hilb^θ_X` for its subfunctor of relative effective Cartier divisors
(`locallyNoetherianRelativeDivisorSubfunctor`, `HilbertScheme/Divisor/Functor`).

* `divisorLocus ξ`, for a family `ξ ∈ Hilb^θ_X(T)`: the open subscheme of the points of `T` over
  which the fibre of `ξ` is an effective Cartier divisor of the fibre of `X ×_{Spec A} T`
  (`Scheme.Hom.fiberCartierLocus`, open since `X ×_{Spec A} T ⟶ T` is flat, of finite type and
  universally closed over the locally Noetherian `T`; `EffectiveCartierDivisor/Relative/Open`).
* `preimage_divisorLocus_eq_top_iff`: a morphism `g : Z ⟶ T` from a locally Noetherian test scheme
  factors through `divisorLocus ξ` if and only if the pullback of `ξ` to `X ×_{Spec A} Z` is a
  relative effective Cartier divisor over `Z`. This is
  `Scheme.Hom.isRelativeEffectiveCartier_iff_range_subset_of_isPullback`
  (`EffectiveCartierDivisor/Relative/BaseChange`) for the cartesian squares
  `X ×_{Spec A} Z ⟶ X ×_{Spec A} T` over `g` (`Scheme.isPullback_pullbackMap_snd`) and
  `g^* ξ ⟶ ξ` (`Scheme.IdealSheafData.isPullback_subschemeMap_comap`); it contains Kleiman's
  field-extension step. Hence `Div^θ_X` is an open subfunctor of `Hilb^θ_X`
  (`isOpenSubfunctor_locallyNoetherianRelativeDivisorSubfunctor`).

Suppose now that `Hilb^θ_X` is represented by `H` through `E`, with universal family
`W = (E.homEquiv (𝟙 H)).1`, a closed subscheme of `X ×_{Spec A} H` flat and proper over `H`. For a
closed `X ⊆ P^n_A` over a Noetherian `A` such a representation is the closed Hilbert scheme of
`i.ker` (`locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion`,
`HilbertScheme/Immersed/ClosedImmersion`); for an immersion it is
`locallyNoetherianImmersedHilbertFunctorRepresentableBy`
(`HilbertScheme/Immersed/Representability`). The points of `Hilb^θ_X` given by morphisms to `H`
are pullbacks of `W` (`locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap`,
`HilbertScheme/Immersed/PointPullback`).

* `divisorSchemeOver E`: the open subscheme `divisorLocus (E.homEquiv (𝟙 H))` of `H` as a locally
  Noetherian test scheme over `Spec A`, with underlying scheme `divisorScheme E` and the open
  immersion `divisorSchemeι E` into `H` (`divisorSchemeToHilbertScheme E` over `Spec A`);
  `preimage_divisorLocus_homEquiv_id_eq_top_iff` is the factorization criterion for morphisms to
  `H`.
* `locallyNoetherianRelativeDivisorFunctorRepresentableBy E`: **`divisorSchemeOver E` represents
  `Div^θ_X`** (`locallyNoetherianRelativeDivisorFunctor i hi θ`) on locally Noetherian test schemes
  over `Spec A`: `Scheme.LocalRepresentability.representableByRestrictOpens` for the subfunctor
  `locallyNoetherianRelativeDivisorSubfunctor i hi θ` and the open
  `divisorLocus (E.homEquiv (𝟙 H))`, transported along `relativeDivisorFunctorObjEquiv`. A
  morphism `a : Z ⟶ divisorSchemeOver E` corresponds to the point of `Hilb^θ_X(Z)` given by
  `a ≫ divisorSchemeToHilbertScheme E`
  (`locallyNoetherianRelativeDivisorFunctorRepresentableBy_homEquiv_coe`), equivalently to the
  pullback of the universal divisor (`…_homEquiv_coe_eq_comap`).
* `universalDivisor E`, the universal relative effective Cartier divisor
  (`isRelativeEffectiveCartier_universalDivisor`, `isRelativeDivisorFamily_universalDivisor`): the
  restriction of `W` to `X ×_{Spec A} divisorSchemeOver E` (`universalDivisor_eq`).
* `isHQuasiProjective_divisorSchemeOver_hom`, `isNoetherian_divisorScheme` and
  `isNoetherian_divisorScheme_of_isHQuasiProjective`: an open subscheme of an H-quasi-projective `H`
  over a Noetherian ring is H-quasi-projective, hence Noetherian, and of a Noetherian `H`
  Noetherian.

Source: Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 3.7 (statement p. 23, proof
p. 24), in the form with fibre Hilbert polynomial `θ` (the Picard plan's `Div^θ_X`). Kleiman's open
is `U = H − q(W − V)`, `V` the set of points of `W` at which `W` is an effective divisor; here it is
the fibrewise locus `Scheme.Hom.fiberCartierLocus`, which is the same open by Lemma 3.4
(`EffectiveCartierDivisor/Relative/Open`), a route choice. The test schemes are locally Noetherian,
as throughout Kleiman's notes (p. 15: "we work only with locally Noetherian schemes") and as for
the Hilbert scheme (Nitsure, arXiv:math/0504590v1, §1, pp. 3–4); the base-change criterion uses
the locally Noetherian base.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.LocalRepresentability

section Subfunctor

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} (i : X ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πX)
  [IsPreimmersion i] (θ : ℚ[X])

/-- **`Div^θ_X` on locally Noetherian test schemes as a subfunctor of `Hilb^θ_X`**: the
restriction of `relativeDivisorSubfunctor i hi θ` to locally Noetherian test schemes, a subfunctor
of `locallyNoetherianImmersedHilbertFunctor i hi θ`. -/
abbrev locallyNoetherianRelativeDivisorSubfunctor :
    Subfunctor (locallyNoetherianImmersedHilbertFunctor i hi θ) :=
  restrictSubfunctor (Scheme.locallyNoetherianOver _) (relativeDivisorSubfunctor i hi θ)

end Subfunctor

section Locus

variable {ι : Type u} [Finite ι] {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} {i : X ⟶ ProjectiveSpace A ι} {hi : i ≫ toSpec A ι = πX}
  [IsClosedImmersion i] {θ : ℚ[X]} {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}

/-- **The divisor locus of a family** `ξ ∈ Hilb^θ_X(T)` over a locally Noetherian `T` (Kleiman,
arXiv:math/0504020v1, proof of Thm 3.7, p. 24): the open subscheme of the points of `T` over which
the fibre of `ξ ⊆ X ×_{Spec A} T` is an effective Cartier divisor of the fibre of
`X ×_{Spec A} T ⟶ T` (`Scheme.Hom.fiberCartierLocus`; open because `X ×_{Spec A} T ⟶ T` is flat,
of finite type and universally closed and `ξ` is flat over `T`). -/
def divisorLocus [Flat πX] (ξ : (locallyNoetherianImmersedHilbertFunctor i hi θ).obj (op T)) :
    T.obj.left.Opens :=
  haveI : IsProper πX := by subst hi; infer_instance
  haveI : Flat (ξ.1.subschemeι ≫ pullback.snd πX T.obj.hom) := ξ.2.flat
  Scheme.Hom.fiberCartierLocus ξ.1.subschemeι (pullback.snd πX T.obj.hom)

theorem mem_divisorLocus [Flat πX] (ξ : (locallyNoetherianImmersedHilbertFunctor i hi θ).obj (op T))
    (t : T.obj.left) :
    t ∈ divisorLocus ξ ↔
      Scheme.Hom.FiberIsEffectiveCartier ξ.1.subschemeι (pullback.snd πX T.obj.hom) t :=
  Iff.rfl

/-- **Factorization through the divisor locus** (Kleiman, arXiv:math/0504020v1, proof of Thm 3.7,
p. 24): for a family `ξ ∈ Hilb^θ_X(T)` over a locally Noetherian `T`, a morphism `g : Z ⟶ T` from
a locally Noetherian test scheme factors through `divisorLocus ξ` if and only if the pullback of
`ξ` to `X ×_{Spec A} Z` is a relative effective Cartier divisor over `Z`. -/
theorem preimage_divisorLocus_eq_top_iff [Flat πX]
    (ξ : (locallyNoetherianImmersedHilbertFunctor i hi θ).obj (op T))
    {Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (g : Z ⟶ T) :
    g.hom.left ⁻¹ᵁ divisorLocus ξ = ⊤ ↔
      Scheme.Hom.IsRelativeEffectiveCartier
        ((locallyNoetherianImmersedHilbertFunctor i hi θ).map g.op ξ).1.subschemeι
        (pullback.snd πX Z.obj.hom) := by
  have : IsProper πX := by subst hi; infer_instance
  have : Flat (ξ.1.subschemeι ≫ pullback.snd πX T.obj.hom) := ξ.2.flat
  rw [locallyNoetherianImmersedHilbertFunctor_map_coe i hi θ ξ g,
    Scheme.Hom.isRelativeEffectiveCartier_iff_range_subset_of_isPullback
      (Scheme.isPullback_pullbackMap_snd πX T.obj.hom Z.obj.hom g.hom.left (Over.w g.hom))
      (ξ.1.isPullback_subschemeMap_comap _)]
  constructor
  · rintro h _ ⟨z, rfl⟩
    have hz : z ∈ g.hom.left ⁻¹ᵁ divisorLocus ξ := by
      rw [h]
      trivial
    exact hz
  · intro h
    exact eq_top_iff.mpr fun z _ => h ⟨z, rfl⟩

/-- **`Div^θ_X` is an open subfunctor of `Hilb^θ_X`** on locally Noetherian test schemes (Kleiman,
arXiv:math/0504020v1, Thm 3.7, p. 23, proof p. 24; Stacks, Tag 01JI, "representable by open
immersions"): for every family `ξ ∈ Hilb^θ_X(T)`, the morphisms `g : Z ⟶ T` that pull `ξ` back to
a relative effective Cartier divisor are those that factor through the open `divisorLocus ξ`. -/
theorem isOpenSubfunctor_locallyNoetherianRelativeDivisorSubfunctor [Flat πX] :
    IsOpenSubfunctor (locallyNoetherianRelativeDivisorSubfunctor i hi θ) :=
  fun _ ξ => ⟨divisorLocus ξ, fun _ g => (preimage_divisorLocus_eq_top_iff ξ g).symm⟩

end Locus

variable {ι : Type u} [Finite ι] {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} {i : X ⟶ ProjectiveSpace A ι} {hi : i ≫ toSpec A ι = πX}
  [IsClosedImmersion i] {θ : ℚ[X]} {H : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianImmersedHilbertFunctor i hi θ).RepresentableBy H)

/-- **Factorization through the divisor locus of the universal family** (Kleiman,
arXiv:math/0504020v1, proof of Thm 3.7, p. 24): a morphism `a : Z ⟶ H` from a locally Noetherian
test scheme factors through `divisorLocus (E.homEquiv (𝟙 H))` if and only if the point of
`Hilb^θ_X(Z)` it classifies is a relative effective Cartier divisor over `Z`. -/
theorem preimage_divisorLocus_homEquiv_id_eq_top_iff [Flat πX]
    {Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a : Z ⟶ H) :
    a.hom.left ⁻¹ᵁ divisorLocus (E.homEquiv (𝟙 H)) = ⊤ ↔
      Scheme.Hom.IsRelativeEffectiveCartier (E.homEquiv a).1.subschemeι
        (pullback.snd πX Z.obj.hom) := by
  rw [E.homEquiv_eq a]
  exact preimage_divisorLocus_eq_top_iff _ a

/-- **`Div^θ_X` as a locally Noetherian test scheme**: the open subscheme
`divisorLocus (E.homEquiv (𝟙 H))` of the representing scheme `H` of `Hilb^θ_X`. -/
def divisorSchemeOver [Flat πX] : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
  restrictOpens H (divisorLocus (E.homEquiv (𝟙 H)))

/-- **The scheme of `Div^θ_X`**, the underlying scheme of `divisorSchemeOver E`: the open
subscheme `divisorLocus (E.homEquiv (𝟙 H))` of the representing scheme `H` of `Hilb^θ_X`. -/
abbrev divisorScheme [Flat πX] : Scheme.{u} :=
  (divisorSchemeOver E).obj.left

/-- The open immersion of the scheme `divisorScheme E` of `Div^θ_X` into the scheme `H` of
`Hilb^θ_X`. -/
def divisorSchemeι [Flat πX] : divisorScheme E ⟶ H.obj.left :=
  (divisorLocus (E.homEquiv (𝟙 H))).ι

/-- **`Div^θ_X` is an open subscheme of `Hilb^θ_X`.** -/
instance isOpenImmersion_divisorSchemeι [Flat πX] : IsOpenImmersion (divisorSchemeι E) :=
  inferInstanceAs (IsOpenImmersion (divisorLocus (E.homEquiv (𝟙 H))).ι)

theorem range_divisorSchemeι [Flat πX] :
    Set.range (divisorSchemeι E) = divisorLocus (E.homEquiv (𝟙 H)) :=
  Scheme.Opens.range_ι _

/-- The open immersion of `divisorSchemeOver E` into `H`, as a morphism of locally Noetherian
test schemes over `Spec A`. Here `H` is the representing scheme of `Hilb^θ_X`, not the Hilbert
scheme `hilbertSchemeOver` of `P^n_A`. -/
def divisorSchemeToHilbertScheme [Flat πX] : divisorSchemeOver E ⟶ H :=
  restrictOpensι _ _

theorem divisorSchemeToHilbertScheme_hom_left [Flat πX] :
    (divisorSchemeToHilbertScheme E).hom.left = divisorSchemeι E :=
  rfl

theorem divisorSchemeOver_hom [Flat πX] :
    (divisorSchemeOver E).obj.hom = divisorSchemeι E ≫ H.obj.hom :=
  rfl

/-- **`Div^θ_X` is represented by an open subscheme of `Hilb^θ_X`** (Kleiman,
arXiv:math/0504020v1, Thm 3.7, p. 23, proof p. 24, with fibre Hilbert polynomial `θ`, on locally
Noetherian test schemes): if `H` represents the Hilbert functor of `X` on locally Noetherian test
schemes over `Spec A`, the open subscheme `divisorSchemeOver E` of `H` represents `Div^θ_X`. A
morphism `a : Z ⟶ divisorSchemeOver E` corresponds to the point of `Hilb^θ_X(Z)` given by
`a ≫ divisorSchemeToHilbertScheme E`, which is a relative effective Cartier divisor. -/
def locallyNoetherianRelativeDivisorFunctorRepresentableBy [Flat πX] :
    (locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy (divisorSchemeOver E) :=
  (representableByRestrictOpens E (locallyNoetherianRelativeDivisorSubfunctor i hi θ)
    (divisorLocus (E.homEquiv (𝟙 H)))
    fun _ a => (preimage_divisorLocus_homEquiv_id_eq_top_iff E a).symm).ofIso
    (NatIso.ofComponents
      (fun T => (relativeDivisorFunctorObjEquiv i hi θ (op T.unop.obj)).toIso) fun _ => rfl)

/-- **Compatibility with `Hilb^θ_X`**: the representing equivalence of `Div^θ_X` sends
`a : Z ⟶ divisorSchemeOver E` to the point of `Hilb^θ_X(Z)` given by
`a ≫ divisorSchemeToHilbertScheme E`. -/
theorem locallyNoetherianRelativeDivisorFunctorRepresentableBy_homEquiv_coe [Flat πX]
    {Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a : Z ⟶ divisorSchemeOver E) :
    ((locallyNoetherianRelativeDivisorFunctorRepresentableBy E).homEquiv a).1 =
      (E.homEquiv (a ≫ divisorSchemeToHilbertScheme E)).1 :=
  rfl

/-- **The universal divisor** over the scheme of `Div^θ_X`: the relative effective Cartier
divisor of `X ×_{Spec A} divisorSchemeOver E` corresponding to the identity. -/
def universalDivisor [Flat πX] :
    (pullback πX (divisorSchemeOver E).obj.hom).IdealSheafData :=
  ((locallyNoetherianRelativeDivisorFunctorRepresentableBy E).homEquiv (𝟙 _)).1

/-- The universal divisor is a point of `Div^θ_X`. -/
theorem isRelativeDivisorFamily_universalDivisor [Flat πX] :
    IsRelativeDivisorFamily i hi θ (divisorSchemeOver E).obj.hom (universalDivisor E) :=
  ((locallyNoetherianRelativeDivisorFunctorRepresentableBy E).homEquiv (𝟙 _)).2

/-- **The universal divisor is a relative effective Cartier divisor** of
`X ×_{Spec A} divisorSchemeOver E` over `divisorSchemeOver E`. -/
theorem isRelativeEffectiveCartier_universalDivisor [Flat πX] :
    Scheme.Hom.IsRelativeEffectiveCartier (universalDivisor E).subschemeι
      (pullback.snd πX (divisorSchemeOver E).obj.hom) :=
  (isRelativeDivisorFamily_universalDivisor E).isRelativeEffectiveCartier

/-- **The universal divisor is the restriction of the universal family** of `Hilb^θ_X`: the
pullback of `W = (E.homEquiv (𝟙 H)).1` along
`X ×_{Spec A} divisorSchemeOver E ⟶ X ×_{Spec A} H`. -/
theorem universalDivisor_eq [Flat πX] :
    universalDivisor E = (E.homEquiv (𝟙 H)).1.comap (pullback.map πX (divisorSchemeOver E).obj.hom
      πX H.obj.hom (𝟙 X) (divisorSchemeι E) (𝟙 _) (by simp)
      (by rw [Category.comp_id, divisorSchemeOver_hom])) := by
  change (E.homEquiv (𝟙 _ ≫ divisorSchemeToHilbertScheme E)).1 = _
  rw [Category.id_comp, locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap i hi E]
  rfl

/-- **The representing equivalence of `Div^θ_X`** sends `a : Z ⟶ divisorSchemeOver E` to the
pullback of the universal divisor along `X ×_{Spec A} Z ⟶ X ×_{Spec A} divisorSchemeOver E`. -/
theorem locallyNoetherianRelativeDivisorFunctorRepresentableBy_homEquiv_coe_eq_comap [Flat πX]
    {Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a : Z ⟶ divisorSchemeOver E) :
    ((locallyNoetherianRelativeDivisorFunctorRepresentableBy E).homEquiv a).1 =
      (universalDivisor E).comap (pullback.map πX Z.obj.hom πX (divisorSchemeOver E).obj.hom
        (𝟙 X) a.hom.left (𝟙 _) (by simp) (by rw [Category.comp_id, Over.w a.hom])) := by
  rw [Functor.RepresentableBy.homEquiv_eq]
  rfl

/-- **`Div^θ_X` is H-quasi-projective** over a Noetherian ring when `H` is: `divisorSchemeι E` is
an open immersion (Kleiman, arXiv:math/0504020v1, Thm 3.7, p. 23: `Div_{X/S}` is an open
subscheme of `Hilb_{X/S}`; p. 30: `Hilb^θ_{X/S}` is projective over `S`). -/
instance isHQuasiProjective_divisorSchemeOver_hom [IsNoetherianRing A] [Flat πX]
    [IsHQuasiProjective H.obj.hom] : IsHQuasiProjective (divisorSchemeOver E).obj.hom :=
  IsHQuasiProjective.comp_of_isImmersion (divisorSchemeι E) H.obj.hom

/-- The scheme of `Div^θ_X` is Noetherian when `H` is, as an open subscheme. -/
instance isNoetherian_divisorScheme [Flat πX] [IsNoetherian H.obj.left] :
    IsNoetherian (divisorScheme E) :=
  haveI : TopologicalSpace.NoetherianSpace (divisorScheme E) :=
    (divisorSchemeι E).isEmbedding.isInducing.noetherianSpace
  {}

/-- The scheme of `Div^θ_X` is Noetherian when `H` is H-quasi-projective over a Noetherian ring:
it is then H-quasi-projective (`isHQuasiProjective_divisorSchemeOver_hom`). -/
instance isNoetherian_divisorScheme_of_isHQuasiProjective [IsNoetherianRing A] [Flat πX]
    [IsHQuasiProjective H.obj.hom] : IsNoetherian (divisorScheme E) :=
  IsHQuasiProjective.isNoetherian (divisorSchemeOver E).obj.hom

end AlgebraicGeometry.ProjectiveSpace

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Decomposition
public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.Family
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Functor
public import Aglib.AlgebraicGeometry.HilbertScheme.Nonempty
public import Aglib.AlgebraicGeometry.IdealSheaf.ImageOverBase

/-!
# The Hilbert functor of an immersed scheme with Hilbert polynomials in a set

Let `A` be a ring, `ι` a finite coordinate type, `i : Y ⟶ P^n_A = ProjectiveSpace A ι` a
preimmersion over `Spec A` (`hi : i ≫ toSpec A ι = πY`; for an immersion, `Y` is a locally closed
subscheme of `P^n_A`) and `F` a set of polynomials. For `g : T ⟶ Spec A` write
`Y_T = Y ×_{Spec A} T`, `P_T = P^n_A ×_{Spec A} T`, `i_T : Y_T ⟶ P_T` for the base change of `i`
(`immersionBaseChange`, `HilbertScheme/Immersed/Functor`) and `P_t(W)` for the fibre Hilbert
polynomial `fiberHilbertPolynomialAt ι g 𝒪_W t` of a closed subscheme `W ⊆ P_T` at `t ∈ T`.

* **The image over the base.** For a closed subscheme `V ⊆ Y_T` closed in `P_T`, its image
  `V.map i_T` has the same image in `T` (`range_map_immersionBaseChange_subschemeι_comp_snd`) and
  the same properties over `T` that respect isomorphisms, such as flatness, properness and
  surjectivity (`map_immersionBaseChange_subschemeι_comp_snd_iff`); `V` is isomorphic over `P_T`
  to its image (`IdealSheaf/ImageOverBase`). Hence a point of `Hilb^Φ_Y(T)` with `Φ ≠ 0` is
  surjective onto `T` (`IsImmersedHilbertFamily.surjective_of_ne_zero`, from
  `IsHilbertFamily.surjective_of_ne_zero`, `HilbertScheme/Nonempty`), and `P_t(V.map i_T) ≠ 0`
  exactly at the points `t` under `V`
  (`fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff`).
* `IsImmersedHilbertFamilyIn i hi F g V`: **a closed subscheme `V ⊆ Y_T` that is proper and flat
  over `T` and whose image in `P_T` has all fibre Hilbert polynomials in `F`**; it is closed in
  `P_T` and its image is flat over `T` (`IsImmersedHilbertFamilyIn.isClosedImmersion`,
  `IsImmersedHilbertFamilyIn.flat_map`), and the condition is stable under base change
  (`IsImmersedHilbertFamilyIn.comap`). A point of `Hilb^Φ_Y(T)` with `Φ ∈ F` is such a family
  (`IsImmersedHilbertFamily.isImmersedHilbertFamilyIn_of_mem`), and such a family whose
  polynomials are all `Φ` is a point of `Hilb^Φ_Y(T)`
  (`IsImmersedHilbertFamilyIn.isImmersedHilbertFamily_of_fiberHilbertPolynomialAt_eq`); for
  `F = {Φ}` the two conditions agree (`isImmersedHilbertFamilyIn_singleton_iff`). If `0 ∉ F`, such
  a family is surjective onto `T` (`IsImmersedHilbertFamilyIn.surjective_of_zero_notMem`). Every
  closed `V ⊆ Y_T` proper and flat over `T` is such a family for the set of fibre polynomials of its
  image (`isImmersedHilbertFamilyIn_range_fiberHilbertPolynomialAt`), which is finite for
  quasi-compact locally Noetherian `T`
  (`finite_range_fiberHilbertPolynomialAt_map_immersionBaseChange`) and omits `0` exactly when
  `V ⟶ T` is surjective
  (`zero_notMem_range_fiberHilbertPolynomialAt_map_immersionBaseChange_iff`).
* `immersedHilbertFunctorIn i hi F`: the functor `T ↦ {V | IsImmersedHilbertFamilyIn i hi F T V}` on
  all schemes over `Spec A`, acting by pullback along `pullback.map πY _ πY _ (𝟙 Y) f (𝟙 _)`, as
  `immersedHilbertFunctor`; `locallyNoetherianImmersedHilbertFunctorIn` is its restriction to
  locally Noetherian test schemes.
* **Glued families** (`IdealSheaf/GlueCoproduct`, `HilbertScheme/Coproduct/Family`): for families
  `D j ⊆ Y ×_{Spec A} H j` proper over `H j`, the image of the glued family
  `sigmaGlue πY πH D ⊆ Y ×_{Spec A} ∐ H` in `P^n_A ×_{Spec A} ∐ H` is the glued family of the
  images (`map_sigmaGlue_immersionBaseChange`). Hence if every `D j` is a point of
  `Hilb^{Φ j}_Y(H j)` with `Φ j ∈ F`, the glued family is a point of the functor with polynomials
  in `F` (`isImmersedHilbertFamilyIn_sigmaGlue`), and for distinct `Φ j` its pullback along
  `a : T ⟶ ∐ H` has fibre polynomial `Φ j` exactly over `a⁻¹(H j)`
  (`fiberHilbertPolynomialAt_map_comap_sigmaGlue_eq_iff`).

For `F` the set of all polynomials this is Nitsure's Hilbert functor `Hilb_{Y/S}` of the closed
subschemes of `Y_T` that are proper and flat over `T` (*Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, §1, pp. 3–4), which "naturally decomposes as a co-product"
`∐_Φ Hilb^{Φ,L}_{Y/S}` (p. 4), the fibre polynomials taken for `L = i^* 𝒪(1)`; for a finite set `F`
it is the functor represented by the finite disjoint union of the open subschemes
`Hilb^{Φ,L}_{X/S}` in the proof of Thm 6.8, p. 33 ("Let H be the finite disjoint union of the
corresponding open subschemes Hilb^{Φ,L}_{X/S} of Hilb_{X/S}"). The functor is defined on all
schemes over `Spec A`; Nitsure's functors, and the representation
(`HilbertScheme/Coproduct/Representability`), concern locally Noetherian test schemes (§1, p. 3).
The fibre polynomials are the chart polynomials `fiberHilbertPolynomialAt` of the flattening
stratification, so that the decomposition of `HilbertScheme/Coproduct/Decomposition` applies to
the image directly.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Cohomology

variable {ι : Type u} {A : Type u} [CommRing A] {Y : Scheme.{u}}
  {πY : Y ⟶ Spec (CommRingCat.of A)} (i : Y ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πY)

section Image

variable {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback πY g).IdealSheafData)

/-- **The image of a closed subscheme over the base**: if `V ⊆ Y ×_{Spec A} T` is closed in
`P^n_A ×_{Spec A} T`, its image `V.map i_T` and `V` have the same image in `T`. -/
theorem range_map_immersionBaseChange_subschemeι_comp_snd
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g)] :
    Set.range ((V.map (immersionBaseChange i hi g)).subschemeι ≫ pullback.snd (toSpec A ι) g) =
      Set.range (V.subschemeι ≫ pullback.snd πY g) :=
  V.range_map_subschemeι_comp (immersionBaseChange_snd i hi g)

/-- **A closed subscheme and its image have the same properties over the base**: if
`V ⊆ Y ×_{Spec A} T` is closed in `P^n_A ×_{Spec A} T`, then for a property `P` of morphisms that
respects isomorphisms (flat, proper, surjective, ...), `V.map i_T ⟶ T` has `P` if and only if
`V ⟶ T` has `P`. -/
theorem map_immersionBaseChange_subschemeι_comp_snd_iff
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g)]
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P ((V.map (immersionBaseChange i hi g)).subschemeι ≫ pullback.snd (toSpec A ι) g) ↔
      P (V.subschemeι ≫ pullback.snd πY g) :=
  V.map_subschemeι_comp_iff (immersionBaseChange_snd i hi g) P

variable (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- **The fibre polynomial of the image vanishes exactly off the image of the family**: if
`V ⊆ Y ×_{Spec A} T` is closed in `P^n_A ×_{Spec A} T`, then `P_t(V.map i_T) ≠ 0` if and only if
some point of `V` lies over `t` (`fiberHilbertPolynomialAt_quotientModule_ne_zero_iff`). -/
theorem fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g)] (t : T) :
    fiberHilbertPolynomialAt ι g (V.map (immersionBaseChange i hi g)).quotientModule t ≠ 0 ↔
      t ∈ Set.range (V.subschemeι ≫ pullback.snd πY g) := by
  rw [fiberHilbertPolynomialAt_quotientModule_ne_zero_iff ι n e,
    range_map_immersionBaseChange_subschemeι_comp_snd]

end Image

variable {i hi} in
/-- **A point of the Hilbert functor of `Y` with nonzero polynomial covers its base** (Nitsure,
arXiv:math/0504590v1, proof of Thm 6.8, p. 33, "Hence p : D → H is surjective"): if `V` is a
point of `Hilb^Φ_Y(T)` and `Φ ≠ 0`, then `V ⟶ T` is surjective, because its image in
`P^n_A ×_{Spec A} T` is (`IsHilbertFamily.surjective_of_ne_zero`) and has the same image in `T`. -/
theorem IsImmersedHilbertFamily.surjective_of_ne_zero [IsPreimmersion i] (n : ℕ)
    (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]} {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
    {V : (pullback πY g).IdealSheafData} (hV : IsImmersedHilbertFamily i hi Φ g V) (hΦ : Φ ≠ 0) :
    Surjective (V.subschemeι ≫ pullback.snd πY g) := by
  have := hV.isClosedImmersion
  rw [← map_immersionBaseChange_subschemeι_comp_snd_iff i hi g V @Surjective]
  exact hV.isHilbertFamily_map.surjective_of_ne_zero ι n e hΦ

variable (F : Set ℚ[X])

/-- **Points of the Hilbert functor of `Y` with Hilbert polynomials in `F`** (Nitsure,
arXiv:math/0504590v1, §1, pp. 3–4, for `L = i^* 𝒪(1)`): a closed subscheme
`V ⊆ Y ×_{Spec A} T` that is proper and flat over `T` and whose image `V.map i_T` in
`P^n_A ×_{Spec A} T` has fibre Hilbert polynomial in `F` at every point of `T`. -/
structure IsImmersedHilbertFamilyIn {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (V : (pullback πY g).IdealSheafData) : Prop where
  /-- `V` is proper over `T`. -/
  isProper : IsProper (V.subschemeι ≫ pullback.snd πY g)
  /-- `V` is flat over `T`. -/
  flat : Flat (V.subschemeι ≫ pullback.snd πY g)
  /-- The fibre Hilbert polynomials of the image of `V` in `P^n_A ×_{Spec A} T` lie in `F`. -/
  fiberHilbertPolynomialAt_mem (t : T) :
    fiberHilbertPolynomialAt ι g (V.map (immersionBaseChange i hi g)).quotientModule t ∈ F

namespace IsImmersedHilbertFamilyIn

variable {i hi F} {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  {V : (pullback πY g).IdealSheafData}

/-- A point with Hilbert polynomials in `F` is closed in `P^n_A ×_{Spec A} T`: it is proper over
`T`, and `P^n_A ×_{Spec A} T ⟶ T` is separated. -/
theorem isClosedImmersion [IsPreimmersion i] (hV : IsImmersedHilbertFamilyIn i hi F g V) :
    IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g) :=
  V.isClosedImmersion_subschemeι_comp_of_isProper (immersionBaseChange_snd i hi g) hV.isProper

/-- The image in `P^n_A ×_{Spec A} T` of a point with Hilbert polynomials in `F` is flat over
`T`: it is isomorphic over `T` to the point. -/
theorem flat_map [IsPreimmersion i] (hV : IsImmersedHilbertFamilyIn i hi F g V) :
    Flat ((V.map (immersionBaseChange i hi g)).subschemeι ≫ pullback.snd (toSpec A ι) g) := by
  have := hV.isClosedImmersion
  have := hV.flat
  -- Instance search does not find `RespectsIso @Flat` here (compare `flat_sigmaGlue`), so the
  -- isomorphism `V ≅ V.map i_T` over `T` is composed by hand.
  rw [(Iso.eq_inv_comp _).mpr (V.mapSubschemeIso_hom_subschemeι (immersionBaseChange i hi g)),
    Category.assoc, Category.assoc, immersionBaseChange_snd]
  infer_instance

/-- The image in `P^n_A ×_{Spec A} T` of a point with Hilbert polynomials in `F` is proper over
`T`. -/
theorem isProper_map [IsPreimmersion i] (hV : IsImmersedHilbertFamilyIn i hi F g V) :
    IsProper ((V.map (immersionBaseChange i hi g)).subschemeι ≫ pullback.snd (toSpec A ι) g) := by
  have := hV.isClosedImmersion
  exact (map_immersionBaseChange_subschemeι_comp_snd_iff i hi g V @IsProper).mpr hV.isProper

/-- **A point with constant Hilbert polynomial `Φ` is a point of `Hilb^Φ_Y`**: for finitely many
coordinates, a point with Hilbert polynomials in `F` whose fibre polynomials are all `Φ` is a point
of the Hilbert functor `immersedHilbertFunctor i hi Φ`. -/
theorem isImmersedHilbertFamily_of_fiberHilbertPolynomialAt_eq [IsPreimmersion i] [Finite ι]
    (hV : IsImmersedHilbertFamilyIn i hi F g V) {Φ : ℚ[X]}
    (hΦ : ∀ t, fiberHilbertPolynomialAt ι g (V.map (immersionBaseChange i hi g)).quotientModule t =
      Φ) :
    IsImmersedHilbertFamily i hi Φ g V :=
  ⟨hV.isProper, (isHilbertFamily_iff_fiberHilbertPolynomialAt ι).mpr ⟨hV.flat_map, hΦ⟩⟩

/-- **Base change of points with Hilbert polynomials in `F`**: for finitely many coordinates and
`f : T' ⟶ T` over `Spec A`, the pullback of such a point `V` along `Y_{T'} ⟶ Y_T` is such a point.
Properness and flatness are stable under base change; the image of the pullback is the pullback of
the image (`comap_baseChangeMap_map_immersionBaseChange`), whose fibre polynomial at `t'` is that of
the image at `f t'` (`fiberHilbertPolynomialAt_quotientModule_comap_baseChangeMap`). -/
theorem comap [IsPreimmersion i] [Finite ι] {T' : Scheme.{u}}
    {g' : T' ⟶ Spec (CommRingCat.of A)} (f : T' ⟶ T) (h : f ≫ g = g')
    (hV : IsImmersedHilbertFamilyIn i hi F g V) :
    IsImmersedHilbertFamilyIn i hi F g' (V.comap (pullback.map πY g' πY g (𝟙 Y) f (𝟙 _)
      (by simp) (by rw [Category.comp_id, h]))) where
  isProper := Scheme.IdealSheafData.comap_subschemeι_comp_of_isPullback @IsProper
    (Scheme.isPullback_pullbackMap_snd πY g g' f h) V hV.isProper
  flat := Scheme.IdealSheafData.comap_subschemeι_comp_of_isPullback @Flat
    (Scheme.isPullback_pullbackMap_snd πY g g' f h) V hV.flat
  fiberHilbertPolynomialAt_mem t' := by
    have := hV.isClosedImmersion
    rw [← comap_baseChangeMap_map_immersionBaseChange i hi g g' f h V,
      fiberHilbertPolynomialAt_quotientModule_comap_baseChangeMap]
    exact hV.fiberHilbertPolynomialAt_mem (f t')

variable (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- **A point with nonzero Hilbert polynomials covers its base** (Nitsure, arXiv:math/0504590v1,
proof of Thm 6.8, p. 33, "Hence p : D → H is surjective"): if `0 ∉ F`, a point with Hilbert
polynomials in `F` is surjective onto `T`, since its fibre polynomial at every point is nonzero
(`fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff`). -/
theorem surjective_of_zero_notMem [IsPreimmersion i] (hV : IsImmersedHilbertFamilyIn i hi F g V)
    (h0 : (0 : ℚ[X]) ∉ F) : Surjective (V.subschemeι ≫ pullback.snd πY g) := by
  have := hV.isClosedImmersion
  refine ⟨fun t => ?_⟩
  refine (fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff i hi g V n e t).mp ?_
  intro h
  exact h0 (h ▸ hV.fiberHilbertPolynomialAt_mem t)

end IsImmersedHilbertFamilyIn

variable {i hi F} in
/-- **A point of `Hilb^Φ_Y` with `Φ ∈ F` has Hilbert polynomials in `F`.** -/
theorem IsImmersedHilbertFamily.isImmersedHilbertFamilyIn_of_mem [IsPreimmersion i] [Finite ι]
    {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)} {V : (pullback πY g).IdealSheafData}
    {Φ : ℚ[X]} (hV : IsImmersedHilbertFamily i hi Φ g V) (hΦ : Φ ∈ F) :
    IsImmersedHilbertFamilyIn i hi F g V where
  isProper := hV.isProper
  flat := hV.flat
  fiberHilbertPolynomialAt_mem t := by
    rw [hV.isHilbertFamily_map.fiberHilbertPolynomialAt_quotientModule_eq ι t]
    exact hΦ

/-- **For a single polynomial the two Hilbert functors agree**: for finitely many coordinates, a
closed subscheme of `Y ×_{Spec A} T` is a point with Hilbert polynomials in `{Φ}` if and only if it
is a point of `Hilb^Φ_Y(T)`. -/
theorem isImmersedHilbertFamilyIn_singleton_iff [IsPreimmersion i] [Finite ι] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback πY g).IdealSheafData) (Φ : ℚ[X]) :
    IsImmersedHilbertFamilyIn i hi {Φ} g V ↔ IsImmersedHilbertFamily i hi Φ g V :=
  ⟨fun hV => hV.isImmersedHilbertFamily_of_fiberHilbertPolynomialAt_eq fun t =>
      hV.fiberHilbertPolynomialAt_mem t,
    fun hV => hV.isImmersedHilbertFamilyIn_of_mem (Set.mem_singleton Φ)⟩

section Range

variable {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback πY g).IdealSheafData)

/-- **The polynomials that occur**: a closed subscheme `V ⊆ Y ×_{Spec A} T` that is proper and flat
over `T` is a point with Hilbert polynomials in the set of fibre Hilbert polynomials of its image
in `P^n_A ×_{Spec A} T`. -/
theorem isImmersedHilbertFamilyIn_range_fiberHilbertPolynomialAt
    (hp : IsProper (V.subschemeι ≫ pullback.snd πY g))
    (hf : Flat (V.subschemeι ≫ pullback.snd πY g)) :
    IsImmersedHilbertFamilyIn i hi
      (Set.range (fiberHilbertPolynomialAt ι g (V.map (immersionBaseChange i hi g)).quotientModule))
      g V :=
  ⟨hp, hf, fun t => ⟨t, rfl⟩⟩

variable (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- **Only finitely many polynomials occur over a quasi-compact base** (Nitsure,
arXiv:math/0504590v1, proof of Thm 6.8, p. 33, "As the parameter scheme X is noetherian and as the
Hilbert polynomial is locally constant, only finitely many polynomials Φ occur"): for a
quasi-compact locally Noetherian `T`, the image of any closed `V ⊆ Y ×_{Spec A} T` has only
finitely many fibre Hilbert polynomials (`finite_range_fiberHilbertPolynomialAt`). -/
theorem finite_range_fiberHilbertPolynomialAt_map_immersionBaseChange [IsLocallyNoetherian T]
    [CompactSpace T] :
    (Set.range (fiberHilbertPolynomialAt ι g
      (V.map (immersionBaseChange i hi g)).quotientModule)).Finite := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact finite_range_fiberHilbertPolynomialAt ι g n e
    (V.map (immersionBaseChange i hi g)).affineLocallyFiniteType_quotientModule

include e in
/-- **No zero polynomial occurs exactly when the family covers its base** (Nitsure,
arXiv:math/0504590v1, proof of Thm 6.8, p. 33: the fibres of `f₂` are nonempty, "and therefore the
Hilbert polynomial of each fiber is non-zero"): if `V ⊆ Y ×_{Spec A} T` is closed in
`P^n_A ×_{Spec A} T`, then `0` is not a fibre Hilbert polynomial of its image if and only if
`V ⟶ T` is surjective (`fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff`). -/
theorem zero_notMem_range_fiberHilbertPolynomialAt_map_immersionBaseChange_iff
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g)] :
    (0 : ℚ[X]) ∉ Set.range
        (fiberHilbertPolynomialAt ι g (V.map (immersionBaseChange i hi g)).quotientModule) ↔
      Surjective (V.subschemeι ≫ pullback.snd πY g) := by
  rw [Set.mem_range, not_exists, surjective_iff]
  exact forall_congr' fun t =>
    fiberHilbertPolynomialAt_map_immersionBaseChange_ne_zero_iff i hi g V n e t

end Range

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
/-- **The Hilbert functor of an immersed scheme with Hilbert polynomials in `F`** (Nitsure,
arXiv:math/0504590v1, §1, pp. 3–4, for `L = i^* 𝒪(1)`), on all schemes `T` over `Spec A`: `T` goes
to the closed subschemes `V ⊆ Y ×_{Spec A} T` that are proper and flat over `T` and whose images in
`P^n_A ×_{Spec A} T` have all fibre Hilbert polynomials in `F`, and `f : T' ⟶ T` acts by pullback
along `pullback.map πY _ πY _ (𝟙 Y) f (𝟙 _)`. For `F` the set of all polynomials this is
Nitsure's `Hilb^L_{Y/S}`. -/
def immersedHilbertFunctorIn [IsPreimmersion i] [Finite ι] :
    (Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u where
  obj T := {V : (pullback πY T.unop.hom).IdealSheafData //
    IsImmersedHilbertFamilyIn i hi F T.unop.hom V}
  map {T T'} f := TypeCat.ofHom fun V =>
    ⟨V.1.comap (pullback.map πY T'.unop.hom πY T.unop.hom (𝟙 Y) f.unop.left (𝟙 _) (by simp)
        (by rw [Category.comp_id, Over.w f.unop])),
      V.2.comap f.unop.left (Over.w f.unop)⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun V => Subtype.ext ?_
    change V.1.comap (pullback.map πY _ πY _ (𝟙 Y) (𝟙 T.unop.left) (𝟙 _) _ _) = V.1
    rw [pullback.map_id, Scheme.IdealSheafData.comap_id]
  map_comp {T T' T''} f f' := by
    refine ConcreteCategory.hom_ext _ _ fun V => Subtype.ext ?_
    change V.1.comap (pullback.map πY _ πY _ (𝟙 Y) (f'.unop.left ≫ f.unop.left) (𝟙 _) _ _) =
      (V.1.comap (pullback.map πY _ πY _ (𝟙 Y) f.unop.left (𝟙 _) _ _)).comap
        (pullback.map πY _ πY _ (𝟙 Y) f'.unop.left (𝟙 _) _ _)
    rw [← Scheme.IdealSheafData.comap_comp]
    congr 1
    apply pullback.hom_ext <;> simp [pullback.map]

theorem immersedHilbertFunctorIn_map_coe [IsPreimmersion i] [Finite ι]
    {T T' : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (f : T ⟶ T')
    (V : (immersedHilbertFunctorIn i hi F).obj T) :
    ((immersedHilbertFunctorIn i hi F).map f V).1 =
      V.1.comap (pullback.map πY T'.unop.hom πY T.unop.hom (𝟙 Y) f.unop.left (𝟙 _) (by simp)
        (by rw [Category.comp_id, Over.w f.unop])) :=
  rfl

/-- The Hilbert functor of `Y` with Hilbert polynomials in `F` on locally Noetherian test schemes
over `Spec A`: the restriction of `immersedHilbertFunctorIn i hi F` along
`Scheme.locallyNoetherianOverInclusion`. -/
abbrev locallyNoetherianImmersedHilbertFunctorIn [IsPreimmersion i] [Finite ι] :
    (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u :=
  (Scheme.locallyNoetherianOverInclusion _).op ⋙ immersedHilbertFunctorIn i hi F

section Sigma

variable [IsPreimmersion i] {J : Type*} [Small.{u} J] {H : J → Scheme.{u}}
  (πH : ∀ j, H j ⟶ Spec (CommRingCat.of A))

/-- **The image of a family on `Y ×_{Spec A} ∐ H` restricted to a component**: for a closed
subscheme `V ⊆ Y ×_{Spec A} ∐ H` closed in `P^n_A ×_{Spec A} ∐ H`, the restriction of its image to
`P^n_A ×_{Spec A} H j` is the image of its restriction to `Y ×_{Spec A} H j`. -/
theorem comap_pullbackSigmaι_map_immersionBaseChange
    (V : (pullback πY (Sigma.desc πH)).IdealSheafData)
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi (Sigma.desc πH))] (j : J) :
    (V.map (immersionBaseChange i hi (Sigma.desc πH))).comap
        (Scheme.pullbackSigmaι (toSpec A ι) πH j) =
      (V.comap (Scheme.pullbackSigmaι πY πH j)).map (immersionBaseChange i hi (πH j)) := by
  rw [pullbackSigmaι_toSpec_eq_baseChangeMap,
    comap_baseChangeMap_map_immersionBaseChange i hi (Sigma.desc πH) (πH j) (Sigma.ι H j)
      (Sigma.ι_comp_desc _ _) V]
  rfl

variable [Finite ι] (D : ∀ j, (pullback πY (πH j)).IdealSheafData)

/-- **The glued image** (the image of the glued family is the glued family of the images): for a
preimmersion `i`, finitely many coordinates and families `D j ⊆ Y ×_{Spec A} H j` proper over
`H j`, the image in `P^n_A ×_{Spec A} ∐ H` of the glued family `sigmaGlue πY πH D` is the glued
family of the images `(D j).map i_{H j}` (`Scheme.IdealSheafData.eq_sigmaGlue_iff`). -/
theorem map_sigmaGlue_immersionBaseChange
    (hD : ∀ j, IsProper ((D j).subschemeι ≫ pullback.snd πY (πH j))) :
    (Scheme.IdealSheafData.sigmaGlue πY πH D).map (immersionBaseChange i hi (Sigma.desc πH)) =
      Scheme.IdealSheafData.sigmaGlue (toSpec A ι) πH
        fun j => (D j).map (immersionBaseChange i hi (πH j)) := by
  have := (isProper_subschemeι_comp_snd_iff_isClosedImmersion i hi (Sigma.desc πH) _).mp
    (Scheme.IdealSheafData.isProper_sigmaGlue πY πH D hD)
  rw [Scheme.IdealSheafData.eq_sigmaGlue_iff]
  intro j
  rw [comap_pullbackSigmaι_map_immersionBaseChange i hi πH
    (Scheme.IdealSheafData.sigmaGlue πY πH D) j, Scheme.IdealSheafData.comap_sigmaGlue]

variable {F} (Φ : J → ℚ[X])

/-- **The glued family of points of `Hilb^{Φ j}_Y` with `Φ j ∈ F` has Hilbert polynomials in
`F`**: for a preimmersion `i` and finitely many coordinates, if every `D j` is a point of
`Hilb^{Φ j}_Y(H j)` with `Φ j ∈ F`, the glued family `sigmaGlue πY πH D` is a point of the
Hilbert functor of `Y` with Hilbert polynomials in `F` at `∐ H`. Properness and flatness are local
on `∐ H` (`HilbertScheme/Coproduct/Family`); the image is the glued family of the images
(`map_sigmaGlue_immersionBaseChange`), with fibre polynomial `Φ j` on the `j`-th component
(`fiberHilbertPolynomialAt_sigmaGlue_sigmaι_of_isHilbertFamily`). -/
theorem isImmersedHilbertFamilyIn_sigmaGlue (hΦ : ∀ j, Φ j ∈ F)
    (hD : ∀ j, IsImmersedHilbertFamily i hi (Φ j) (πH j) (D j)) :
    IsImmersedHilbertFamilyIn i hi F (Sigma.desc πH) (Scheme.IdealSheafData.sigmaGlue πY πH D) where
  isProper := Scheme.IdealSheafData.isProper_sigmaGlue πY πH D fun j => (hD j).isProper
  flat := Scheme.IdealSheafData.flat_sigmaGlue πY πH D fun j => (hD j).flat
  fiberHilbertPolynomialAt_mem x := by
    rw [map_sigmaGlue_immersionBaseChange i hi πH D fun j => (hD j).isProper]
    obtain ⟨j, y, rfl⟩ := Scheme.exists_sigmaι_eq x
    rw [fiberHilbertPolynomialAt_sigmaGlue_sigmaι_of_isHilbertFamily ι πH
      (fun j => (D j).map (immersionBaseChange i hi (πH j))) Φ
      (fun j => (hD j).isHilbertFamily_map) j y]
    exact hΦ j

/-- **The pullback of a glued family detects the component**: for a preimmersion `i`, finitely
many coordinates, distinct polynomials `Φ j` and points `D j` of `Hilb^{Φ j}_Y(H j)`, the pullback
of the glued family along `a : T ⟶ ∐ H` over `Spec A` has image in `P^n_A ×_{Spec A} T` with fibre
polynomial `Φ j` at `t` exactly when `a t` lies in the `j`-th component
(`fiberHilbertPolynomialAt_sigmaGlue_comap_eq_iff`, through `map_sigmaGlue_immersionBaseChange`). -/
theorem fiberHilbertPolynomialAt_map_comap_sigmaGlue_eq_iff (hΦ : Function.Injective Φ)
    (hD : ∀ j, IsImmersedHilbertFamily i hi (Φ j) (πH j) (D j)) {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (a : T ⟶ ∐ H) (ha : a ≫ Sigma.desc πH = g) (t : T)
    (j : J) :
    fiberHilbertPolynomialAt ι g (((Scheme.IdealSheafData.sigmaGlue πY πH D).comap
        (pullback.map πY g πY (Sigma.desc πH) (𝟙 Y) a (𝟙 _) (by simp)
          (by rw [Category.comp_id, ha]))).map (immersionBaseChange i hi g)).quotientModule t =
        Φ j ↔
      a t ∈ Set.range (Sigma.ι H j) := by
  have := (isProper_subschemeι_comp_snd_iff_isClosedImmersion i hi (Sigma.desc πH) _).mp
    (Scheme.IdealSheafData.isProper_sigmaGlue πY πH D fun j => (hD j).isProper)
  rw [← comap_baseChangeMap_map_immersionBaseChange i hi (Sigma.desc πH) g a ha
      (Scheme.IdealSheafData.sigmaGlue πY πH D),
    map_sigmaGlue_immersionBaseChange i hi πH D fun j => (hD j).isProper]
  exact fiberHilbertPolynomialAt_sigmaGlue_comap_eq_iff ι πH
    (fun j => (D j).map (immersionBaseChange i hi (πH j))) Φ hΦ
    (fun j => (hD j).isHilbertFamily_map) g a ha t j

end Sigma

end AlgebraicGeometry.ProjectiveSpace

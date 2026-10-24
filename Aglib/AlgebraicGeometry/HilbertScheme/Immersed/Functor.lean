/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Functor
public import Aglib.AlgebraicGeometry.IdealSheaf.Monomorphism
public import Aglib.AlgebraicGeometry.Limits.FibreProductBaseChange
public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The Hilbert functor of an immersed scheme

Let `A` be a ring, `ι` a coordinate type, `Y` a scheme with `πY : Y ⟶ Spec A`, and
`i : Y ⟶ P^n_A = ProjectiveSpace A ι` a preimmersion over `Spec A` (`i ≫ toSpec A ι = πY`); for
an immersion `i`, `Y` is a locally closed subscheme of `P^n_A`. For `g : T ⟶ Spec A` write
`Y_T = Y ×_{Spec A} T` and `P_T = P^n_A ×_{Spec A} T`. The base change
`immersionBaseChange i hi g : Y_T ⟶ P_T` of `i` is Mathlib's over-category base change
`((Over.pullback g).map (Over.homMk i hi)).left` (`immersionBaseChange_eq_overPullbackMap`) and
Mathlib's `pullback.map` of `i` (`immersionBaseChange_eq_pullbackMap`). Its square over `i` is
cartesian (`isPullback_immersionBaseChange`, from `Scheme.isPullback_overPullbackMap`), so it is
again a preimmersion, an immersion or a closed immersion when `i` is one, and it is compatible with
base change along `f : T' ⟶ T` (`isPullback_immersionBaseChange_baseChangeMap`: the square formed
with `pullback.map πY _ πY _ (𝟙 Y) f (𝟙 _)` and `baseChangeMap` is cartesian; the square of
`Y_T ⟶ T` itself is `Scheme.isPullback_pullbackMap_snd`, `Limits/FibreProductBaseChange`).

* The comparison of closed subschemes: `isProper_subschemeι_comp_snd_iff_isClosedImmersion` (a
  closed `V ⊆ Y_T` is proper over `T` if and only if `V ⟶ P_T` is a closed immersion) and
  `properClosedSubschemeEquiv` (`V ↦ V.map i_T` is a bijection onto the closed subschemes of
  `P_T` that factor through `i_T`, with inverse `W ↦ W.comap i_T`), for `[IsPreimmersion i]` and
  `[Finite ι]`; `comap_baseChangeMap_map_immersionBaseChange` (for `[IsPreimmersion i]`) and
  `comap_pullbackMap_comap_immersionBaseChange` (for any `i`): both maps commute with base change
  along `f : T' ⟶ T`.
* `IsImmersedHilbertFamily i hi Φ g V`: a closed subscheme `V ⊆ Y_T` that is proper over `T` and
  whose image `V.map i_T` in `P_T` is a point of `hilbertFunctor ι Φ` (`IsHilbertFamily`: flat
  over `T`, all fibre Hilbert polynomials `Φ`). Such a `V` is closed in `P_T`
  (`IsImmersedHilbertFamily.isClosedImmersion`; `P_T ⟶ T` is separated), hence isomorphic over
  `P_T` to its image, and flat over `T` (`IsImmersedHilbertFamily.flat`). The condition is stable
  under base change (`IsImmersedHilbertFamily.comap`).
* `immersedHilbertFunctor i hi Φ`: the functor `T ↦ {V | IsImmersedHilbertFamily i hi Φ T V}` on
  all schemes over `Spec A`, acting by pullback along the maps
  `pullback.map πY _ πY _ (𝟙 Y) f (𝟙 _)` of the fibre products `Y_T` (the maps of
  `RelativePicard.familyScheme πY`). This is Nitsure's
  Hilbert functor `Hilb^{Φ,L}_{Y/S}` (*Construction of Hilbert and Quot schemes*,
  arXiv:math/0504590v1, §1, pp. 3–4: closed subschemes of `Y_T` that are proper and flat over
  `T`, with the fibre Hilbert polynomials taken for `L`) for `L = i^* 𝒪(1)`, the setting of
  Thm 6.1 (p. 28) with `E = 𝒪` and trivial bundles: the fibre polynomials are those of the images
  of the fibres in `P^n_K`, which is how this definition expresses `L`. Nitsure's statements
  restrict it to locally Noetherian test schemes (`locallyNoetherianImmersedHilbertFunctor`).
* `immersedHilbertSubfunctor i hi Φ`: the subfunctor of `hilbertFunctor ι Φ` of the families
  `W ⊆ P_T` whose inclusion factors through `i_T`, for any morphism `i` over `Spec A`.
* `immersedHilbertFunctorIso i hi Φ` (`[Finite ι]`): the two are isomorphic, by `V ↦ V.map i_T`
  with inverse `W ↦ W.comap i_T` (`Scheme.IdealSheafData.mapEquivOfMono`,
  `IdealSheaf/Monomorphism`), naturally in `T` (`Scheme.IdealSheafData.map_comap_of_isPullback`).
  The closed subschemes of `Y_T` that are proper over `T` are exactly those that are closed in
  `P_T` (`Scheme.IdealSheafData.isProper_subschemeι_comp_iff_isClosedImmersion`, for the proper
  projection `P_T ⟶ T`).
* `isImmersedHilbertFamily_iff_of_isClosedImmersion` (`[Finite ι]`): for a closed immersion `i`
  the properness condition is automatic.

Nitsure uses this identification only implicitly and in two steps: for a closed `X ⊆ P(V)` he
regards the Quot functor on `X` as a subfunctor of that on `P(V)` (p. 25, after Lemma 5.4), and
for an open `X ⊆ Z` with `Z` proper he regards `Quot_{E|_X/X/S}` as a subfunctor of
`Quot_{E/Z/S}` (the second Exercise on p. 28). His proof of Thm 6.1 (p. 28) combines them through a
prolongation `Ē` of `E` to the schematic closure `X'` of `X` and applies Thm 5.2 to `X'`.
Stating the identification in one step along the immersion `i_T`, for every `T`, is a route choice.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {ι : Type u} {A : Type u} [CommRing A] {Y : Scheme.{u}}
  {πY : Y ⟶ Spec (CommRingCat.of A)} (i : Y ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πY)

section BaseChange

/-- The base change `i_T : Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T` of a morphism `i : Y ⟶ P^n_A`
over `Spec A` along `g : T ⟶ Spec A`. -/
def immersionBaseChange {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) :
    pullback πY g ⟶ pullback (toSpec A ι) g :=
  pullback.lift (pullback.fst πY g ≫ i) (pullback.snd πY g) (by
    rw [Category.assoc, hi, pullback.condition])

@[reassoc (attr := simp)]
theorem immersionBaseChange_fst {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) :
    immersionBaseChange i hi g ≫ pullback.fst (toSpec A ι) g = pullback.fst πY g ≫ i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem immersionBaseChange_snd {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) :
    immersionBaseChange i hi g ≫ pullback.snd (toSpec A ι) g = pullback.snd πY g :=
  pullback.lift_snd _ _ _

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
/-- `i_T` is Mathlib's `pullback.map` of `i` over the identity of `T`. -/
theorem immersionBaseChange_eq_pullbackMap {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) :
    immersionBaseChange i hi g = pullback.map πY g (toSpec A ι) g i (𝟙 T) (𝟙 _)
      (by rw [Category.comp_id, hi]) (by simp) := by
  apply pullback.hom_ext <;> simp [pullback.map]

/-- `i_T` is Mathlib's over-category base change of `i`, viewed as a morphism
`Over.mk πY ⟶ Over.mk (toSpec A ι)` over `Spec A`, along `g`. -/
theorem immersionBaseChange_eq_overPullbackMap {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) :
    immersionBaseChange i hi g = ((Over.pullback g).map
      (Over.homMk (U := Over.mk πY) (V := Over.mk (toSpec A ι)) i hi)).left :=
  rfl

/-- **`i_T` is the base change of `i`**: the square formed by
`Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T` and `i : Y ⟶ P^n_A` is cartesian
(`Scheme.isPullback_overPullbackMap`). -/
theorem isPullback_immersionBaseChange {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) :
    IsPullback (immersionBaseChange i hi g) (pullback.fst πY g) (pullback.fst (toSpec A ι) g)
      i := by
  rw [immersionBaseChange_eq_overPullbackMap]
  exact (Scheme.isPullback_overPullbackMap g
    (Over.homMk (U := Over.mk πY) (V := Over.mk (toSpec A ι)) i hi)).flip

instance isPreimmersion_immersionBaseChange [IsPreimmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) : IsPreimmersion (immersionBaseChange i hi g) :=
  MorphismProperty.of_isPullback (isPullback_immersionBaseChange i hi g).flip ‹_›

instance isImmersion_immersionBaseChange [IsImmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) : IsImmersion (immersionBaseChange i hi g) :=
  MorphismProperty.of_isPullback (isPullback_immersionBaseChange i hi g).flip ‹_›

instance isClosedImmersion_immersionBaseChange [IsClosedImmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) : IsClosedImmersion (immersionBaseChange i hi g) :=
  MorphismProperty.of_isPullback (isPullback_immersionBaseChange i hi g).flip ‹_›

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
/-- **`i_T` is compatible with base change**: for `f : T' ⟶ T` over `Spec A`, the square formed by
`i_{T'}`, `i_T`, the map `pullback.map πY _ πY _ (𝟙 Y) f (𝟙 _) : Y_{T'} ⟶ Y_T` and
`baseChangeMap ι g g' f h : P_{T'} ⟶ P_T` is cartesian. -/
theorem isPullback_immersionBaseChange_baseChangeMap {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (h : f ≫ g = g') :
    IsPullback (immersionBaseChange i hi g')
      (pullback.map πY g' πY g (𝟙 Y) f (𝟙 _) (by simp) (by rw [Category.comp_id, h]))
      (baseChangeMap ι g g' f h) (immersionBaseChange i hi g) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_baseChangeMap ι g g' f h).flip
  · rw [immersionBaseChange_snd, immersionBaseChange_snd]
    exact (Scheme.isPullback_pullbackMap_snd πY g g' f h).flip
  · apply pullback.hom_ext <;> simp [pullback.map]

end BaseChange

section ClosedSubschemes

/-- **Proper closed subschemes of `Y_T` are the closed subschemes closed in `P_T`**: for a
preimmersion `i` and finitely many coordinates, a closed subscheme `V ⊆ Y ×_{Spec A} T` is proper
over `T` if and only if `V ⟶ Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T` is a closed immersion
(`Scheme.IdealSheafData.isProper_subschemeι_comp_iff_isClosedImmersion` for the proper
projection `P^n_A ×_{Spec A} T ⟶ T`). -/
theorem isProper_subschemeι_comp_snd_iff_isClosedImmersion [IsPreimmersion i] [Finite ι]
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback πY g).IdealSheafData) :
    IsProper (V.subschemeι ≫ pullback.snd πY g) ↔
      IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g) :=
  V.isProper_subschemeι_comp_iff_isClosedImmersion (immersionBaseChange_snd i hi g)

/-- **Closed subschemes of `Y_T` proper over `T` and closed subschemes of `P_T` in `Y_T`**: for a
preimmersion `i` and finitely many coordinates, `V ↦ V.map i_T` (the kernel of
`V ⟶ P^n_A ×_{Spec A} T`) is a bijection from the closed subschemes of `Y ×_{Spec A} T` that are
proper over `T` onto the closed subschemes of `P^n_A ×_{Spec A} T` whose inclusion factors through
`i_T`, with inverse `W ↦ W.comap i_T` (`Scheme.IdealSheafData.mapEquivOfMono`). -/
def properClosedSubschemeEquiv [IsPreimmersion i] [Finite ι] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) :
    {V : (pullback πY g).IdealSheafData // IsProper (V.subschemeι ≫ pullback.snd πY g)} ≃
      {W : (pullback (toSpec A ι) g).IdealSheafData //
        ∃ w : W.subscheme ⟶ pullback πY g, w ≫ immersionBaseChange i hi g = W.subschemeι} :=
  (Equiv.subtypeEquivRight fun V =>
    isProper_subschemeι_comp_snd_iff_isClosedImmersion i hi g V).trans
      (Scheme.IdealSheafData.mapEquivOfMono _)

@[simp]
theorem properClosedSubschemeEquiv_apply_coe [IsPreimmersion i] [Finite ι] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (V : {V : (pullback πY g).IdealSheafData // IsProper (V.subschemeι ≫ pullback.snd πY g)}) :
    (properClosedSubschemeEquiv i hi g V).1 = V.1.map (immersionBaseChange i hi g) :=
  rfl

@[simp]
theorem properClosedSubschemeEquiv_symm_apply_coe [IsPreimmersion i] [Finite ι] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (W : {W : (pullback (toSpec A ι) g).IdealSheafData //
      ∃ w : W.subscheme ⟶ pullback πY g, w ≫ immersionBaseChange i hi g = W.subschemeι}) :
    ((properClosedSubschemeEquiv i hi g).symm W).1 = W.1.comap (immersionBaseChange i hi g) :=
  rfl

/-- **The image commutes with base change**: for `f : T' ⟶ T` over `Spec A` and a closed
subscheme `V ⊆ Y ×_{Spec A} T` closed in `P^n_A ×_{Spec A} T`, the pullback of its image along
`baseChangeMap` is the image of its pullback along `Y_{T'} ⟶ Y_T`. -/
theorem comap_baseChangeMap_map_immersionBaseChange [IsPreimmersion i] {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (h : f ≫ g = g') (V : (pullback πY g).IdealSheafData)
    [IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g)] :
    (V.map (immersionBaseChange i hi g)).comap (baseChangeMap ι g g' f h) =
      (V.comap (pullback.map πY g' πY g (𝟙 Y) f (𝟙 _) (by simp)
        (by rw [Category.comp_id, h]))).map (immersionBaseChange i hi g') :=
  Scheme.IdealSheafData.map_comap_of_isPullback
    (isPullback_immersionBaseChange_baseChangeMap i hi g g' f h) V

/-- **The pullback to `Y_T` commutes with base change**: for `f : T' ⟶ T` over `Spec A` and any
closed subscheme `W ⊆ P^n_A ×_{Spec A} T`, pulling back to `Y ×_{Spec A} T` and then along
`Y_{T'} ⟶ Y_T` is pulling back along `baseChangeMap` and then to `Y ×_{Spec A} T'`. -/
theorem comap_pullbackMap_comap_immersionBaseChange {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (h : f ≫ g = g') (W : (pullback (toSpec A ι) g).IdealSheafData) :
    (W.comap (immersionBaseChange i hi g)).comap
        (pullback.map πY g' πY g (𝟙 Y) f (𝟙 _) (by simp) (by rw [Category.comp_id, h])) =
      (W.comap (baseChangeMap ι g g' f h)).comap (immersionBaseChange i hi g') := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    (isPullback_immersionBaseChange_baseChangeMap i hi g g' f h).w]

end ClosedSubschemes

variable (Φ : ℚ[X])

/-- **Points of the Hilbert functor of an immersed scheme** (Nitsure, arXiv:math/0504590v1, §1,
pp. 3–4, with `L = i^* 𝒪(1)`): a closed subscheme `V ⊆ Y ×_{Spec A} T` that is proper over `T`
and whose image `V.map i_T` in `P^n_A ×_{Spec A} T` is flat over `T` with all fibre Hilbert
polynomials `Φ`. -/
structure IsImmersedHilbertFamily {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (V : (pullback πY g).IdealSheafData) : Prop where
  /-- `V` is proper over `T`. -/
  isProper : IsProper (V.subschemeι ≫ pullback.snd πY g)
  /-- The image of `V` in `P^n_A ×_{Spec A} T` is a point of `Hilb^Φ(T)`. -/
  isHilbertFamily_map : IsHilbertFamily ι Φ g (V.map (immersionBaseChange i hi g))

namespace IsImmersedHilbertFamily

variable {i hi Φ} {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  {V : (pullback πY g).IdealSheafData}

/-- **A point of the Hilbert functor of `Y` is closed in `P^n_A ×_{Spec A} T`**: it is proper over
`T`, and `P^n_A ×_{Spec A} T ⟶ T` is separated. -/
theorem isClosedImmersion [IsPreimmersion i] (hV : IsImmersedHilbertFamily i hi Φ g V) :
    IsClosedImmersion (V.subschemeι ≫ immersionBaseChange i hi g) :=
  V.isClosedImmersion_subschemeι_comp_of_isProper (immersionBaseChange_snd i hi g) hV.isProper

/-- **A point of the Hilbert functor of `Y` is flat over `T`**: it is isomorphic over `T` to its
image in `P^n_A ×_{Spec A} T`, which is flat over `T`. -/
theorem flat [IsPreimmersion i] (hV : IsImmersedHilbertFamily i hi Φ g V) :
    Flat (V.subschemeι ≫ pullback.snd πY g) := by
  have := hV.isClosedImmersion
  have := hV.isHilbertFamily_map.flat
  rw [← immersionBaseChange_snd i hi g, ← V.mapSubschemeIso_hom_subschemeι_assoc]
  infer_instance

/-- **Base change of points**: for `f : T' ⟶ T` over `Spec A`, the pullback of a point `V` of the
Hilbert functor of `Y` along `Y_{T'} ⟶ Y_T` is a point. Properness is stable under base change,
and the image of the pullback is the pullback of the image
(`Scheme.IdealSheafData.map_comap_of_isPullback`), a point of `Hilb^Φ(T')` by
`IsHilbertFamily.comap`. -/
theorem comap [IsPreimmersion i] {T' : Scheme.{u}} {g' : T' ⟶ Spec (CommRingCat.of A)}
    (f : T' ⟶ T) (h : f ≫ g = g') (hV : IsImmersedHilbertFamily i hi Φ g V) :
    IsImmersedHilbertFamily i hi Φ g' (V.comap (pullback.map πY g' πY g (𝟙 Y) f (𝟙 _) (by simp)
      (by rw [Category.comp_id, h]))) where
  isProper := Scheme.IdealSheafData.comap_subschemeι_comp_of_isPullback @IsProper
    (Scheme.isPullback_pullbackMap_snd πY g g' f h) V hV.isProper
  isHilbertFamily_map := by
    have := hV.isClosedImmersion
    rw [← Scheme.IdealSheafData.map_comap_of_isPullback
      (isPullback_immersionBaseChange_baseChangeMap i hi g g' f h) V]
    exact hV.isHilbertFamily_map.comap ι f h

end IsImmersedHilbertFamily

/-- **Closed subschemes of a closed subscheme**: for a closed immersion `i` and finitely many
coordinates, every closed subscheme of `Y ×_{Spec A} T` is proper over `T`, so a point of the
Hilbert functor of `Y` is a closed subscheme whose image is a point of `Hilb^Φ(T)`. -/
theorem isImmersedHilbertFamily_iff_of_isClosedImmersion [IsClosedImmersion i] [Finite ι]
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback πY g).IdealSheafData) :
    IsImmersedHilbertFamily i hi Φ g V ↔
      IsHilbertFamily ι Φ g (V.map (immersionBaseChange i hi g)) :=
  ⟨fun hV => hV.isHilbertFamily_map, fun hV =>
    ⟨(V.isProper_subschemeι_comp_iff_isClosedImmersion (immersionBaseChange_snd i hi g)).mpr
      inferInstance, hV⟩⟩

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
/-- **The Hilbert functor of an immersed scheme** `Hilb^{Φ,L}_{Y/S}` (Nitsure,
arXiv:math/0504590v1, §1, pp. 3–4, for `L = i^* 𝒪(1)`; Thm 6.1, p. 28), on all schemes `T` over
`Spec A`: `T` goes to the closed subschemes `V ⊆ Y ×_{Spec A} T` that are proper over `T` and whose
image in `P^n_A ×_{Spec A} T` is flat over `T` with all fibre Hilbert polynomials `Φ`, and
`f : T' ⟶ T` acts by pullback along `pullback.map πY _ πY _ (𝟙 Y) f (𝟙 _)`. Here `i` is a
preimmersion, for example an immersion; Nitsure's representability statements concern locally
Noetherian `T`. -/
def immersedHilbertFunctor [IsPreimmersion i] :
    (Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u where
  obj T := {V : (pullback πY T.unop.hom).IdealSheafData //
    IsImmersedHilbertFamily i hi Φ T.unop.hom V}
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

theorem immersedHilbertFunctor_map_coe [IsPreimmersion i]
    {T T' : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (f : T ⟶ T')
    (V : (immersedHilbertFunctor i hi Φ).obj T) :
    ((immersedHilbertFunctor i hi Φ).map f V).1 =
      V.1.comap (pullback.map πY T'.unop.hom πY T.unop.hom (𝟙 Y) f.unop.left (𝟙 _) (by simp)
        (by rw [Category.comp_id, Over.w f.unop])) :=
  rfl

/-- The Hilbert functor of an immersed scheme on locally Noetherian test schemes over `Spec A`:
the restriction of `immersedHilbertFunctor i hi Φ` along `Scheme.locallyNoetherianOverInclusion`. -/
abbrev locallyNoetherianImmersedHilbertFunctor [IsPreimmersion i] :
    (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u :=
  (Scheme.locallyNoetherianOverInclusion _).op ⋙ immersedHilbertFunctor i hi Φ

/-- **The families of `Hilb^Φ` contained in `Y`**: the subfunctor of `hilbertFunctor ι Φ` of the
closed subschemes `W ⊆ P^n_A ×_{Spec A} T` whose inclusion factors through
`i_T : Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T`. It is a subfunctor for any morphism `i` over
`Spec A`, because `i_{T'}` is the base change of `i_T`
(`isPullback_immersionBaseChange_baseChangeMap`). -/
def immersedHilbertSubfunctor : Subfunctor (hilbertFunctor (A := A) ι Φ) where
  obj T := {W | ∃ w : W.1.subscheme ⟶ pullback πY T.unop.hom,
    w ≫ immersionBaseChange i hi T.unop.hom = W.1.subschemeι}
  map {T T'} f W hW := by
    obtain ⟨w, hw⟩ := hW
    exact Scheme.IdealSheafData.exists_lift_comap_subschemeι_of_isPullback
      (isPullback_immersionBaseChange_baseChangeMap i hi T.unop.hom T'.unop.hom f.unop.left
        (Over.w f.unop)) W.1 w hw

theorem mem_immersedHilbertSubfunctor_obj {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ}
    (W : (hilbertFunctor ι Φ).obj T) :
    W ∈ (immersedHilbertSubfunctor i hi Φ).obj T ↔ ∃ w : W.1.subscheme ⟶ pullback πY T.unop.hom,
      w ≫ immersionBaseChange i hi T.unop.hom = W.1.subschemeι :=
  Iff.rfl

section Iso

variable [IsPreimmersion i] [Finite ι]

/-- The component at `T` of `immersedHilbertFunctorIso`: a point `V` goes to its image
`V.map i_T`, and a family `W` contained in `Y` goes to `W.comap i_T`
(`Scheme.IdealSheafData.mapEquivOfMono`). -/
def immersedHilbertFunctorObjEquiv (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ) :
    (immersedHilbertFunctor i hi Φ).obj T ≃ (immersedHilbertSubfunctor i hi Φ).toFunctor.obj T where
  toFun V :=
    haveI := V.2.isClosedImmersion
    ⟨⟨V.1.map (immersionBaseChange i hi T.unop.hom), V.2.isHilbertFamily_map⟩,
      V.1.exists_lift_map_subschemeι _⟩
  invFun W :=
    ⟨W.1.1.comap (immersionBaseChange i hi T.unop.hom), by
      obtain ⟨w, hw⟩ := W.2
      have := W.1.1.isClosedImmersion_comap_subschemeι_comp _ w hw
      refine ⟨(Scheme.IdealSheafData.isProper_subschemeι_comp_iff_isClosedImmersion _
        (immersionBaseChange_snd i hi T.unop.hom)).mpr this, ?_⟩
      rw [Scheme.IdealSheafData.map_comap_of_comp_eq _ _ w hw]
      exact W.1.2⟩
  left_inv V := by
    have := V.2.isClosedImmersion
    exact Subtype.ext (Scheme.IdealSheafData.comap_map_of_mono_of_isClosedImmersion V.1 _)
  right_inv W := by
    obtain ⟨w, hw⟩ := W.2
    exact Subtype.ext (Subtype.ext (Scheme.IdealSheafData.map_comap_of_comp_eq W.1.1 _ w hw))

/-- **The Hilbert functor of an immersed scheme is the subfunctor of families in `Y`**: for a
preimmersion `i : Y ⟶ P^n_A` over `Spec A` and finitely many coordinates, `V ↦ V.map i_T` is a
natural isomorphism from `immersedHilbertFunctor i hi Φ` (closed subschemes of `Y ×_{Spec A} T`
proper over `T`) onto the subfunctor of `hilbertFunctor ι Φ` of the families that factor through
`i_T`, with inverse `W ↦ W.comap i_T`. Nitsure uses this identification implicitly, for closed
and for open subschemes separately (arXiv:math/0504590v1, p. 25 after Lemma 5.4, and the second
Exercise on p. 28); the one-step comparison along `i_T` is a route choice (see the module
docstring). -/
def immersedHilbertFunctorIso :
    immersedHilbertFunctor i hi Φ ≅ (immersedHilbertSubfunctor i hi Φ).toFunctor :=
  NatIso.ofComponents (fun T => (immersedHilbertFunctorObjEquiv i hi Φ T).toIso) fun {T T'} f => by
    refine ConcreteCategory.hom_ext _ _ fun V => Subtype.ext (Subtype.ext ?_)
    have := V.2.isClosedImmersion
    exact (Scheme.IdealSheafData.map_comap_of_isPullback
      (isPullback_immersionBaseChange_baseChangeMap i hi T.unop.hom T'.unop.hom f.unop.left
        (Over.w f.unop)) V.1).symm

theorem immersedHilbertFunctorIso_hom_app_coe (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ)
    (V : (immersedHilbertFunctor i hi Φ).obj T) :
    ((immersedHilbertFunctorIso i hi Φ).hom.app T V).1.1 =
      V.1.map (immersionBaseChange i hi T.unop.hom) :=
  rfl

theorem immersedHilbertFunctorIso_inv_app_coe (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ)
    (W : (immersedHilbertSubfunctor i hi Φ).toFunctor.obj T) :
    ((immersedHilbertFunctorIso i hi Φ).inv.app T W).1 =
      W.1.1.comap (immersionBaseChange i hi T.unop.hom) :=
  rfl

end Iso

end AlgebraicGeometry.ProjectiveSpace

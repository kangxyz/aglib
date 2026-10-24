/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.MonoFactor
public import Aglib.AlgebraicGeometry.IdealSheaf.Comap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Closed subschemes along a monomorphism

Let `j : X ⟶ Y` be a monomorphism of schemes, for example an immersion. A closed subscheme `I` of
`X` whose composite `I.subscheme ⟶ X ⟶ Y` is a closed immersion is the same thing as a closed
subscheme of `Y` that factors through `j`. In terms of Mathlib's pushforward
`IdealSheafData.map` (the kernel of `I.subscheme ⟶ X ⟶ Y`, so the scheme-theoretic image) and
pullback `IdealSheafData.comap`:

* `ker_comap_of_mono` (`IdealSheaf/Closed/MonoFactor`): for `z : Z ⟶ X` with `z ≫ j` a closed
  immersion, `(z ≫ j).ker.comap j = z.ker`; everything below builds on it;
* `comap_map_of_mono_of_isClosedImmersion`: `(I.map j).comap j = I` when `I.subscheme ⟶ Y` is a
  closed immersion. It generalizes `comap_map_of_isClosedImmersion`
  (`IdealSheaf/ClosedExtension`, `j` a closed immersion); for a quasi-compact open immersion `j`
  and any `I` the same equation is `comap_map_of_isOpenImmersion` (`IdealSheaf/OpenExtension`).
  `exists_lift_map_subschemeι`: then `I.map j` factors through `j`; `mapSubschemeIso` is the
  isomorphism `I.subscheme ≅ (I.map j).subscheme` over `Y` (`mapSubschemeIso_hom_subschemeι`),
  which transfers isomorphism-invariant properties such as flatness over a base between the two;
* `comap_eq_ker_of_comp_eq`, `map_comap_of_comp_eq` and
  `isClosedImmersion_comap_subschemeι_comp`: for a closed subscheme `J` of `Y` with
  `J.subschemeι = w ≫ j`, `J.comap j = w.ker`, `(J.comap j).map j = J` (for this one `j` need not
  be a monomorphism) and `J.comap j ⟶ X ⟶ Y` is a closed immersion;
* `mapEquivOfMono j`: hence `I ↦ I.map j` and `J ↦ J.comap j` are inverse bijections between the
  closed subschemes of `X` that are closed in `Y` and the closed subschemes of `Y` that factor
  through `j`. The closedness condition cannot be dropped: `(I.map j).comap j = I` can fail for an
  open immersion `j` that is not quasi-compact (the example in the docstring of
  `IdealSheaf/Glue`, checked by hand there);
* `comap_subschemeι_comp_of_isPullback`: a property stable under base change (properness,
  flatness, being a closed immersion) of `I.subscheme ⟶ X₁ ⟶ T₁` passes to
  `(I.comap a).subscheme ⟶ X₂ ⟶ T₂` for a cartesian square `a ≫ p₁ = p₂ ≫ f`;
* `exists_lift_comap_subschemeι_of_isPullback`, `map_comap_of_isPullback` and
  `isClosedImmersion_comap_subschemeι_comp_of_isPullback`: both maps commute with pullback along a
  cartesian square `j₂ ≫ b = a ≫ j₁` (the pullback along `a` and `b` respectively; for `comap`
  this is `comap_comp` and needs only commutativity). Only `map_comap_of_isPullback` needs `j₁` to
  be a monomorphism;
* `isClosedImmersion_subschemeι_comp_of_isProper` and
  `isProper_subschemeι_comp_iff_isClosedImmersion`: if `j` is a preimmersion (for example an
  immersion) and `q : Y ⟶ T` is separated, a closed subscheme `I` of `X` that is proper over `T`
  is closed in `Y`; if `q` is proper, `I` is proper over `T` if and only if `I.subscheme ⟶ Y` is a
  closed immersion. The proof is Mathlib's `IsProper.of_comp` (Mathlib's attribution: Stacks,
  Tag 01W6, (2)) and `IsClosedImmersion.of_isPreimmersion`, for the closed image of a universally
  closed morphism; `Scheme.isClosedImmersion_of_immersion_over_proper` (`Morphisms/Proper/Over`)
  is the same argument for immersions in `Over S`. For a monomorphism `j` the same equivalence
  follows from Mathlib's `IsClosedImmersion.iff_isProper_and_mono` (Stacks, Tag 04XV), which is
  not imported here.

The main application is the Hilbert functor of a locally closed subscheme `Y ⊆ P` over `S`: for
an `S`-scheme `T` and the immersion `j = i_T : Y_T ⟶ P_T`, the closed subschemes of `Y_T` that
are proper over `T`, as in Nitsure's definition of `Hilb_{Y/S}` (*Construction of Hilbert and Quot
schemes*, arXiv:math/0504590v1, §1, pp. 3–4), are the closed subschemes of `P_T` that lie in
`Y_T` (`HilbertScheme/Immersed/Functor`). Nitsure uses this identification implicitly,
separately for closed subschemes (p. 25, after Lemma 5.4) and for open subschemes of a proper `Z`
(the second Exercise on p. 28), and proves Thm 6.1 (p. 28) through a prolongation `Ē` on the
schematic closure `X'` of `X`; the one-step comparison along an immersion is a route choice.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y Z T : Scheme.{u}}

/-- The pullback of a monomorphism `j` along a morphism that factors through `j` is an
isomorphism. -/
private lemma isIso_pullback_snd_of_comp_eq (j : X ⟶ Y) [Mono j] {g : Z ⟶ Y} (w : Z ⟶ X)
    (hw : w ≫ j = g) : IsIso (pullback.snd j g) := by
  subst hw
  infer_instance

/-- For a monomorphism `j` and a closed subscheme `I` of `X` that is closed in `Y`, the pullback
along `j` of the image `I.map j` is `I`. For a closed immersion `j` this is
`comap_map_of_isClosedImmersion`. -/
theorem comap_map_of_mono_of_isClosedImmersion (I : X.IdealSheafData) (j : X ⟶ Y) [Mono j]
    [IsClosedImmersion (I.subschemeι ≫ j)] : (I.map j).comap j = I := by
  change (I.subschemeι ≫ j).ker.comap j = I
  rw [ker_comap_of_mono, ker_subschemeι]

/-- A closed subscheme `I` of `X` that is closed in `Y` is isomorphic over `Y` to its image
`I.map j`. -/
def mapSubschemeIso (I : X.IdealSheafData) (j : X ⟶ Y) [IsClosedImmersion (I.subschemeι ≫ j)] :
    I.subscheme ≅ (I.map j).subscheme :=
  (asIso (I.subschemeι ≫ j).toImage : I.subscheme ≅ (I.subschemeι ≫ j).image)

@[reassoc (attr := simp)]
theorem mapSubschemeIso_hom_subschemeι (I : X.IdealSheafData) (j : X ⟶ Y)
    [IsClosedImmersion (I.subschemeι ≫ j)] :
    (I.mapSubschemeIso j).hom ≫ (I.map j).subschemeι = I.subschemeι ≫ j :=
  (I.subschemeι ≫ j).toImage_imageι

/-- The image `I.map j` of a closed subscheme `I` of `X` that is closed in `Y` factors through
`j`. -/
theorem exists_lift_map_subschemeι (I : X.IdealSheafData) (j : X ⟶ Y)
    [IsClosedImmersion (I.subschemeι ≫ j)] :
    ∃ w : (I.map j).subscheme ⟶ X, w ≫ j = (I.map j).subschemeι :=
  ⟨(I.mapSubschemeIso j).inv ≫ I.subschemeι, by
    rw [Category.assoc, Iso.inv_comp_eq, mapSubschemeIso_hom_subschemeι]⟩

/-- For a monomorphism `j` and a closed subscheme `J` of `Y` with `J.subschemeι = w ≫ j`, the
pullback of `J` along `j` is the closed subscheme `w` of `X`. -/
theorem comap_eq_ker_of_comp_eq (J : Y.IdealSheafData) (j : X ⟶ Y) [Mono j]
    (w : J.subscheme ⟶ X) (hw : w ≫ j = J.subschemeι) : J.comap j = w.ker := by
  have : IsClosedImmersion (w ≫ j) := by
    rw [hw]
    infer_instance
  calc J.comap j = (w ≫ j).ker.comap j := by rw [hw, ker_subschemeι]
    _ = w.ker := ker_comap_of_mono w j

/-- For a closed subscheme `J` of `Y` that factors through `j`, the image of the pullback
`J.comap j` is `J`. No monomorphism hypothesis is needed: `pullback.lift w (𝟙 _)` is a section of
the second projection `pullback j J.subschemeι ⟶ J.subscheme`, so the kernel of
`J.comap j ⟶ Y` is contained in `J`, and the other inclusion is `le_map_comap`. -/
theorem map_comap_of_comp_eq (J : Y.IdealSheafData) (j : X ⟶ Y) (w : J.subscheme ⟶ X)
    (hw : w ≫ j = J.subschemeι) : (J.comap j).map j = J := by
  refine le_antisymm ?_ (le_map_comap J j)
  change ((J.comap j).subschemeι ≫ j).ker ≤ J
  rw [← comapIso_hom_fst, Category.assoc, pullback.condition, Hom.ker_comp_of_isIso]
  calc (pullback.snd j J.subschemeι ≫ J.subschemeι).ker
      ≤ (pullback.lift w (𝟙 _) (by rw [hw, Category.id_comp]) ≫
          pullback.snd j J.subschemeι ≫ J.subschemeι).ker := Hom.le_ker_comp _ _
    _ = J := by rw [pullback.lift_snd_assoc, Category.id_comp, ker_subschemeι]

/-- For a monomorphism `j` and a closed subscheme `J` of `Y` that factors through `j`, the
pullback `J.comap j` is closed in `Y`: `(J.comap j).subscheme ⟶ X ⟶ Y` is a closed immersion. -/
theorem isClosedImmersion_comap_subschemeι_comp (J : Y.IdealSheafData) (j : X ⟶ Y) [Mono j]
    (w : J.subscheme ⟶ X) (hw : w ≫ j = J.subschemeι) :
    IsClosedImmersion ((J.comap j).subschemeι ≫ j) := by
  have := isIso_pullback_snd_of_comp_eq j w hw
  rw [← comapIso_hom_fst, Category.assoc, pullback.condition]
  infer_instance

/-- **Closed subschemes along a monomorphism**: for a monomorphism `j : X ⟶ Y`, the image
`I ↦ I.map j` and the pullback `J ↦ J.comap j` are inverse bijections between the closed
subschemes `I` of `X` with `I.subscheme ⟶ X ⟶ Y` a closed immersion and the closed subschemes
`J` of `Y` whose inclusion factors through `j`. -/
def mapEquivOfMono (j : X ⟶ Y) [Mono j] :
    {I : X.IdealSheafData // IsClosedImmersion (I.subschemeι ≫ j)} ≃
      {J : Y.IdealSheafData // ∃ w : J.subscheme ⟶ X, w ≫ j = J.subschemeι} where
  toFun I :=
    haveI := I.2
    ⟨I.1.map j, I.1.exists_lift_map_subschemeι j⟩
  invFun J := ⟨J.1.comap j, J.2.elim fun w hw => isClosedImmersion_comap_subschemeι_comp J.1 j w hw⟩
  left_inv I :=
    haveI := I.2
    Subtype.ext (comap_map_of_mono_of_isClosedImmersion I.1 j)
  right_inv J := Subtype.ext (J.2.elim fun w hw => map_comap_of_comp_eq J.1 j w hw)

@[simp]
theorem mapEquivOfMono_apply_coe (j : X ⟶ Y) [Mono j]
    (I : {I : X.IdealSheafData // IsClosedImmersion (I.subschemeι ≫ j)}) :
    (mapEquivOfMono j I).1 = I.1.map j :=
  rfl

@[simp]
theorem mapEquivOfMono_symm_apply_coe (j : X ⟶ Y) [Mono j]
    (J : {J : Y.IdealSheafData // ∃ w : J.subscheme ⟶ X, w ≫ j = J.subschemeι}) :
    ((mapEquivOfMono j).symm J).1 = J.1.comap j :=
  rfl

/-- **Base change of a closed subscheme over a base**: for a cartesian square `a ≫ p₁ = p₂ ≫ f`
and a property `P` of morphisms that is stable under base change (for example properness,
flatness or being a closed immersion), if `I.subscheme ⟶ X₁ ⟶ T₁` has `P`, then so does
`(I.comap a).subscheme ⟶ X₂ ⟶ T₂`. The square of closed subschemes is cartesian by
`isPullback_subschemeMap_comap`. -/
theorem comap_subschemeι_comp_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {X₁ X₂ T₁ T₂ : Scheme.{u}} {a : X₂ ⟶ X₁} {p₁ : X₁ ⟶ T₁}
    {p₂ : X₂ ⟶ T₂} {f : T₂ ⟶ T₁} (h : IsPullback a p₂ p₁ f) (I : X₁.IdealSheafData)
    (hI : P (I.subschemeι ≫ p₁)) : P ((I.comap a).subschemeι ≫ p₂) :=
  MorphismProperty.of_isPullback ((isPullback_subschemeMap_comap I a).paste_vert h) hI

section BaseChange

variable {X₁ Y₁ X₂ Y₂ : Scheme.{u}} {j₁ : X₁ ⟶ Y₁} {j₂ : X₂ ⟶ Y₂} {a : X₂ ⟶ X₁} {b : Y₂ ⟶ Y₁}

/-- **Factoring through `j` is stable under base change**: for a cartesian square
`j₂ ≫ b = a ≫ j₁`, if a closed subscheme `J` of `Y₁` factors through `j₁`, then its pullback
`J.comap b` factors through `j₂`. -/
theorem exists_lift_comap_subschemeι_of_isPullback (h : IsPullback j₂ a b j₁)
    (J : Y₁.IdealSheafData) (w : J.subscheme ⟶ X₁) (hw : w ≫ j₁ = J.subschemeι) :
    ∃ w' : (J.comap b).subscheme ⟶ X₂, w' ≫ j₂ = (J.comap b).subschemeι := by
  refine ⟨h.lift (J.comap b).subschemeι ((J.comapIso b).hom ≫ pullback.snd b J.subschemeι ≫ w)
    ?_, h.lift_fst _ _ _⟩
  rw [← comapIso_hom_fst]
  simp only [Category.assoc]
  rw [hw, pullback.condition]

/-- **The image commutes with base change**: for a cartesian square `j₂ ≫ b = a ≫ j₁` with `j₁`
a monomorphism and a closed subscheme `I` of `X₁` that is closed in `Y₁`, the pullback along `b`
of the image of `I` is the image of the pullback of `I` along `a`. -/
theorem map_comap_of_isPullback (h : IsPullback j₂ a b j₁) [Mono j₁] (I : X₁.IdealSheafData)
    [IsClosedImmersion (I.subschemeι ≫ j₁)] : (I.map j₁).comap b = (I.comap a).map j₂ := by
  obtain ⟨w, hw⟩ := I.exists_lift_map_subschemeι j₁
  obtain ⟨w', hw'⟩ := exists_lift_comap_subschemeι_of_isPullback h (I.map j₁) w hw
  rw [← map_comap_of_comp_eq _ j₂ w' hw', ← comap_comp, h.w, comap_comp,
    comap_map_of_mono_of_isClosedImmersion]

/-- **Closedness is stable under base change**: for a cartesian square `j₂ ≫ b = a ≫ j₁` and a
closed subscheme `I` of `X₁` that is closed in `Y₁`, the pullback of `I` along `a` is closed in
`Y₂`; closed immersions are stable under base change (`comap_subschemeι_comp_of_isPullback`). -/
theorem isClosedImmersion_comap_subschemeι_comp_of_isPullback (h : IsPullback j₂ a b j₁)
    (I : X₁.IdealSheafData) [IsClosedImmersion (I.subschemeι ≫ j₁)] :
    IsClosedImmersion ((I.comap a).subschemeι ≫ j₂) :=
  comap_subschemeι_comp_of_isPullback @IsClosedImmersion h.flip I inferInstance

end BaseChange

/-- **Proper closed subschemes are closed in a separated target**: let `j : X ⟶ Y` be a
preimmersion (for example an immersion) and `q : Y ⟶ T` separated, with `j ≫ q = p`. A closed
subscheme `I` of `X` that is proper over `T` is closed in `Y`: `I.subscheme ⟶ Y` is proper
(Mathlib's `IsProper.of_comp`, attributed there to Stacks, Tag 01W6, (2)), so its image is
closed, and a preimmersion with closed image is a closed immersion
(`IsClosedImmersion.of_isPreimmersion`). For immersions in `Over S` the same argument is
`Scheme.isClosedImmersion_of_immersion_over_proper`. -/
theorem isClosedImmersion_subschemeι_comp_of_isProper (I : X.IdealSheafData) {j : X ⟶ Y}
    [IsPreimmersion j] {q : Y ⟶ T} [IsSeparated q] {p : X ⟶ T} (hp : j ≫ q = p)
    (hI : IsProper (I.subschemeι ≫ p)) : IsClosedImmersion (I.subschemeι ≫ j) := by
  subst hp
  rw [← Category.assoc] at hI
  have := IsProper.of_comp (I.subschemeι ≫ j) q
  exact IsClosedImmersion.of_isPreimmersion _ (I.subschemeι ≫ j).isClosedMap.isClosed_range

/-- **Proper closed subschemes of an immersed scheme**: let `j : X ⟶ Y` be a preimmersion (for
example an immersion) and `q : Y ⟶ T` proper, with `j ≫ q = p`. A closed subscheme `I` of `X` is
proper over `T` if and only if `I.subscheme ⟶ X ⟶ Y` is a closed immersion. -/
theorem isProper_subschemeι_comp_iff_isClosedImmersion (I : X.IdealSheafData) {j : X ⟶ Y}
    [IsPreimmersion j] {q : Y ⟶ T} [IsProper q] {p : X ⟶ T} (hp : j ≫ q = p) :
    IsProper (I.subschemeι ≫ p) ↔ IsClosedImmersion (I.subschemeι ≫ j) := by
  refine ⟨I.isClosedImmersion_subschemeι_comp_of_isProper hp, fun _ => ?_⟩
  subst hp
  rw [← Category.assoc]
  infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData

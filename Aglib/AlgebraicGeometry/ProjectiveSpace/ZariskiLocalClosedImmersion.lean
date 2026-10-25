/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.LinearEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Closed embeddings into projective spaces Zariski locally over the base

For a morphism of schemes `f : X ⟶ S`, a `ProjectiveSpace.ZariskiLocalClosedImmersion f` consists of

* open immersions `j a : Spec A_a ⟶ S` of affine schemes, indexed by a type `I` in the universe of
  `S`, whose images cover `S`;
* for each `a`, a finite coordinate type `ι a ≃ Fin (N a + 1)` and a closed immersion
  `c a : X ×_S Spec A_a ⟶ P(ι a)_{A_a}` over `Spec A_a`, that is,
  `c a ≫ toSpec A_a (ι a) = pullback.snd f (j a)`.

This is the hypothesis "`f : X → S` is projective Zariski locally over `S`" of Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Thm 4.8, p. 27, with the projective embeddings chosen over an affine
open cover: over each `Spec A_a` the morphism `X ×_S Spec A_a ⟶ Spec A_a` is H-projective
(Stacks, Definition 29.44.1, Tag 01W8, over an affine base; `IsHProjective`). Kleiman does not
spell out his convention for "projective" in that text; his proof reduces to `S` Noetherian and
`X/S` projective (p. 28) and then works with a closed subscheme of a projective space over a
Noetherian ring, which is the form used here over each `Spec A_a`. With "projective" as in
Stacks, Definition 29.44.1, Tag 01W8, which follows EGA (a closed subscheme of `P(ℰ)` for a
quasi-coherent `𝒪_S`-module `ℰ` of finite type), "projective Zariski locally over `S`" is
"locally projective" there, which holds exactly when `f` is H-projective over the members of an
open cover of `S` (Stacks, Lemma 29.44.4, Tag 01WB); the members may be taken affine, since
H-projectivity is stable under base change (Lemma 29.44.8, Tag 01WF). Neither the finiteness of
the cover nor a global embedding of `X` is assumed.

For `S` locally Noetherian every `A_a` is a Noetherian ring (`isNoetherianRing`, from Mathlib's
`isLocallyNoetherian_of_isOpenImmersion` and `isLocallyNoetherian_Spec`). Flatness and geometric
integrality of `f` pass to the embedded families `c a ≫ toSpec A_a (ι a)` (`flat_c_comp_toSpec`,
`geometricallyIntegral_c_comp_toSpec`), since they are the base changes `pullback.snd f (j a)`. The
embedded families are proper (`isProper_c_comp_toSpec`), hence so is `f`, properness being local on
the target (`isProper`). The open immersions form the open cover `openCover` of `S`.

**The property.** `IsZariskiLocallyHProjective f` states Kleiman's hypothesis as a property of
`f`: every point of `S` lies in an affine open `j : Spec R ⟶ S` over which `f` is H-projective,
`IsHProjective (pullback.snd f j)`. Embeddings `E` give the property
(`ZariskiLocalClosedImmersion.isZariskiLocallyHProjective`), and the property gives embeddings
(`ZariskiLocalClosedImmersion.nonempty_of_isZariskiLocallyHProjective`): at every point choose an
affine open and a closed immersion into some `P(ι)_R` with `ι` finite, followed by the linear
embedding `P(ι)_R ⊆ P(Option ι)_R` (`linearEmbedding`), which makes the number of coordinates
positive (`Option ι ≃ Fin (Nat.card ι + 1)`).

Consumer: representability of the fppf Picard functor over a locally Noetherian base,
`Aglib.AlgebraicGeometry.Picard.Representability.LocallyNoetherianBase`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **H-projective Zariski locally over the base** (Kleiman, arXiv:math/0504020v1, Thm 4.8, p. 27,
"projective Zariski locally over `S`", with projectivity over an affine base in the sense of
`IsHProjective`): every point of `S` lies in an affine open `j : Spec R ⟶ S` over which `f` is
H-projective. This is Stacks' "locally projective" (Definition 29.44.1, Tag 01W8) by Lemmas
29.44.4 and 29.44.8 (Tags 01WB, 01WF). -/
class IsZariskiLocallyHProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- Every point of `S` has an affine open neighbourhood over which `f` is H-projective. -/
  exists_isHProjective : ∀ x : S, ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ S),
    IsOpenImmersion j ∧ x ∈ Set.range j ∧ IsHProjective (pullback.snd f j)

namespace ProjectiveSpace

variable {X S : Scheme.{u}}

/-- **Closed embeddings into projective spaces Zariski locally over `S`** (Kleiman,
arXiv:math/0504020v1, Thm 4.8, p. 27, "projective Zariski locally over `S`", with the embeddings
chosen over an affine open cover): open immersions `j a : Spec A_a ⟶ S` covering `S`, and closed
immersions `c a : X ×_S Spec A_a ⟶ P(ι a)_{A_a}` over `Spec A_a` with `ι a ≃ Fin (N a + 1)`. -/
structure ZariskiLocalClosedImmersion (f : X ⟶ S) where
  /-- The index type of the affine open cover of `S`. -/
  I : Type u
  /-- The coordinate rings of the affine opens. -/
  A : I → Type u
  /-- The ring structures of the coordinate rings. -/
  [commRing : ∀ a, CommRing (A a)]
  /-- The affine opens `Spec A_a ⟶ S`. -/
  j : ∀ a, Spec (.of (A a)) ⟶ S
  /-- Each `j a` is an open immersion. -/
  [isOpenImmersion : ∀ a, IsOpenImmersion (j a)]
  /-- The affine opens cover `S`. -/
  covers : ∀ x : S, ∃ a, x ∈ Set.range (j a)
  /-- The homogeneous coordinates over `Spec A_a`. -/
  ι : I → Type u
  /-- The relative dimension of the projective space over `Spec A_a`. -/
  N : I → ℕ
  /-- The homogeneous coordinates are `N a + 1` in number. -/
  e : ∀ a, ι a ≃ Fin (N a + 1)
  /-- The embeddings `X ×_S Spec A_a ⟶ P(ι a)_{A_a}`. -/
  c : ∀ a, pullback f (j a) ⟶ ProjectiveSpace (A a) (ι a)
  /-- Each `c a` is a closed immersion. -/
  [isClosedImmersion : ∀ a, IsClosedImmersion (c a)]
  /-- Each `c a` lies over `Spec A_a`. -/
  c_comp_toSpec : ∀ a, c a ≫ toSpec (A a) (ι a) = pullback.snd f (j a)

namespace ZariskiLocalClosedImmersion

attribute [instance] commRing isOpenImmersion isClosedImmersion

variable {f : X ⟶ S} (E : ZariskiLocalClosedImmersion f)

/-- The affine opens `Spec A_a ⟶ S`, as an open cover of `S`. -/
def openCover : S.OpenCover where
  I₀ := E.I
  X a := Spec (.of (E.A a))
  f := E.j
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨E.covers, fun a => inferInstance⟩

/-- Over a locally Noetherian base the coordinate rings `A_a` are Noetherian: `Spec A_a` is an open
subscheme of `S`. -/
instance isNoetherianRing [IsLocallyNoetherian S] (a : E.I) : IsNoetherianRing (E.A a) := by
  have : IsLocallyNoetherian (Spec (.of (E.A a))) := isLocallyNoetherian_of_isOpenImmersion (E.j a)
  exact isLocallyNoetherian_Spec.mp this

/-- The embedded family `X ×_S Spec A_a ⟶ Spec A_a` is flat when `f` is: it is the base change
`pullback.snd f (j a)`. -/
instance flat_c_comp_toSpec [Flat f] (a : E.I) : Flat (E.c a ≫ toSpec (E.A a) (E.ι a)) := by
  rw [E.c_comp_toSpec]
  infer_instance

/-- The embedded family `X ×_S Spec A_a ⟶ Spec A_a` has geometrically integral fibres when `f`
has: it is the base change `pullback.snd f (j a)`. -/
instance geometricallyIntegral_c_comp_toSpec [GeometricallyIntegral f] (a : E.I) :
    GeometricallyIntegral (E.c a ≫ toSpec (E.A a) (E.ι a)) := by
  rw [E.c_comp_toSpec]
  infer_instance

/-- The embedded family `X ×_S Spec A_a ⟶ Spec A_a` is proper: a closed immersion followed by
`toSpec A_a (ι a)`, which is proper since `ι a` is finite (`isProper_toSpec`). -/
instance isProper_c_comp_toSpec (a : E.I) : IsProper (E.c a ≫ toSpec (E.A a) (E.ι a)) := by
  have : Finite (E.ι a) := .of_equiv _ (E.e a).symm
  infer_instance

include E in
/-- **A morphism projective Zariski locally over the base is proper** (Stacks, Lemma 29.44.5,
Tag 01WC): properness is local on the target (Mathlib's `IsZariskiLocalAtTarget @IsProper`), and
over each `Spec A_a` the morphism is `c a ≫ toSpec A_a (ι a)`. -/
theorem isProper : IsProper f :=
  IsZariskiLocalAtTarget.of_openCover (P := @IsProper) E.openCover fun (a : E.I) => by
    change IsProper (pullback.snd f (E.j a))
    rw [← E.c_comp_toSpec a]
    infer_instance

include E in
/-- **Embeddings give the property**: over the chart `a` containing a point, `f` is H-projective
through `c a`. -/
theorem isZariskiLocallyHProjective : IsZariskiLocallyHProjective f where
  exists_isHProjective x := by
    obtain ⟨a, ha⟩ := E.covers x
    have : Finite (E.ι a) := .of_equiv _ (E.e a).symm
    exact ⟨.of (E.A a), E.j a, inferInstance, ha, ⟨E.ι a, inferInstance, E.c a, inferInstance,
      E.c_comp_toSpec a⟩⟩

/-- **The property gives embeddings**: at every point of `S` choose an affine open `Spec R ⟶ S`
over which `f` is H-projective, with a closed immersion into `P(ι)_R`, `ι` finite, followed by the
linear embedding `P(ι)_R ⊆ P(Option ι)_R`, so that the coordinates are `Nat.card ι + 1` in
number. -/
theorem nonempty_of_isZariskiLocallyHProjective (f : X ⟶ S) [h : IsZariskiLocallyHProjective f] :
    Nonempty (ZariskiLocalClosedImmersion f) := by
  choose R j hj hx hR using h.exists_isHProjective
  choose ι hι c hc hcomp using fun x => (hR x).exists_isClosedImmersion
  exact ⟨{
    I := S
    A x := R x
    j := j
    isOpenImmersion := hj
    covers x := ⟨x, hx x⟩
    ι x := Option (ι x)
    N x := Nat.card (ι x)
    e _ := Finite.equivFinOfCardEq Finite.card_option
    c x := c x ≫ linearEmbedding (R x) (Option.some_injective (ι x))
    c_comp_toSpec x := by
      change (c x ≫ linearEmbedding (R x) (Option.some_injective (ι x))) ≫
        toSpec (R x) (Option (ι x)) = pullback.snd f (j x)
      rw [Category.assoc, linearEmbedding_toSpec]
      exact hcomp x }⟩

end ZariskiLocalClosedImmersion

end ProjectiveSpace

end AlgebraicGeometry

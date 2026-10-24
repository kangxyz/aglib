/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.LocallyNoetherianFunctor
public import Aglib.AlgebraicGeometry.Morphisms.UniversallyClosed.ImageComplement
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability

/-!
# The Hilbert functor of an open subscheme of projective space is an open subfunctor

Let `A` be a ring, `ι` a finite coordinate type, `U ⊆ P^n_A` an open and `Φ ∈ ℚ[X]`. For a scheme
`g : T ⟶ Spec A`, a closed subscheme `Z ⊆ P^n_A ×_{Spec A} T` *lies in* `U_T = U ×_{Spec A} T`
when its support lies in the preimage of `U` under the first projection. This condition is open
on `T` and universal (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
§6, p. 28, first Exercise ("Exercise A"), for the proper morphism `P^n_A ×_{Spec A} T ⟶ T`, the
closed subscheme `Y = (P^n_A ∖ U)_T` and the coherent sheaf `F = 𝒪_Z`, whose support is the
support of `Z`):

* `containmentLocus ι g Z U`: the open set of the points `t ∈ T` over which `Z` lies in `U_T`
  (`mem_containmentLocus`), the complement of the image of the closed set `Z ∖ U_T` under the
  proper projection `P^n_A ×_{Spec A} T ⟶ T` (`Scheme.Hom.complImage`,
  `Morphisms/UniversallyClosed/ImageComplement`);
* `preimage_containmentLocus_eq_top_iff`: for `f : T' ⟶ T` over `Spec A`, `f` factors through
  `containmentLocus ι g Z U` if and only if the pullback of `Z` along the base-changed map lies
  in `U_{T'}`. The proof is the base-change compatibility of images on points
  (`Scheme.preimage_complImage_eq_top_iff_of_isPullback`) for the cartesian square
  `isPullback_baseChangeMap`, with `IdealSheafData.support_comap`.

No flatness of `Z` and no Noetherian hypothesis on `A` or `T` is used. Consequently:

* `openHilbertSubfunctor ι Φ U`, the subfunctor `Hilb^Φ_U ⊆ Hilb^Φ` of the points `Z` of
  `hilbertFunctor ι Φ` that lie in `U_T`, defined on all schemes over `Spec A`;
* `isOpenOverSubfunctor_openHilbertSubfunctor`: it is an open subfunctor (Stacks, Tag 01JI,
  Definition 26.15.3, "representable by open immersions"), with open `containmentLocus` for the
  point `Z`;
* `locallyNoetherianOpenHilbertSubfunctor ι A Φ U` and
  `isOpenSubfunctor_locallyNoetherianOpenHilbertSubfunctor`: its restriction to locally
  Noetherian test schemes, a subfunctor of `locallyNoetherianHilbertFunctor ι A Φ`, is open.

Its representability by an open subscheme of the Hilbert scheme is
`HilbertScheme/OpenSubscheme`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A]

section ContainmentLocus

variable [Finite ι] {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))

/-- **The locus over which a closed subscheme of `P^n_T` lies in an open `U ⊆ P^n_A`**
(Nitsure, arXiv:math/0504590v1, §6, p. 28, Exercise A, for `F = 𝒪_Z` and `Y = (P^n_A ∖ U)_T`):
for `g : T ⟶ Spec A`, a closed subscheme `Z ⊆ P^n_A ×_{Spec A} T` and an open `U ⊆ P^n_A`, the open
set of the points of `T` over which `Z` lies in `U_T`, the complement of the image of the closed
set `Z ∖ U_T` under the proper projection `P^n_A ×_{Spec A} T ⟶ T`. -/
def containmentLocus (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (U : (ProjectiveSpace A ι).Opens) : T.Opens :=
  (pullback.snd (toSpec A ι) g).complImage
    (Z.support ⊓ (pullback.fst (toSpec A ι) g ⁻¹ᵁ U).compl)

/-- A point `t ∈ T` lies in `containmentLocus ι g Z U` if and only if every point of `Z` over `t`
lies in `U_T`. -/
theorem mem_containmentLocus (Z : (pullback (toSpec A ι) g).IdealSheafData)
    (U : (ProjectiveSpace A ι).Opens) (t : T) :
    t ∈ containmentLocus ι g Z U ↔ ∀ x ∈ Z.support, pullback.snd (toSpec A ι) g x = t →
      pullback.fst (toSpec A ι) g x ∈ U := by
  rw [containmentLocus, Scheme.Hom.mem_complImage]
  constructor
  · intro h x hx hxt
    by_contra hxU
    exact h x ⟨hx, hxU⟩ hxt
  · intro h x hx hxt
    exact hx.2 (h x hx.1 hxt)

/-- **The containment locus is universal** (Nitsure, arXiv:math/0504590v1, §6, p. 28,
Exercise A): for `f : T' ⟶ T` over `Spec A`, `f` factors through `containmentLocus ι g Z U` if
and only if the pullback of `Z` along the base-changed map
`P^n_A ×_{Spec A} T' ⟶ P^n_A ×_{Spec A} T` lies in `U_{T'}`. -/
theorem preimage_containmentLocus_eq_top_iff {T' : Scheme.{u}}
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g')
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (U : (ProjectiveSpace A ι).Opens) :
    f ⁻¹ᵁ containmentLocus ι g Z U = ⊤ ↔
      ∀ x ∈ (Z.comap (baseChangeMap ι g g' f h)).support, pullback.fst (toSpec A ι) g' x ∈ U := by
  rw [containmentLocus,
    Scheme.preimage_complImage_eq_top_iff_of_isPullback (isPullback_baseChangeMap ι g g' f h),
    Scheme.IdealSheafData.support_comap]
  constructor
  · intro hC x hx
    by_contra hxU
    have hmem : x ∈ baseChangeMap ι g g' f h ⁻¹'
        ((Z.support ⊓ (pullback.fst (toSpec A ι) g ⁻¹ᵁ U).compl : Closeds _) : Set _) := by
      refine ⟨hx, ?_⟩
      change pullback.fst (toSpec A ι) g (baseChangeMap ι g g' f h x) ∉ U
      rw [← Scheme.Hom.comp_apply, baseChangeMap_fst]
      exact hxU
    rw [hC] at hmem
    exact (Set.mem_empty_iff_false x).1 hmem
  · intro hsub
    refine Set.eq_empty_of_forall_notMem fun x hx => hx.2 ?_
    have hfst : pullback.fst (toSpec A ι) g' x ∈ U := hsub x hx.1
    change pullback.fst (toSpec A ι) g (baseChangeMap ι g g' f h x) ∈ U
    rw [← Scheme.Hom.comp_apply, baseChangeMap_fst]
    exact hfst

end ContainmentLocus

/-- **The Hilbert subfunctor of an open `U ⊆ P^n_A`** (`Hilb^Φ_U`; Nitsure,
arXiv:math/0504590v1, §6, p. 28, Exercise A): the points `Z` of `Hilb^Φ(T)` that lie in
`U_T = U ×_{Spec A} T`, that is, every point of the support of `Z` maps into `U` under the first
projection `P^n_A ×_{Spec A} T ⟶ P^n_A`. It is defined on all schemes over `Spec A`. -/
def openHilbertSubfunctor (Φ : ℚ[X]) (U : (ProjectiveSpace A ι).Opens) :
    Subfunctor (hilbertFunctor (A := A) ι Φ) where
  obj T := {Z | ∀ x ∈ Z.1.support, pullback.fst (toSpec A ι) T.unop.hom x ∈ U}
  map {T T'} f Z hZ := by
    change ∀ x ∈ (Z.1.comap (baseChangeMap ι T.unop.hom T'.unop.hom f.unop.left
      (Over.w f.unop))).support, pullback.fst (toSpec A ι) T'.unop.hom x ∈ U
    rw [Scheme.IdealSheafData.support_comap]
    intro x hx
    have hfst : pullback.fst (toSpec A ι) T.unop.hom
        (baseChangeMap ι T.unop.hom T'.unop.hom f.unop.left (Over.w f.unop) x) ∈ U :=
      hZ (baseChangeMap ι T.unop.hom T'.unop.hom f.unop.left (Over.w f.unop) x) hx
    rw [← baseChangeMap_fst ι T.unop.hom T'.unop.hom f.unop.left (Over.w f.unop),
      Scheme.Hom.comp_apply]
    exact hfst

theorem mem_openHilbertSubfunctor_obj (Φ : ℚ[X]) (U : (ProjectiveSpace A ι).Opens)
    {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (Z : (hilbertFunctor ι Φ).obj T) :
    Z ∈ (openHilbertSubfunctor ι Φ U).obj T ↔
      ∀ x ∈ Z.1.support, pullback.fst (toSpec A ι) T.unop.hom x ∈ U :=
  Iff.rfl

/-- **`Hilb^Φ_U` is an open subfunctor of `Hilb^Φ`** (Nitsure, arXiv:math/0504590v1, §6, p. 28,
Exercise A; Stacks, Tag 01JI, "representable by open immersions"): for a point `Z` of
`Hilb^Φ(T)`, a morphism `f : T' ⟶ T` over `Spec A` pulls `Z` back into `Hilb^Φ_U` if and only if
it factors through the open `containmentLocus ι T.hom Z U`. -/
theorem isOpenOverSubfunctor_openHilbertSubfunctor [Finite ι] (Φ : ℚ[X])
    (U : (ProjectiveSpace A ι).Opens) :
    Scheme.LocalRepresentability.IsOpenOverSubfunctor (openHilbertSubfunctor ι Φ U) :=
  fun T Z => ⟨containmentLocus ι T.hom Z.1 U, fun T' f =>
    (preimage_containmentLocus_eq_top_iff ι T.hom T'.hom f.left (Over.w f) Z.1 U).symm⟩

variable (A) in
/-- **`Hilb^Φ_U` on locally Noetherian test schemes**: the restriction of
`openHilbertSubfunctor ι Φ U`, a subfunctor of `locallyNoetherianHilbertFunctor ι A Φ`. -/
abbrev locallyNoetherianOpenHilbertSubfunctor (Φ : ℚ[X]) (U : (ProjectiveSpace A ι).Opens) :
    Subfunctor (locallyNoetherianHilbertFunctor ι A Φ) :=
  Scheme.LocalRepresentability.restrictSubfunctor (Scheme.locallyNoetherianOver _)
    (openHilbertSubfunctor ι Φ U)

/-- **`Hilb^Φ_U` is an open subfunctor of `Hilb^Φ` on locally Noetherian test schemes**. -/
theorem isOpenSubfunctor_locallyNoetherianOpenHilbertSubfunctor [Finite ι] (Φ : ℚ[X])
    (U : (ProjectiveSpace A ι).Opens) :
    Scheme.LocalRepresentability.IsOpenSubfunctor
      (locallyNoetherianOpenHilbertSubfunctor ι A Φ U) :=
  (isOpenOverSubfunctor_openHilbertSubfunctor ι Φ U).restrict

end AlgebraicGeometry.ProjectiveSpace

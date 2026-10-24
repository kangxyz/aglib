/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.OpenSubfunctor
public import Aglib.AlgebraicGeometry.HilbertScheme.Representability
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.LocallyNoetherian
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.OpenSubscheme

/-!
# The Hilbert scheme of an open subscheme of projective space

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)`, `Φ ∈ ℚ[X]`, `r ≥ hilbertRegularityBound n Φ` a
natural number, `G_Φ = hilbertScheme ι n e A Φ r` the Hilbert scheme of `P^n_A`
(`HilbertScheme/Representability`) with universal family `W ⊆ P^n_A ×_{Spec A} G_Φ`
(`universalHilbertFamily`), and `U ⊆ P^n_A` an open.

* `openHilbertSchemeOpens ι n e A Φ r U`: the open of `G_Φ` over which `W` lies in `U`
  (`containmentLocus`, `mem_openHilbertSchemeOpens`), the complement of the image of the closed
  set `W ∖ U_{G_Φ}` under the proper projection `P^n_A ×_{Spec A} G_Φ ⟶ G_Φ`;
* `openHilbertScheme ι n e A Φ r U`: the corresponding open subscheme `G_Φ^U`, a Noetherian
  scheme (`isNoetherian_openHilbertScheme`). `openHilbertSchemeOver ι n e A Φ r U` is `G_Φ^U` as
  a locally Noetherian test scheme over `Spec A`, and `openHilbertSchemeι : G_Φ^U ⟶ G_Φ` is the
  open immersion (`isOpenImmersion_openHilbertSchemeι`; over `Spec A`,
  `openHilbertSchemeToHilbertScheme`);
* `locallyNoetherianOpenHilbertSubfunctorRepresentableBy`: **`G_Φ^U` represents the Hilbert
  subfunctor `Hilb^Φ_U` of the families contained in `U`** (`openHilbertSubfunctor`) on locally
  Noetherian test schemes over `Spec A`. A morphism `a : T ⟶ G_Φ^U` corresponds to the pullback
  of `W` along `T ⟶ G_Φ^U ⟶ G_Φ`
  (`locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_coe`), and the universal
  family is the restriction of `W` to `G_Φ^U`
  (`locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_id_coe`).

This is Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §6, p. 28,
first Exercise ("Exercise A"), for the proper morphism `π : P^n_A ×_{Spec A} G_Φ ⟶ G_Φ`, the closed
subscheme `Y = (P^n_A ∖ U)_{G_Φ}` and `F = 𝒪_W`: the openness step of the proof of Theorem 6.1
(p. 28) for Hilbert schemes, with `Hilb^Φ_U` the subfunctor of the families contained in `U`. Its
identification with the Hilbert functor of `U` itself (the second Exercise, "Exercise B") is not
part of this file. A morphism `a : T ⟶ G_Φ` factors through `G_Φ^U` if and only if the pullback of
`W` to `T` lies in `U_T` (`preimage_openHilbertSchemeOpens_eq_top_iff`, from
`preimage_containmentLocus_eq_top_iff`): images commute with base change on points. The
representation is then the restriction of `locallyNoetherianHilbertFunctorRepresentableBy` to the
open subscheme (`Scheme.LocalRepresentability.representableByRestrictOpens`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.LocalRepresentability

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (Φ : ℚ[X]) (r : ℕ) (U : (ProjectiveSpace A ι).Opens)

/-- **The open locus of the Hilbert scheme over which the universal family lies in `U`**: the
points of `G_Φ` over which the universal family `W` lies in `U_{G_Φ}` (`containmentLocus`). -/
def openHilbertSchemeOpens : (hilbertScheme ι n e A Φ r).Opens :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  containmentLocus ι (hilbertSchemeOver ι n e A Φ r).obj.hom
    (universalHilbertFamily ι n e A Φ r) U

/-- A point of the Hilbert scheme lies in `openHilbertSchemeOpens ι n e A Φ r U` if and only if
every point of the universal family over it lies in `U_{G_Φ}`. -/
theorem mem_openHilbertSchemeOpens (x : hilbertScheme ι n e A Φ r) :
    x ∈ openHilbertSchemeOpens ι n e A Φ r U ↔
      ∀ w ∈ (universalHilbertFamily ι n e A Φ r).support,
        pullback.snd (toSpec A ι) (hilbertSchemeOver ι n e A Φ r).obj.hom w = x →
          pullback.fst (toSpec A ι) (hilbertSchemeOver ι n e A Φ r).obj.hom w ∈ U :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  mem_containmentLocus ι _ _ U x

/-- **The Hilbert scheme of `U`** as a locally Noetherian test scheme over `Spec A`: the open
subscheme `openHilbertSchemeOpens ι n e A Φ r U` of the Hilbert scheme. -/
def openHilbertSchemeOver : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)) :=
  restrictOpens (hilbertSchemeOver ι n e A Φ r) (openHilbertSchemeOpens ι n e A Φ r U)

/-- **The Hilbert scheme of `U`**, the open subscheme `G_Φ^U` of the Hilbert scheme over which the
universal family lies in `U`. -/
abbrev openHilbertScheme : Scheme.{u} :=
  (openHilbertSchemeOver ι n e A Φ r U).obj.left

/-- The inclusion `G_Φ^U ⟶ G_Φ` of the Hilbert scheme of `U` into the Hilbert scheme. -/
def openHilbertSchemeι : openHilbertScheme ι n e A Φ r U ⟶ hilbertScheme ι n e A Φ r :=
  (openHilbertSchemeOpens ι n e A Φ r U).ι

/-- **The Hilbert scheme of `U` is an open subscheme of the Hilbert scheme.** -/
instance isOpenImmersion_openHilbertSchemeι :
    IsOpenImmersion (openHilbertSchemeι ι n e A Φ r U) :=
  inferInstanceAs (IsOpenImmersion (openHilbertSchemeOpens ι n e A Φ r U).ι)

/-- The Hilbert scheme of `U` is Noetherian, as an open subscheme of the Noetherian Hilbert
scheme. -/
instance isNoetherian_openHilbertScheme : IsNoetherian (openHilbertScheme ι n e A Φ r U) :=
  haveI : TopologicalSpace.NoetherianSpace (openHilbertScheme ι n e A Φ r U) :=
    (openHilbertSchemeι ι n e A Φ r U).isEmbedding.isInducing.noetherianSpace
  {}

theorem range_openHilbertSchemeι :
    Set.range (openHilbertSchemeι ι n e A Φ r U) = openHilbertSchemeOpens ι n e A Φ r U :=
  Scheme.Opens.range_ι _

/-- The open immersion `G_Φ^U ⟶ G_Φ` as a morphism of test schemes over `Spec A`. -/
def openHilbertSchemeToHilbertScheme :
    openHilbertSchemeOver ι n e A Φ r U ⟶ hilbertSchemeOver ι n e A Φ r :=
  restrictOpensι _ _

theorem openHilbertSchemeToHilbertScheme_hom_left :
    (openHilbertSchemeToHilbertScheme ι n e A Φ r U).hom.left = openHilbertSchemeι ι n e A Φ r U :=
  rfl

variable {ι n e A Φ r U} in
/-- **A morphism to the Hilbert scheme factors through `G_Φ^U` if and only if the pulled-back
family lies in `U`** (Nitsure, arXiv:math/0504590v1, §6, p. 28, Exercise A): for a locally
Noetherian `T` and `a : T ⟶ G_Φ`, `a` maps into `openHilbertSchemeOpens ι n e A Φ r U` if and only
if the pullback of the universal family along `a` lies in `U_T`. -/
theorem preimage_openHilbertSchemeOpens_eq_top_iff
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ hilbertSchemeOver ι n e A Φ r) :
    a.hom.left ⁻¹ᵁ openHilbertSchemeOpens ι n e A Φ r U = ⊤ ↔
      ∀ x ∈ ((locallyNoetherianHilbertFunctor ι A Φ).map a.op
        (universalHilbertPoint ι n e A Φ r)).1.support,
          pullback.fst (toSpec A ι) T.obj.hom x ∈ U :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  preimage_containmentLocus_eq_top_iff ι _ T.obj.hom a.hom.left (Over.w a.hom)
    (universalHilbertFamily ι n e A Φ r) U

section Representability

variable (hr : hilbertRegularityBound n Φ ≤ r)

/-- **Representability of the Hilbert functor of an open `U ⊆ P^n_A`** (Nitsure,
arXiv:math/0504590v1, §6, p. 28, Exercise A, with §5, p. 24, Theorem 5.3 for `P^n_A`): for a
Noetherian ring `A`, `ι ≃ Fin (n + 1)`, `Φ ∈ ℚ[X]`, a natural `r ≥ hilbertRegularityBound n Φ` and
an open `U ⊆ P^n_A`, the subfunctor `Hilb^Φ_U` of the Hilbert functor of `P^n_A` of the families
contained in `U` is represented, on locally Noetherian test schemes over `Spec A`, by the open
subscheme `G_Φ^U` of the Hilbert scheme (`isOpenImmersion_openHilbertSchemeι`), with universal
family the restriction of `universalHilbertFamily`. -/
def locallyNoetherianOpenHilbertSubfunctorRepresentableBy :
    (locallyNoetherianOpenHilbertSubfunctor ι A Φ U).toFunctor.RepresentableBy
      (openHilbertSchemeOver ι n e A Φ r U) :=
  representableByRestrictOpens (locallyNoetherianHilbertFunctorRepresentableBy ι n e A Φ r hr)
    (locallyNoetherianOpenHilbertSubfunctor ι A Φ U) (openHilbertSchemeOpens ι n e A Φ r U)
    fun _ a => (preimage_openHilbertSchemeOpens_eq_top_iff a).symm

/-- The representing equivalence sends `a : T ⟶ G_Φ^U` to the pullback of the universal family
along `T ⟶ G_Φ^U ⟶ G_Φ`. -/
theorem locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_coe
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ openHilbertSchemeOver ι n e A Φ r U) :
    ((locallyNoetherianOpenHilbertSubfunctorRepresentableBy ι n e A Φ r U hr).homEquiv a :
        (locallyNoetherianHilbertFunctor ι A Φ).obj (op T)) =
      (locallyNoetherianHilbertFunctor ι A Φ).map
        (a ≫ openHilbertSchemeToHilbertScheme ι n e A Φ r U).op
        (universalHilbertPoint ι n e A Φ r) :=
  rfl

/-- **The universal family of `Hilb^Φ_U`** is the restriction of the universal family of the
Hilbert scheme to `G_Φ^U`: its pullback along `P^n_A ×_{Spec A} G_Φ^U ⟶ P^n_A ×_{Spec A} G_Φ`. -/
theorem locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_id_coe :
    ((locallyNoetherianOpenHilbertSubfunctorRepresentableBy ι n e A Φ r U hr).homEquiv (𝟙 _) :
        (locallyNoetherianHilbertFunctor ι A Φ).obj (op (openHilbertSchemeOver ι n e A Φ r U))).1 =
      (universalHilbertFamily ι n e A Φ r).comap
        (baseChangeMap ι (hilbertSchemeOver ι n e A Φ r).obj.hom
          (openHilbertSchemeOver ι n e A Φ r U).obj.hom (openHilbertSchemeι ι n e A Φ r U)
          rfl) := by
  rw [locallyNoetherianOpenHilbertSubfunctorRepresentableBy_homEquiv_coe, Category.id_comp]
  rfl

end Representability

end AlgebraicGeometry.ProjectiveSpace

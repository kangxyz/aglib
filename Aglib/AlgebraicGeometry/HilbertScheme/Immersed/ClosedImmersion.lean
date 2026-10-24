/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.ClosedSubscheme.Representability
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Subfunctor
public import Aglib.AlgebraicGeometry.HilbertScheme.QuasiProjective

/-!
# The Hilbert functor of a closed subscheme `X ⊆ P^n_A`, X-first

Let `A` be a Noetherian ring, `e : ι ≃ Fin (n + 1)`, `i : X ⟶ P^n_A = ProjectiveSpace A ι` a closed
immersion over `Spec A` (`hi : i ≫ toSpec A ι = πX`) and `θ ∈ ℚ[X]`. Write `C = i.ker` for the
closed subscheme of `P^n_A` cut out by `i`.

* `immersedHilbertSubfunctorIsoClosedHilbertSubfunctor` and
  `locallyNoetherianImmersedHilbertFunctorIsoOfIsClosedImmersion`: the families of `Hilb^θ`
  contained in `X` are the points of the Hilbert subfunctor of `C`
  (`immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker`, `HilbertScheme/Immersed/Subfunctor`),
  so with `locallyNoetherianImmersedHilbertFunctorIso` (`V ↦ V.map i_T`) the Hilbert functor of `X`
  (X-first) is the Hilbert subfunctor of `C` on locally Noetherian test schemes.
* `locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion`: hence, for a natural
  `r ≥ hilbertRegularityBound n θ` and sections `φ` of `𝒪(r)` cutting out `C`, the closed Hilbert
  scheme `closedHilbertSchemeOver ι n e A θ r hr φ` of `C` represents the Hilbert functor of `X`,
  with universal family the pullback of the universal family of `C` to `X ×_{Spec A} H`
  (`…_homEquiv_id_coe`); the image of a point in `P^n_A ×_{Spec A} T` is the corresponding point of
  `Hilb^θ_C` (`…_homEquiv_coe_map`). This is the closed case of Nitsure, *Construction of Hilbert
  and Quot schemes*, arXiv:math/0504590v1, Thm 6.1, p. 28 (through Thm 5.3, p. 24, and
  Lemma 5.4 (ii), p. 25, as in `HilbertScheme/ClosedSubscheme/Representability`), in the X-first
  form.
* `isHQuasiProjective_closedHilbertSchemeOver_hom`: the representing scheme is H-quasi-projective
  over `Spec A`, as a closed subscheme of the Hilbert scheme of `P^n_A`
  (`HilbertScheme/QuasiProjective`); with the existence of the sections `φ`
  (`exists_sectionPairing_imageIdealData_eq`) this gives
  `exists_locallyNoetherianImmersedHilbertFunctor_representableBy_of_isClosedImmersion`.

For an immersion `i`, `HilbertScheme/Immersed/Representability` represents the same functor by
`immersedHilbertSchemeOver`, an open subscheme of the same closed Hilbert scheme of `i.ker`. For a
closed `i` the closed Hilbert scheme itself is used here; the scheme of relative effective Cartier
divisors with polynomial `θ` (`HilbertScheme/Divisor/ClosedHilbertScheme`) is an open subscheme of
it.

The identification of the Hilbert functor of `X` with the Hilbert subfunctor of `C` is used
implicitly by Nitsure (p. 25, after Lemma 5.4); the closed and locally closed forms of the
underlying factorization are in `HilbertScheme/Immersed/Subfunctor`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

section ClosedCase

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} (i : X ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πX)
  [IsClosedImmersion i]

/-- The underlying functors of `immersedHilbertSubfunctor i hi Φ` and of the Hilbert subfunctor of
`C = i.ker` are isomorphic, by the identity on the underlying families. -/
def immersedHilbertSubfunctorIsoClosedHilbertSubfunctor (Φ : ℚ[X]) :
    (immersedHilbertSubfunctor i hi Φ).toFunctor ≅ (closedHilbertSubfunctor ι Φ i.ker).toFunctor
    where
  hom := Subfunctor.homOfLe (immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker i hi Φ).le
  inv := Subfunctor.homOfLe (immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker i hi Φ).ge
  hom_inv_id := by
    rw [← cancel_mono (immersedHilbertSubfunctor i hi Φ).ι, Category.assoc,
      Subfunctor.homOfLe_ι, Subfunctor.homOfLe_ι, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (closedHilbertSubfunctor ι Φ i.ker).ι, Category.assoc,
      Subfunctor.homOfLe_ι, Subfunctor.homOfLe_ι, Category.id_comp]

/-- **The Hilbert functor of a closed `X ⊆ P^n_A` is the Hilbert subfunctor of `C = i.ker`** on
locally Noetherian test schemes: `V ↦ V.map i_T` (`locallyNoetherianImmersedHilbertFunctorIso`),
followed by `immersedHilbertSubfunctorIsoClosedHilbertSubfunctor` at each test scheme. -/
def locallyNoetherianImmersedHilbertFunctorIsoOfIsClosedImmersion [Finite ι] (Φ : ℚ[X]) :
    locallyNoetherianImmersedHilbertFunctor i hi Φ ≅
      (locallyNoetherianClosedHilbertSubfunctor ι A Φ i.ker).toFunctor :=
  locallyNoetherianImmersedHilbertFunctorIso i hi Φ ≪≫
    NatIso.ofComponents
      (fun T => (immersedHilbertSubfunctorIsoClosedHilbertSubfunctor i hi Φ).app (op T.unop.obj))
      fun f => (immersedHilbertSubfunctorIsoClosedHilbertSubfunctor i hi Φ).hom.naturality
        ((Scheme.locallyNoetherianOverInclusion _).op.map f)

end ClosedCase

section Representability

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] {X : Scheme.{u}} {πX : X ⟶ Spec (CommRingCat.of A)}
  (i : X ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πX) [IsClosedImmersion i] (θ : ℚ[X])
  (r : ℕ) (hr : hilbertRegularityBound n θ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))

/-- **The closed Hilbert scheme is H-quasi-projective** over `Spec A`: it is a closed subscheme of
the Hilbert scheme of `P^n_A` (`isHQuasiProjective_hilbertSchemeOver_hom`). -/
instance isHQuasiProjective_closedHilbertSchemeOver_hom :
    IsHQuasiProjective (closedHilbertSchemeOver ι n e A θ r hr φ).obj.hom :=
  @IsHQuasiProjective.comp_of_isImmersion _ _ _ _ (closedHilbertSchemeι ι n e A θ r hr φ)
    (hilbertSchemeOver ι n e A θ r).obj.hom inferInstance
    (isHQuasiProjective_hilbertSchemeOver_hom ι n e A θ r)

/-- **The Hilbert functor of a closed subscheme `X ⊆ P^n_A` is represented by its closed Hilbert
scheme** (Nitsure, arXiv:math/0504590v1, Thm 6.1, p. 28, for a closed `X`, X-first, on locally
Noetherian test schemes): for a closed immersion `i : X ⟶ P^n_A`, a natural
`r ≥ hilbertRegularityBound n θ` and sections `φ` of `𝒪(r)` cutting out `C = i.ker`, the closed
Hilbert scheme `closedHilbertSchemeOver ι n e A θ r hr φ` represents
`locallyNoetherianImmersedHilbertFunctor i hi θ`. A morphism `a` corresponds to the pullback to
`X ×_{Spec A} T` of the point of `Hilb^θ_C(T)` given by `a`. For an immersion `i`,
`locallyNoetherianImmersedHilbertFunctorRepresentableBy` represents the same functor by an open
subscheme of the same closed Hilbert scheme. -/
def locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    (locallyNoetherianImmersedHilbertFunctor i hi θ).RepresentableBy
      (closedHilbertSchemeOver ι n e A θ r hr φ) :=
  haveI : Finite ι := Finite.of_equiv _ e.symm
  (locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A θ r hr φ hC).ofIso
    (locallyNoetherianImmersedHilbertFunctorIsoOfIsClosedImmersion i hi θ).symm

variable {ι n e A i hi θ r hr φ}

/-- The representing equivalence of the Hilbert functor of `X` sends `a` to the pullback along
`i_T` of the point of `Hilb^θ_C(T)` given by `a`. -/
theorem locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion_homEquiv_coe
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ closedHilbertSchemeOver ι n e A θ r hr φ) :
    ((locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion ι n e A i hi θ r
        hr φ hC).homEquiv a).1 =
      ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A θ r hr φ hC).homEquiv
        a).1.1.comap (immersionBaseChange i hi T.obj.hom) :=
  rfl

/-- **The image in `P^n_A ×_{Spec A} T`** of the point of the Hilbert functor of `X` given by `a`
is the point of `Hilb^θ_C(T)` given by `a`. -/
theorem locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion_homEquiv_coe_map
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a : T ⟶ closedHilbertSchemeOver ι n e A θ r hr φ) :
    ((locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion ι n e A i hi θ r
        hr φ hC).homEquiv a).1.map (immersionBaseChange i hi T.obj.hom) =
      ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A θ r hr φ hC).homEquiv
        a).1.1 := by
  obtain ⟨w, hw⟩ := (exists_lift_immersionBaseChange_iff i hi T.obj.hom _).mpr
    ((locallyNoetherianClosedHilbertSubfunctorRepresentableBy ι n e A θ r hr φ hC).homEquiv a).2
  rw [locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion_homEquiv_coe]
  exact Scheme.IdealSheafData.map_comap_of_comp_eq _ _ w hw

/-- **The universal family of the Hilbert functor of `X`** over the closed Hilbert scheme `H` is
the pullback to `X ×_{Spec A} H` of the universal family of `Hilb^θ_C`, the restriction of the
universal family of the Hilbert scheme of `P^n_A`. -/
theorem locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion_homEquiv_id_coe
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = i.ker) :
    ((locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion ι n e A i hi θ r
        hr φ hC).homEquiv (𝟙 _)).1 =
      ((universalHilbertFamily ι n e A θ r).comap
        (baseChangeMap ι (hilbertSchemeOver ι n e A θ r).obj.hom
          (closedHilbertSchemeOver ι n e A θ r hr φ).obj.hom (closedHilbertSchemeι ι n e A θ r hr φ)
          rfl)).comap
        (immersionBaseChange i hi (closedHilbertSchemeOver ι n e A θ r hr φ).obj.hom) := by
  rw [locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion_homEquiv_coe,
    locallyNoetherianClosedHilbertSubfunctorRepresentableBy_homEquiv_id_coe]

variable (ι n e A i hi θ)

include e in
/-- **The Hilbert functor of a closed subscheme `X ⊆ P^n_A` is representable by an
H-quasi-projective scheme** over the Noetherian ring `A`, on locally Noetherian test schemes
(Nitsure, arXiv:math/0504590v1, Thm 6.1, p. 28, for a closed `X`, X-first, with `E = 𝒪`): the
closed Hilbert scheme of `C = i.ker` for any large `r`. -/
theorem exists_locallyNoetherianImmersedHilbertFunctor_representableBy_of_isClosedImmersion :
    ∃ H : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)),
      IsHQuasiProjective H.obj.hom ∧
        Nonempty ((locallyNoetherianImmersedHilbertFunctor i hi θ).RepresentableBy H) := by
  obtain ⟨m, hm⟩ := exists_sectionPairing_imageIdealData_eq ι n e i.ker
  obtain ⟨r, hr, hmr⟩ : ∃ r : ℕ, hilbertRegularityBound n θ ≤ r ∧ m ≤ r :=
    ⟨max (hilbertRegularityBound n θ).toNat m.toNat,
      (Int.self_le_toNat _).trans (by exact_mod_cast le_max_left _ _),
      (Int.self_le_toNat _).trans (by exact_mod_cast le_max_right _ _)⟩
  obtain ⟨J, φ, hC⟩ := hm r hmr
  exact ⟨closedHilbertSchemeOver ι n e A θ r hr φ, inferInstance,
    ⟨locallyNoetherianImmersedHilbertFunctorRepresentableByOfIsClosedImmersion ι n e A i hi θ r hr
      φ hC⟩⟩

end Representability

end AlgebraicGeometry.ProjectiveSpace

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.ClosedSubscheme.Representability
public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Functor
public import Aglib.AlgebraicGeometry.HilbertScheme.OpenSubfunctor
public import Aglib.AlgebraicGeometry.Properties.Noetherian.Yoneda

/-!
# Families in an immersed scheme: a closed and an open condition

Let `A` be a ring, `ι` a coordinate type, `P = P^n_A = ProjectiveSpace A ι` and
`i : Y ⟶ P` a morphism over `Spec A` (`i ≫ toSpec A ι = πY`). For `g : T ⟶ Spec A` write
`p : P_T = P ×_{Spec A} T ⟶ P` for the projection and `i_T : Y_T ⟶ P_T` for the base change of `i`
(`immersionBaseChange`, `HilbertScheme/Immersed/Functor`). For an immersion `i`, let
`C = i.ker` be its scheme-theoretic image and `U = i.coborderRange` the largest open of `P`
containing the image of `i` in which that image is closed. A closed subscheme `W ⊆ P_T` is
*contained in `Y`* if its inclusion factors through `i_T`.

* `comap_fst_le_iff_exists_lift`: for any closed `C ⊆ P`, `W ⊆ C_T` (that is,
  `C.comap p ≤ W`) if and only if `W ⟶ P_T ⟶ P` factors through `C`;
* `comap_ker_le_of_comp_eq` and `fst_mem_coborderRange_of_comp_eq`: a closed subscheme contained
  in `Y` lies in `C_T` and in `U_T` (for any morphism `i`, and for an immersion `i`);
* `exists_lift_immersionBaseChange_iff_closed_and_open`: **conversely, for a quasi-compact
  immersion `i`, a closed subscheme of `P_T` lying in `C_T` and in `U_T` is contained in `Y`**.
  The proof is Mathlib's cartesian square `Y = im(i) ×_P U`
  (`IsImmersion.isPullback_toImage_liftCoborder`; quasi-compactness is needed there), followed by
  the cartesian square of `i_T` (`isPullback_immersionBaseChange`);
* `exists_lift_immersionBaseChange_iff`: for a closed immersion `i` the open condition is void: a
  closed subscheme of `P_T` is contained in `Y` if and only if it lies in `C_T`, the kernel of
  `i_T` (`ker_immersionBaseChange`, through Mathlib's `ker_fst_of_isClosedImmersion`).

Consequently, as Mathlib `Subfunctor`s of `hilbertFunctor ι Φ` on all schemes over `Spec A`:

* `immersedHilbertSubfunctor_eq_inf`: **for a quasi-compact immersion `i`, the families of
  `Hilb^Φ` contained in `Y` are `Hilb^Φ_C ⊓ Hilb^Φ_U`**, the meet of the Hilbert subfunctor of the
  closed subscheme `C` (`closedHilbertSubfunctor`, `HilbertScheme/ClosedSubscheme/Representability`)
  and that of the open `U` (`openHilbertSubfunctor`, `HilbertScheme/OpenSubfunctor`). Over a
  Noetherian ring and with finitely many coordinates every immersion into `P` is quasi-compact
  (`quasiCompact_of_isImmersion_of_isLocallyNoetherian`, used in
  `HilbertScheme/Immersed/Representability`).
* `immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker`: for a closed immersion `i`, the
  families contained in `Y` are the Hilbert subfunctor of `C = i.ker`; for a closed subscheme
  `C ⊆ P` and its inclusion `i = C.subschemeι` this is `immersedHilbertSubfunctor_subschemeι`.
  Together with `immersedHilbertFunctorIso` it identifies the Hilbert subfunctor of `C` with the
  Nitsure-form Hilbert functor of `C` (closed subschemes of `C_T`, whose properness over `T` is
  automatic, `isImmersedHilbertFamily_iff_of_isClosedImmersion`).
* `locallyNoetherianImmersedHilbertSubfunctor i hi Φ`: the restriction of
  `immersedHilbertSubfunctor i hi Φ` to locally Noetherian test schemes (through
  `Scheme.LocalRepresentability.restrictSubfunctor`, as for `Hilb^Φ_C` and `Hilb^Φ_U`), and
  `locallyNoetherianImmersedHilbertFunctorIso` (`[Finite ι]`, `[IsPreimmersion i]`): the restricted
  Nitsure-form Hilbert functor `locallyNoetherianImmersedHilbertFunctor i hi Φ` is isomorphic to
  it, by `immersedHilbertFunctorIso` restricted to locally Noetherian test schemes; and
  `map_comap_immersionBaseChange_of_mem` (no hypothesis on `i`): a family contained in `Y` is the
  image of its pullback to `Y_T`.

This is the combination step of Nitsure's proof of Thm 6.1 (*Construction of Hilbert and Quot
schemes*, arXiv:math/0504590v1, p. 28) for `E = 𝒪` and trivial bundles: there `X ⊆ P(V)` is open
in its schematic closure `X'`, the Hilbert functor of `X` is an open subfunctor of that of `X'`
(the two Exercises on p. 28), and that of the closed `X'` is a closed subfunctor of `Hilb^Φ` of
`P(V)` (p. 25, Lemma 5.4 (ii) and after it). Here `C` is the schematic closure `X'` and `U` an
open of `P` with `X = X' ∩ U`; the identification is made on families in `P_T` contained in `Y_T`.
Their comparison with closed subschemes of `Y_T` proper over `T` is `immersedHilbertFunctorIso`,
which Nitsure uses only implicitly; the one-step comparison along `i_T` is a route choice.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {ι : Type u} {A : Type u} [CommRing A] {Y : Scheme.{u}}
  {πY : Y ⟶ Spec (CommRingCat.of A)} (i : Y ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πY)

section Factorization

variable {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
  (W : (pullback (toSpec A ι) g).IdealSheafData)

/-- **Lying in `C_T`**: for a closed subscheme `C ⊆ P^n_A` and a closed subscheme
`W ⊆ P^n_A ×_{Spec A} T`, `C.comap p ≤ W` (that is, `W ⊆ C_T`, for the projection
`p : P^n_A ×_{Spec A} T ⟶ P^n_A`) if and only if `W ⟶ P^n_A ×_{Spec A} T ⟶ P^n_A` factors through
`C`. -/
theorem comap_fst_le_iff_exists_lift (C : (ProjectiveSpace A ι).IdealSheafData) :
    C.comap (pullback.fst (toSpec A ι) g) ≤ W ↔
      ∃ a : W.subscheme ⟶ C.subscheme,
        a ≫ C.subschemeι = W.subschemeι ≫ pullback.fst (toSpec A ι) g :=
  Scheme.IdealSheafData.le_map_iff_comap_le.symm.trans
    (Scheme.IdealSheafData.exists_lift_subschemeι_iff_le_ker C
      (W.subschemeι ≫ pullback.fst (toSpec A ι) g)).symm

variable {g W}

/-- **A family contained in `Y` lies in the scheme-theoretic image of `Y`**: if the inclusion of a
closed subscheme `W ⊆ P^n_A ×_{Spec A} T` factors through `i_T`, then `W ⊆ C_T` for `C = i.ker`.
No hypothesis on `i` is needed. -/
theorem comap_ker_le_of_comp_eq {w : W.subscheme ⟶ pullback πY g}
    (hw : w ≫ immersionBaseChange i hi g = W.subschemeι) :
    i.ker.comap (pullback.fst (toSpec A ι) g) ≤ W := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
  have h := Scheme.Hom.le_ker_comp (w ≫ pullback.fst πY g) i
  rw [Category.assoc, ← immersionBaseChange_fst i hi g, ← Category.assoc, hw] at h
  exact h

/-- **A family contained in `Y` lies in `U_T`**: for an immersion `i`, if the inclusion of a closed
subscheme `W ⊆ P^n_A ×_{Spec A} T` factors through `i_T`, then every point of `W` maps into
`U = i.coborderRange`, which contains the image of `i`. -/
theorem fst_mem_coborderRange_of_comp_eq [IsImmersion i] {w : W.subscheme ⟶ pullback πY g}
    (hw : w ≫ immersionBaseChange i hi g = W.subschemeι) :
    ∀ x ∈ W.support, pullback.fst (toSpec A ι) g x ∈ i.coborderRange := by
  intro x hx
  have hx' : x ∈ Set.range W.subschemeι := by
    rw [W.range_subschemeι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  have h : (W.subschemeι ≫ pullback.fst (toSpec A ι) g) y = (w ≫ pullback.fst πY g ≫ i) y := by
    rw [← hw, Category.assoc, immersionBaseChange_fst]
  simp only [Scheme.Hom.comp_apply] at h
  rw [h]
  change _ ∈ coborder (Set.range i)
  exact subset_coborder ⟨_, rfl⟩

/-- **Families contained in an immersed `Y`** (the combination step of Nitsure,
arXiv:math/0504590v1, Thm 6.1, p. 28): for a quasi-compact immersion `i : Y ⟶ P^n_A` over
`Spec A`, the inclusion of a closed subscheme `W ⊆ P^n_A ×_{Spec A} T` factors through
`i_T : Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T` if and only if `W` lies in `C_T` for the
scheme-theoretic image `C = i.ker` and every point of `W` maps into `U = i.coborderRange`. -/
theorem exists_lift_immersionBaseChange_iff_closed_and_open [IsImmersion i] [QuasiCompact i] :
    (∃ w : W.subscheme ⟶ pullback πY g, w ≫ immersionBaseChange i hi g = W.subschemeι) ↔
      i.ker.comap (pullback.fst (toSpec A ι) g) ≤ W ∧
        ∀ x ∈ W.support, pullback.fst (toSpec A ι) g x ∈ i.coborderRange := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨comap_ker_le_of_comp_eq i hi hw, fst_mem_coborderRange_of_comp_eq i hi hw⟩
  · rintro ⟨hC, hU⟩
    obtain ⟨a, ha⟩ := (comap_fst_le_iff_exists_lift g W i.ker).1 hC
    have hrange : Set.range (W.subschemeι ≫ pullback.fst (toSpec A ι) g) ⊆
        Set.range i.coborderRange.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      have hy : W.subschemeι y ∈ W.support := by
        have h : W.subschemeι y ∈ Set.range W.subschemeι := ⟨y, rfl⟩
        rw [W.range_subschemeι] at h
        exact h
      rw [Scheme.Hom.comp_apply]
      exact hU _ hy
    obtain ⟨b, hb⟩ : ∃ b : W.subscheme ⟶ i.coborderRange,
        b ≫ i.coborderRange.ι = W.subschemeι ≫ pullback.fst (toSpec A ι) g :=
      ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ _⟩
    have hsq := IsImmersion.isPullback_toImage_liftCoborder i
    obtain ⟨c, hc⟩ : ∃ c : W.subscheme ⟶ Y,
        c ≫ i = W.subschemeι ≫ pullback.fst (toSpec A ι) g := by
      refine ⟨hsq.lift a b (ha.trans hb.symm), ?_⟩
      calc hsq.lift a b (ha.trans hb.symm) ≫ i =
            hsq.lift a b (ha.trans hb.symm) ≫ i.toImage ≫ i.imageι := by
              rw [i.toImage_imageι]
        _ = a ≫ i.imageι := by rw [← Category.assoc, hsq.lift_fst]
        _ = W.subschemeι ≫ pullback.fst (toSpec A ι) g := ha
    exact ⟨(isPullback_immersionBaseChange i hi g).lift W.subschemeι c hc.symm,
      (isPullback_immersionBaseChange i hi g).lift_fst _ _ _⟩

end Factorization

section ClosedImmersion

/-- **The kernel of `i_T`**: for a closed immersion `i : Y ⟶ P^n_A`, the base change
`i_T : Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T` has kernel `C_T`, the pullback of `C = i.ker` along
`P^n_A ×_{Spec A} T ⟶ P^n_A` (Mathlib's `ker_fst_of_isClosedImmersion` for the cartesian square
`isPullback_immersionBaseChange`). -/
theorem ker_immersionBaseChange [IsClosedImmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) :
    (immersionBaseChange i hi g).ker = i.ker.comap (pullback.fst (toSpec A ι) g) := by
  rw [← (isPullback_immersionBaseChange i hi g).isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- **Closed subschemes of `P^n_A ×_{Spec A} T` contained in a closed `Y_T`**: for a closed
immersion `i : Y ⟶ P^n_A`, a closed subscheme `V ⊆ P^n_A ×_{Spec A} T` factors through
`i_T : Y ×_{Spec A} T ⟶ P^n_A ×_{Spec A} T` if and only if `V ⊆ C_T` for `C = i.ker`, that is,
`C_T ≤ V` as ideal sheaves. -/
theorem exists_lift_immersionBaseChange_iff [IsClosedImmersion i] {T : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (V : (pullback (toSpec A ι) g).IdealSheafData) :
    (∃ w : V.subscheme ⟶ pullback πY g, w ≫ immersionBaseChange i hi g = V.subschemeι) ↔
      i.ker.comap (pullback.fst (toSpec A ι) g) ≤ V := by
  rw [← ker_immersionBaseChange i hi g]
  constructor
  · rintro ⟨w, hw⟩
    rw [← V.ker_subschemeι, ← hw]
    exact Scheme.Hom.le_ker_comp w _
  · intro h
    rw [← V.ker_subschemeι] at h
    exact ⟨IsClosedImmersion.lift _ _ h, IsClosedImmersion.lift_fac _ _ _⟩

/-- **The families of `Hilb^Φ` contained in a closed `Y` are the Hilbert subfunctor of `C`**: for a
closed immersion `i : Y ⟶ P^n_A`, the subfunctor of `hilbertFunctor ι Φ` of the families whose
inclusion factors through `i_T` is the Hilbert subfunctor of the closed subscheme `C = i.ker`. -/
theorem immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker [IsClosedImmersion i]
    (Φ : ℚ[X]) : immersedHilbertSubfunctor i hi Φ = closedHilbertSubfunctor ι Φ i.ker :=
  Subfunctor.ext <| funext fun T => Set.ext fun W =>
    exists_lift_immersionBaseChange_iff i hi T.unop.hom W.1

end ClosedImmersion

section Subfunctor

variable (Φ : ℚ[X])

/-- Membership in the families of `Hilb^Φ` contained in an immersed `Y`, for a quasi-compact
immersion: the point lies in the Hilbert subfunctors of `C = i.ker` and of `U = i.coborderRange`. -/
theorem mem_immersedHilbertSubfunctor_obj_iff_closed_and_open [IsImmersion i] [QuasiCompact i]
    {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (W : (hilbertFunctor ι Φ).obj T) :
    W ∈ (immersedHilbertSubfunctor i hi Φ).obj T ↔
      W ∈ (closedHilbertSubfunctor ι Φ i.ker).obj T ∧
        W ∈ (openHilbertSubfunctor ι Φ i.coborderRange).obj T :=
  exists_lift_immersionBaseChange_iff_closed_and_open i hi (g := T.unop.hom) (W := W.1)

/-- **The families of `Hilb^Φ` contained in an immersed scheme** (the combination step of Nitsure,
arXiv:math/0504590v1, Thm 6.1, p. 28, for `E = 𝒪`): for a quasi-compact immersion
`i : Y ⟶ P^n_A` over `Spec A`, the subfunctor of `hilbertFunctor ι Φ` of the families contained
in `Y` is the meet of the Hilbert subfunctor of the scheme-theoretic image `C = i.ker` (a closed
subfunctor) and that of the open `U = i.coborderRange` (an open subfunctor). -/
theorem immersedHilbertSubfunctor_eq_inf [IsImmersion i] [QuasiCompact i] :
    immersedHilbertSubfunctor i hi Φ =
      closedHilbertSubfunctor ι Φ i.ker ⊓ openHilbertSubfunctor ι Φ i.coborderRange := by
  ext T W
  exact mem_immersedHilbertSubfunctor_obj_iff_closed_and_open i hi Φ W

/-- **Families contained in a closed subscheme** `C ⊆ P^n_A`: for the inclusion
`i = C.subschemeι`, the families of `Hilb^Φ` whose inclusion factors through `i_T` are the points
of the Hilbert subfunctor of `C` (`W ⊆ C_T`); the case `i = C.subschemeι` of
`immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker`, since `C.subschemeι.ker = C`. -/
theorem immersedHilbertSubfunctor_subschemeι (C : (ProjectiveSpace A ι).IdealSheafData) :
    immersedHilbertSubfunctor C.subschemeι rfl Φ = closedHilbertSubfunctor ι Φ C :=
  (immersedHilbertSubfunctor_eq_closedHilbertSubfunctor_ker C.subschemeι rfl Φ).trans
    (congrArg (closedHilbertSubfunctor ι Φ) C.ker_subschemeι)

/-- **The families of `Hilb^Φ` contained in `Y`, on locally Noetherian test schemes**: the
restriction of `immersedHilbertSubfunctor i hi Φ`, a subfunctor of
`locallyNoetherianHilbertFunctor ι A Φ`. -/
abbrev locallyNoetherianImmersedHilbertSubfunctor :
    Subfunctor (locallyNoetherianHilbertFunctor ι A Φ) :=
  Scheme.LocalRepresentability.restrictSubfunctor (Scheme.locallyNoetherianOver _)
    (immersedHilbertSubfunctor i hi Φ)

/-- **The Hilbert functor of an immersed scheme on locally Noetherian test schemes is the
subfunctor of families contained in it**: for a preimmersion `i` and finitely many coordinates,
`immersedHilbertFunctorIso i hi Φ` restricted to locally Noetherian test schemes, from
`locallyNoetherianImmersedHilbertFunctor i hi Φ` (closed subschemes of `Y_T` proper over `T`) onto
`locallyNoetherianImmersedHilbertSubfunctor i hi Φ`. -/
def locallyNoetherianImmersedHilbertFunctorIso [IsPreimmersion i] [Finite ι] :
    locallyNoetherianImmersedHilbertFunctor i hi Φ ≅
      (locallyNoetherianImmersedHilbertSubfunctor i hi Φ).toFunctor :=
  NatIso.ofComponents (fun T => (immersedHilbertFunctorIso i hi Φ).app (op T.unop.obj))
    fun f => (immersedHilbertFunctorIso i hi Φ).hom.naturality
      ((Scheme.locallyNoetherianOverInclusion _).op.map f)

/-- **A family contained in `Y` is the image of its pullback to `Y_T`**: a point `W` of
`Hilb^Φ(T)` whose inclusion factors through `i_T` satisfies `(W.comap i_T).map i_T = W`
(`Scheme.IdealSheafData.map_comap_of_comp_eq`, `IdealSheaf/Monomorphism`). No hypothesis on `i`
is needed. -/
theorem map_comap_immersionBaseChange_of_mem {T : (Over (Spec (CommRingCat.of A)))ᵒᵖ}
    {W : (hilbertFunctor ι Φ).obj T} (hW : W ∈ (immersedHilbertSubfunctor i hi Φ).obj T) :
    (W.1.comap (immersionBaseChange i hi T.unop.hom)).map (immersionBaseChange i hi T.unop.hom) =
      W.1 := by
  obtain ⟨w, hw⟩ := hW
  exact Scheme.IdealSheafData.map_comap_of_comp_eq W.1 _ w hw

theorem locallyNoetherianImmersedHilbertFunctorIso_hom_app_coe [IsPreimmersion i] [Finite ι]
    (T : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ)
    (V : (locallyNoetherianImmersedHilbertFunctor i hi Φ).obj T) :
    ((locallyNoetherianImmersedHilbertFunctorIso i hi Φ).hom.app T V).1.1 =
      V.1.map (immersionBaseChange i hi T.unop.obj.hom) :=
  rfl

theorem locallyNoetherianImmersedHilbertFunctorIso_inv_app_coe [IsPreimmersion i] [Finite ι]
    (T : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ)
    (W : (locallyNoetherianImmersedHilbertSubfunctor i hi Φ).toFunctor.obj T) :
    ((locallyNoetherianImmersedHilbertFunctorIso i hi Φ).inv.app T W).1 =
      W.1.1.comap (immersionBaseChange i hi T.unop.obj.hom) :=
  rfl

end Subfunctor

end AlgebraicGeometry.ProjectiveSpace

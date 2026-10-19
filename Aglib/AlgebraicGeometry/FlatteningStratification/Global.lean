/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.AffineBase
public import Aglib.AlgebraicGeometry.IdealSheaf.GlueImmersion

/-!
# The flattening stratification over a locally Noetherian base

Let `A` be a ring, `s : S ⟶ Spec A` with `S` locally Noetherian, `ι ≃ Fin (n + 1)`,
`X_S = P^n_A ×_{Spec A} S` (`pullback (toSpec A ι) s`) and `F` a coherent module on `X_S`, flat or
not. This file proves Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
Thm 4.3 (p. 19), over `S`, for locally Noetherian test schemes. The pullback of `F` to a test
scheme `g : T ⟶ S` is taken on the native fibre product `X_S ×_S T`, flat over `T` through
`pullback.snd`. The fibre Hilbert polynomial `P_y` at `y ∈ S` is `fiberHilbertPolynomialAt ι s F y`
(`AffineBase`).

* **The strata** (`flatteningStratum ι s n e hF f`, with the immersion `flatteningStratumι`): for
  every polynomial `f`, a locally Noetherian scheme with an immersion into `S` such that, for
  locally Noetherian `T`, `g : T ⟶ S` factors through it if and only if the pullback of `F` to
  `X_S ×_S T` is flat over `T` and `P_{g t} = f` for every `t ∈ T`
  (`exists_lift_flatteningStratumι_iff`). It is obtained by gluing
  (`Scheme.exists_isImmersion_forall_exists_lift_iff`, in `IdealSheaf/GlueImmersion`): over an
  affine open `U`, the condition is represented by the affine stratum `S_f` of the restriction of
  `F` to `P^n_{Γ(S, U)}` (`exists_lift_hilbertPolynomialStratumι_comp_fromSpec_iff`), for any
  bound of the fibre statements of (B) and (C) over `U`, or by the empty scheme if `f` does not
  occur over `U`. No common bound over `S` is needed, and quasi-compactness of `S` is used only for
  the finiteness of the set of polynomials that occur (`finite_range_fiberHilbertPolynomialAt`).
  Over an affine open `U`, `S_f ×_S U` is the affine stratum of `F_U`
  (`exists_iso_pullback_flatteningStratumι`), and `S_f` is unique up to unique isomorphism
  (`exists_iso_flatteningStratum`).
* **Theorem 4.3 (i)** (`range_flatteningStratumι`): `|S_f| = {y : P_y = f}`, for every `f`.
* **Theorem 4.3 (ii)** (`exists_lift_flatteningStrataι_iff`): `∐ S_f ⟶ S`, `f` over the
  polynomials that occur, is a monomorphism (`mono_flatteningStrataι`), and a morphism from a
  locally Noetherian `T` factors through it if and only if the pullback of `F` to `X_S ×_S T` is
  flat over `T`; "⇒" holds for every `T` (`relativeFlat_of_exists_lift_flatteningStrataι`), and
  `F` is flat over `∐ S_f` (`relativeFlat_flatteningStrata`).
* **Theorem 4.3 (iii)** (`closure_range_flatteningStratumι_subset`): the closure of `|S_f|` lies in
  the union of the `|S_g|`, `g` occurring with `f(m) ≤ g(m)` for `m ≫ 0`; it is read on an affine
  open around each point of the closure, from the affine statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} [IsLocallyNoetherian S]
  (s : S ⟶ Spec (CommRingCat.of A)) (n : ℕ) (e : ι ≃ Fin (n + 1))
  {F : (pullback (toSpec A ι) s).Modules}
  (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F)

include e hF in
/-- **The strata over an affine open.** For an affine open `U` of `S`, a bound `N` of the fibre
statements of (B) and (C) for the restriction `F_U` of `F` to `P^n_{Γ(S, U)}` and a polynomial `f`
that occurs over `U`, a morphism `g' ≫ U.fromSpec` from a locally Noetherian `T` factors through
`S_f(F_U) ⟶ Spec Γ(S, U) ⟶ S` if and only if the pullback of `F` to `X_S ×_S T` is flat over `T`
and all fibre Hilbert polynomials are `f`. -/
theorem exists_lift_hilbertPolynomialStratumι_comp_fromSpec_iff {U : S.Opens}
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(S, U)] {N : ℕ}
    (hN : IsFiberBaseChangeBound (affineBaseModule ι s F hU) N) (f : Polynomial ℚ)
    (hf : f ∈ Set.range (fiberHilbertPolynomial (affineBaseModule ι s F hU)))
    {T : Scheme.{u}} [IsLocallyNoetherian T] (g' : T ⟶ Spec Γ(S, U)) :
    (∃ h : T ⟶ hilbertPolynomialStratum n e (affineBaseModule ι s F hU)
        (affineLocallyFiniteType_affineBaseModule ι s n e hF hU) N f,
        h ≫ hilbertPolynomialStratumι n e (affineBaseModule ι s F hU)
          (affineLocallyFiniteType_affineBaseModule ι s n e hF hU) N f ≫ hU.fromSpec =
          g' ≫ hU.fromSpec) ↔
      relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) (g' ≫ hU.fromSpec))
          ((Scheme.Modules.pullback
            (pullback.fst (pullback.snd (toSpec A ι) s) (g' ≫ hU.fromSpec))).obj F) ∧
        ∀ t : T, fiberHilbertPolynomialAt ι s F ((g' ≫ hU.fromSpec) t) = f := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  have h1 := exists_lift_hilbertPolynomialStratumι_iff_relativeFlat n e _
    (affineLocallyFiniteType_affineBaseModule ι s n e hF hU) hN f hf g'
  have h2 := relativeFlat_pullback_affineBaseMap_iff ι s F hU g'
  have h3 : ∀ t : T, fiberHilbertPolynomialAt ι s F ((g' ≫ hU.fromSpec) t) =
      fiberHilbertPolynomial (affineBaseModule ι s F hU) (g' t) := fun t =>
    fiberHilbertPolynomialAt_fromSpec ι s F hU (g' t)
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨hfl, hpts⟩ := h1.mp ⟨h, (cancel_mono hU.fromSpec).mp (by rwa [Category.assoc])⟩
    exact ⟨h2.mpr hfl, fun t => (h3 t).trans (hpts t)⟩
  · rintro ⟨hfl, hpts⟩
    obtain ⟨h, hh⟩ := h1.mpr ⟨h2.mp hfl, fun t => (h3 t).symm.trans (hpts t)⟩
    exact ⟨h, by rw [← Category.assoc, hh]⟩

include e hF in
/-- **Existence of the stratum `S_f`** over a locally Noetherian base, for every polynomial `f`:
an immersion into `S` along which a morphism from a locally Noetherian `T` factors exactly when
the pullback of `F` to `X_S ×_S T` is flat over `T` with all fibre Hilbert polynomials `f`. -/
theorem exists_isImmersion_flatteningStratum (f : Polynomial ℚ) :
    ∃ (Z : Scheme.{u}) (m : Z ⟶ S), IsImmersion m ∧
      ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ S),
        (∃ h : T ⟶ Z, h ≫ m = g) ↔
          relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
              ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F) ∧
            ∀ t : T, fiberHilbertPolynomialAt ι s F (g t) = f := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  refine exists_isImmersion_forall_exists_lift_iff
    (fun T g => relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F) ∧
        ∀ t : T, fiberHilbertPolynomialAt ι s F (g t) = f) ?_ ?_ ?_
  · rintro T _ g V ⟨hfl, hpts⟩
    exact ⟨relativeFlat_pullback_snd_opensι _ F g V hfl, fun t => hpts _⟩
  · intro T _ g H
    refine ⟨relativeFlat_pullback_snd_of_forall_opens _ F g fun t => ?_, fun t => ?_⟩
    · obtain ⟨V, htV, hV, -⟩ := H t
      exact ⟨V, htV, hV⟩
    · obtain ⟨V, htV, -, hV⟩ := H t
      exact hV ⟨t, htV⟩
  · intro x
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
    have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hFU := affineLocallyFiniteType_affineBaseModule ι s n e hF hU
    refine ⟨U, hxU, ?_⟩
    by_cases hf : f ∈ Set.range (fiberHilbertPolynomial (affineBaseModule ι s F hU))
    · obtain ⟨N, hN⟩ := exists_isFiberBaseChangeBound n e _ hFU
      refine ⟨_, hilbertPolynomialStratumι n e _ hFU N f ≫ hU.fromSpec, inferInstance, ?_,
        fun T _ g hg => ?_⟩
      · rintro _ ⟨z, rfl⟩
        rw [Scheme.Hom.comp_apply, ← hU.range_fromSpec]
        exact ⟨_, rfl⟩
      · obtain ⟨g', rfl⟩ : ∃ g' : T ⟶ Spec Γ(S, U), g' ≫ hU.fromSpec = g :=
          ⟨IsOpenImmersion.lift hU.fromSpec g (by rwa [hU.range_fromSpec]),
            IsOpenImmersion.lift_fac _ _ _⟩
        exact (exists_lift_hilbertPolynomialStratumι_comp_fromSpec_iff ι s n e hF hU hN f hf
          g').symm
    · refine ⟨_, (⊥ : S.Opens).ι, inferInstance, by simp, fun T _ g hg => ?_⟩
      constructor
      · rintro ⟨-, hpts⟩
        have : IsEmpty T := ⟨fun t => hf ⟨_,
          (fiberHilbertPolynomialAt_eq ι s F hU (g t) (hg ⟨t, rfl⟩)).symm.trans (hpts t)⟩⟩
        exact ⟨IsOpenImmersion.lift _ g (fun _ ⟨t, _⟩ => (IsEmpty.false t).elim),
          IsOpenImmersion.lift_fac _ _ _⟩
      · rintro ⟨h, -⟩
        have : IsEmpty T := ⟨fun t => by simpa using (h t).2⟩
        exact ⟨fun x => (IsEmpty.false (pullback.snd _ g x)).elim,
          fun t => (IsEmpty.false t).elim⟩

/-- **Nitsure's stratum `S_f`** (arXiv:math/0504590v1, Thm 4.3, p. 19) over the locally
Noetherian base `S`, for a polynomial `f`: a locally Noetherian scheme with an immersion into `S`
(`flatteningStratumι`) representing, on locally Noetherian schemes, flatness of the pullback of `F`
with fibre Hilbert polynomial `f` (`exists_lift_flatteningStratumι_iff`). It is empty unless `f`
occurs. -/
def flatteningStratum (f : Polynomial ℚ) : Scheme.{u} :=
  (exists_isImmersion_flatteningStratum ι s n e hF f).choose

/-- The immersion `S_f ⟶ S`. -/
def flatteningStratumι (f : Polynomial ℚ) : flatteningStratum ι s n e hF f ⟶ S :=
  (exists_isImmersion_flatteningStratum ι s n e hF f).choose_spec.choose

instance (f : Polynomial ℚ) : IsImmersion (flatteningStratumι ι s n e hF f) :=
  (exists_isImmersion_flatteningStratum ι s n e hF f).choose_spec.choose_spec.1

instance (f : Polynomial ℚ) : IsLocallyNoetherian (flatteningStratum ι s n e hF f) :=
  LocallyOfFiniteType.isLocallyNoetherian (flatteningStratumι ι s n e hF f)

/-- **The universal property of the stratum `S_f`** (Nitsure, arXiv:math/0504590v1, Thm 4.3 (ii),
for one stratum): a morphism `g : T ⟶ S` from a locally Noetherian `T` factors through `S_f` if and
only if the pullback of `F` to `X_S ×_S T` is flat over `T` and every fibre Hilbert polynomial
`P_{g t}` is `f`. -/
theorem exists_lift_flatteningStratumι_iff (f : Polynomial ℚ) {T : Scheme.{u}}
    [IsLocallyNoetherian T] (g : T ⟶ S) :
    (∃ h : T ⟶ flatteningStratum ι s n e hF f, h ≫ flatteningStratumι ι s n e hF f = g) ↔
      relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F) ∧
        ∀ t : T, fiberHilbertPolynomialAt ι s F (g t) = f :=
  (exists_isImmersion_flatteningStratum ι s n e hF f).choose_spec.choose_spec.2 g

/-- **`F` is flat over every stratum** (Nitsure, arXiv:math/0504590v1, proof of Thm 4.3 (ii),
p. 22). -/
theorem relativeFlat_flatteningStratum (f : Polynomial ℚ) :
    relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) (flatteningStratumι ι s n e hF f))
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s)
        (flatteningStratumι ι s n e hF f))).obj F) :=
  ((exists_lift_flatteningStratumι_iff ι s n e hF f _).mp ⟨𝟙 _, Category.id_comp _⟩).1

include e hF in
/-- **The stratum `S_f` is unique up to unique isomorphism** (compare Nitsure,
arXiv:math/0504590v1, Thm 4.3 (ii), "the subscheme `S_f` is uniquely determined"): a monomorphism
`m : Z ⟶ S` from a locally Noetherian `Z` with the universal property of `S_f` on locally
Noetherian schemes is isomorphic to `S_f ⟶ S` over `S`. In particular `flatteningStratum` does not
depend on the choices made in its construction. -/
theorem exists_iso_flatteningStratum (f : Polynomial ℚ) {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (m : Z ⟶ S) [Mono m]
    (hm : ∀ ⦃T : Scheme.{u}⦄ [IsLocallyNoetherian T] (g : T ⟶ S),
      (∃ h : T ⟶ Z, h ≫ m = g) ↔
        relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F) ∧
          ∀ t : T, fiberHilbertPolynomialAt ι s F (g t) = f) :
    ∃ φ : Z ≅ flatteningStratum ι s n e hF f, φ.hom ≫ flatteningStratumι ι s n e hF f = m := by
  obtain ⟨a, ha⟩ := (exists_lift_flatteningStratumι_iff ι s n e hF f m).mpr
    ((hm m).mp ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨b, hb⟩ := (hm (flatteningStratumι ι s n e hF f)).mpr
    ((exists_lift_flatteningStratumι_iff ι s n e hF f _).mp ⟨𝟙 _, Category.id_comp _⟩)
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · rw [← cancel_mono m, Category.assoc, hb, ha, Category.id_comp]
  · rw [← cancel_mono (flatteningStratumι ι s n e hF f), Category.assoc, ha, hb, Category.id_comp]

include e hF in
/-- **Over an affine open, `S_f` is the affine stratum** (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3, p. 20, the reduction to an affine base): for an affine open `U` of `S`, a bound `N` of the
fibre statements of (B) and (C) for the restriction `F_U` of `F` to `P^n_{Γ(S, U)}` and `f` that
occurs over `U`, the base change `S_f ×_S U` is isomorphic over `Spec Γ(S, U)` to the affine
stratum `S_f(F_U)` of `HilbertPolynomial`. -/
theorem exists_iso_pullback_flatteningStratumι {U : S.Opens} (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(S, U)] {N : ℕ} (hN : IsFiberBaseChangeBound (affineBaseModule ι s F hU) N)
    (f : Polynomial ℚ) (hf : f ∈ Set.range (fiberHilbertPolynomial (affineBaseModule ι s F hU))) :
    ∃ φ : pullback (flatteningStratumι ι s n e hF f) hU.fromSpec ≅
        hilbertPolynomialStratum n e (affineBaseModule ι s F hU)
          (affineLocallyFiniteType_affineBaseModule ι s n e hF hU) N f,
      φ.hom ≫ hilbertPolynomialStratumι n e (affineBaseModule ι s F hU)
          (affineLocallyFiniteType_affineBaseModule ι s n e hF hU) N f =
        pullback.snd (flatteningStratumι ι s n e hF f) hU.fromSpec := by
  have hFU := affineLocallyFiniteType_affineBaseModule ι s n e hF hU
  have : IsLocallyNoetherian (pullback (flatteningStratumι ι s n e hF f) hU.fromSpec) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (flatteningStratumι ι s n e hF f) hU.fromSpec)
  have : IsLocallyNoetherian (hilbertPolynomialStratum n e _ hFU N f) :=
    LocallyOfFiniteType.isLocallyNoetherian (hilbertPolynomialStratumι n e _ hFU N f)
  obtain ⟨a, ha⟩ := (exists_lift_hilbertPolynomialStratumι_comp_fromSpec_iff ι s n e hF hU hN f hf
    (pullback.snd (flatteningStratumι ι s n e hF f) hU.fromSpec)).mpr
      ((exists_lift_flatteningStratumι_iff ι s n e hF f _).mp
        ⟨pullback.fst _ _, pullback.condition⟩)
  have ha' : a ≫ hilbertPolynomialStratumι n e _ hFU N f =
      pullback.snd (flatteningStratumι ι s n e hF f) hU.fromSpec :=
    (cancel_mono hU.fromSpec).mp (by rw [Category.assoc, ha])
  obtain ⟨k, hk⟩ := (exists_lift_flatteningStratumι_iff ι s n e hF f
    (hilbertPolynomialStratumι n e _ hFU N f ≫ hU.fromSpec)).mpr
      ((exists_lift_hilbertPolynomialStratumι_comp_fromSpec_iff ι s n e hF hU hN f hf
        (hilbertPolynomialStratumι n e _ hFU N f)).mp ⟨𝟙 _, Category.id_comp _⟩)
  let b := pullback.lift k (hilbertPolynomialStratumι n e _ hFU N f) hk
  have hb : b ≫ pullback.snd (flatteningStratumι ι s n e hF f) hU.fromSpec =
      hilbertPolynomialStratumι n e _ hFU N f := pullback.lift_snd _ _ _
  refine ⟨⟨a, b, ?_, ?_⟩, ha'⟩
  · rw [← cancel_mono (pullback.snd (flatteningStratumι ι s n e hF f) hU.fromSpec),
      Category.assoc, hb, ha', Category.id_comp]
  · rw [← cancel_mono (hilbertPolynomialStratumι n e _ hFU N f), Category.assoc, ha', hb,
      Category.id_comp]

include e hF in
/-- **Nitsure's Theorem 4.3 (i)** (arXiv:math/0504590v1, p. 19, and proof, p. 22) over the
locally Noetherian base `S`: the underlying set of `S_f` consists of the points `y` with
`P_y = f`, for every polynomial `f`. -/
theorem range_flatteningStratumι (f : Polynomial ℚ) :
    Set.range (flatteningStratumι ι s n e hF f) = {y | fiberHilbertPolynomialAt ι s F y = f} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ((exists_lift_flatteningStratumι_iff ι s n e hF f
      (flatteningStratumι ι s n e hF f)).mp ⟨𝟙 _, Category.id_comp _⟩).2 z
  · intro hy
    have : Finite ι := Finite.of_equiv _ e.symm
    have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
    obtain ⟨U, hU, hyU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
    have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hFU := affineLocallyFiniteType_affineBaseModule ι s n e hF hU
    obtain ⟨N, hN⟩ := exists_isFiberBaseChangeBound n e _ hFU
    have hyU' : fiberHilbertPolynomial (affineBaseModule ι s F hU) (hU.primeIdealOf ⟨y, hyU⟩) =
        f := (fiberHilbertPolynomialAt_eq ι s F hU y hyU).symm.trans hy
    have hf : f ∈ Set.range (fiberHilbertPolynomial (affineBaseModule ι s F hU)) := ⟨_, hyU'⟩
    have hmem : hU.primeIdealOf ⟨y, hyU⟩ ∈ Set.range (hilbertPolynomialStratumι n e _ hFU N f) := by
      rw [range_hilbertPolynomialStratumι n e _ hFU hN f hf]
      exact hyU'
    obtain ⟨z, hz⟩ := hmem
    have : IsLocallyNoetherian (hilbertPolynomialStratum n e _ hFU N f) :=
      LocallyOfFiniteType.isLocallyNoetherian (hilbertPolynomialStratumι n e _ hFU N f)
    obtain ⟨k, hk⟩ := (exists_lift_flatteningStratumι_iff ι s n e hF f
      (hilbertPolynomialStratumι n e _ hFU N f ≫ hU.fromSpec)).mpr
      ((exists_lift_hilbertPolynomialStratumι_comp_fromSpec_iff ι s n e hF hU hN f hf
        (hilbertPolynomialStratumι n e _ hFU N f)).mp ⟨𝟙 _, Category.id_comp _⟩)
    refine ⟨k z, ?_⟩
    change (k ≫ flatteningStratumι ι s n e hF f) z = y
    rw [hk, Scheme.Hom.comp_apply, hz, IsAffineOpen.fromSpec_primeIdealOf]

include e hF in
/-- **Theorem 4.3 (i), "in particular"** (Nitsure, arXiv:math/0504590v1, p. 19): the sets `|S_f|`
are pairwise disjoint and cover `S`. -/
theorem iUnion_range_flatteningStratumι_eq_univ_and_pairwiseDisjoint :
    (⋃ f ∈ Set.range (fiberHilbertPolynomialAt ι s F),
        Set.range (flatteningStratumι ι s n e hF f)) = Set.univ ∧
      Pairwise fun f g : Polynomial ℚ => Disjoint (Set.range (flatteningStratumι ι s n e hF f))
        (Set.range (flatteningStratumι ι s n e hF g)) := by
  refine ⟨Set.eq_univ_of_forall fun y => Set.mem_iUnion₂.mpr ⟨_, ⟨y, rfl⟩, ?_⟩,
    fun f g hfg => ?_⟩
  · rw [range_flatteningStratumι]
    rfl
  · dsimp only
    rw [range_flatteningStratumι, range_flatteningStratumι]
    exact Set.disjoint_left.mpr fun y h₁ h₂ => hfg (h₁.symm.trans h₂)

/-! ### The disjoint union of the strata and Theorem 4.3 (ii) -/

/-- The disjoint union `∐ S_f` of the strata, over the polynomials `f` that occur. -/
abbrev flatteningStrata : Scheme.{u} :=
  ∐ fun f : Set.range (fiberHilbertPolynomialAt ι s F) => flatteningStratum ι s n e hF f

/-- The morphism `∐ S_f ⟶ S` induced by the immersions of the strata. -/
def flatteningStrataι : flatteningStrata ι s n e hF ⟶ S :=
  Sigma.desc fun f : Set.range (fiberHilbertPolynomialAt ι s F) => flatteningStratumι ι s n e hF f

@[reassoc (attr := simp)]
theorem sigmaι_flatteningStrataι (f : Set.range (fiberHilbertPolynomialAt ι s F)) :
    Sigma.ι (fun f : Set.range (fiberHilbertPolynomialAt ι s F) =>
        flatteningStratum ι s n e hF f) f ≫ flatteningStrataι ι s n e hF =
      flatteningStratumι ι s n e hF f :=
  Sigma.ι_comp_desc _ _

include e hF in
/-- **The disjoint union of the strata is a monomorphism** into `S`: the strata are immersions with
pairwise disjoint images (Theorem 4.3 (i)). -/
theorem mono_flatteningStrataι : Mono (flatteningStrataι ι s n e hF) :=
  Scheme.mono_sigmaDesc_of_pairwise_disjoint _ fun f g hfg => by
    dsimp only
    rw [range_flatteningStratumι, range_flatteningStratumι]
    exact Set.disjoint_left.mpr fun y h₁ h₂ => hfg (Subtype.ext (h₁.symm.trans h₂))

include e hF in
/-- **Flatness after factoring through the strata** (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3 (ii), p. 22): if `g : T ⟶ S` factors through `∐ S_f`, the pullback of `F` to `X_S ×_S T`
is flat over `T`, for every `T`. -/
theorem relativeFlat_of_exists_lift_flatteningStrataι {T : Scheme.{u}} (g : T ⟶ S)
    (h : T ⟶ flatteningStrata ι s n e hF) (hg : h ≫ flatteningStrataι ι s n e hF = g) :
    relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  refine relativeFlat_pullback_snd_of_forall_opens _ F g fun t => ?_
  obtain ⟨f, y, hy⟩ := Scheme.exists_sigmaι_eq (h t)
  let ιf := Sigma.ι (fun f : Set.range (fiberHilbertPolynomialAt ι s F) =>
    flatteningStratum ι s n e hF f) f
  let V : T.Opens := h ⁻¹ᵁ ιf.opensRange
  have hsub : Set.range (V.ι ≫ h) ⊆ Set.range ιf := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  let l := IsOpenImmersion.lift ιf (V.ι ≫ h) hsub
  have hl : l ≫ flatteningStratumι ι s n e hF f = V.ι ≫ g := by
    rw [← sigmaι_flatteningStrataι ι s n e hF f, ← Category.assoc, IsOpenImmersion.lift_fac,
      Category.assoc, hg]
  refine ⟨V, show h t ∈ Set.range ιf from ⟨y, hy⟩, ?_⟩
  have := relativeFlat_of_isPullback_comp (IsPullback.of_hasPullback _ _) (j := l)
    (IsPullback.of_hasPullback (pullback.snd (toSpec A ι) s)
      (l ≫ flatteningStratumι ι s n e hF f)) F (relativeFlat_flatteningStratum ι s n e hF f)
  rwa [hl] at this

include e hF in
/-- **Flat test schemes factor through the strata** (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3 (ii), p. 22, converse direction): if `T` is locally Noetherian and the pullback of `F` to
`X_S ×_S T` is flat over `T`, then `g` factors through `∐ S_f`. Over an affine open `U` of `S`,
the restriction of `g` factors through the affine `∐ S_f` of `F_U`; near each point it lands in
one affine stratum, so the fibre Hilbert polynomials are locally constant and the restriction
factors through one `S_f`. The local factorizations glue because `∐ S_f ⟶ S` is a monomorphism. -/
theorem exists_lift_flatteningStrataι_of_relativeFlat {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ S)
    (hflat : relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F)) :
    ∃ h : T ⟶ flatteningStrata ι s n e hF, h ≫ flatteningStrataι ι s n e hF = g := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  have := mono_flatteningStrataι ι s n e hF
  refine Scheme.exists_lift_of_mono_of_forall_exists _ g fun t => ?_
  obtain ⟨U, hU, htU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (g t))
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hFU := affineLocallyFiniteType_affineBaseModule ι s n e hF hU
  obtain ⟨N, hN⟩ := exists_isFiberBaseChangeBound n e _ hFU
  refine ⟨g ⁻¹ᵁ U, htU, ?_⟩
  have hsub : Set.range ((g ⁻¹ᵁ U).ι ≫ g) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    exact v.2
  let g' := IsOpenImmersion.lift hU.fromSpec ((g ⁻¹ᵁ U).ι ≫ g) hsub
  have hg' : g' ≫ hU.fromSpec = (g ⁻¹ᵁ U).ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hflatV := relativeFlat_pullback_snd_opensι _ F g (g ⁻¹ᵁ U) hflat
  have hflat' := (relativeFlat_pullback_affineBaseMap_iff ι s F hU g').mp (by rwa [hg'])
  obtain ⟨H, hH⟩ := exists_lift_hilbertPolynomialStrataι_of_relativeFlat n e _ hFU hN g' hflat'
  refine Scheme.exists_lift_of_mono_of_forall_exists _ _ fun w => ?_
  obtain ⟨f', y, hy⟩ := Scheme.exists_sigmaι_eq (H w)
  let W := H ⁻¹ᵁ (Sigma.ι (fun f : Set.range (fiberHilbertPolynomial (affineBaseModule ι s F hU)) =>
    hilbertPolynomialStratum n e _ hFU N f) f').opensRange
  have hpts : ∀ w' : W.toScheme,
      fiberHilbertPolynomialAt ι s F ((W.ι ≫ (g ⁻¹ᵁ U).ι ≫ g) w') = f' := by
    intro w'
    obtain ⟨y', hy'⟩ : H (W.ι w') ∈ Set.range (Sigma.ι (fun f : Set.range
        (fiberHilbertPolynomial (affineBaseModule ι s F hU)) =>
          hilbertPolynomialStratum n e _ hFU N f) f') := w'.2
    have hmem : g' (W.ι w') ∈ Set.range (hilbertPolynomialStratumι n e _ hFU N f') :=
      ⟨y', by rw [← hH, Scheme.Hom.comp_apply, ← hy', ← Scheme.Hom.comp_apply,
        sigmaι_hilbertPolynomialStrataι]⟩
    have hmem' : fiberHilbertPolynomial (affineBaseModule ι s F hU) (g' (W.ι w')) = f' :=
      (Set.ext_iff.mp (range_hilbertPolynomialStratumι n e _ hFU hN _ f'.2) _).mp hmem
    rw [← hg']
    exact (fiberHilbertPolynomialAt_fromSpec ι s F hU (g' (W.ι w'))).trans hmem'
  have hf'' : (f' : Polynomial ℚ) ∈ Set.range (fiberHilbertPolynomialAt ι s F) := by
    obtain ⟨y₀, hy₀⟩ := f'.2
    exact ⟨hU.fromSpec y₀, (fiberHilbertPolynomialAt_fromSpec ι s F hU y₀).trans hy₀⟩
  obtain ⟨k, hk⟩ := (exists_lift_flatteningStratumι_iff ι s n e hF f'
    (W.ι ≫ (g ⁻¹ᵁ U).ι ≫ g)).mpr ⟨relativeFlat_pullback_snd_opensι _ F _ W hflatV, hpts⟩
  exact ⟨W, show H w ∈ Set.range _ from ⟨y, hy⟩,
    k ≫ Sigma.ι (fun f : Set.range (fiberHilbertPolynomialAt ι s F) =>
      flatteningStratum ι s n e hF f) ⟨f', hf''⟩, by
    rw [Category.assoc, sigmaι_flatteningStrataι, hk]⟩

include e hF in
/-- **Nitsure's Theorem 4.3 (ii)** (arXiv:math/0504590v1, p. 19, proof pp. 22–23) over the locally
Noetherian base `S`, for locally Noetherian test schemes: a morphism `g : T ⟶ S` from a locally
Noetherian `T` factors through the disjoint union `∐ S_f ⟶ S` of the strata, `f` ranging over the
polynomials that occur, if and only if the pullback of `F` to `X_S ×_S T` is flat over `T`. The
factorization is unique (`mono_flatteningStrataι`); "⇒" holds for every `T`
(`relativeFlat_of_exists_lift_flatteningStrataι`). -/
theorem exists_lift_flatteningStrataι_iff {T : Scheme.{u}} [IsLocallyNoetherian T] (g : T ⟶ S) :
    (∃ h : T ⟶ flatteningStrata ι s n e hF, h ≫ flatteningStrataι ι s n e hF = g) ↔
      relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F) :=
  ⟨fun ⟨h, hg⟩ => relativeFlat_of_exists_lift_flatteningStrataι ι s n e hF g h hg,
    exists_lift_flatteningStrataι_of_relativeFlat ι s n e hF g⟩

include e hF in
/-- **`F` is flat over the disjoint union of the strata** (Nitsure, arXiv:math/0504590v1,
Thm 4.3 (ii), first assertion): the pullback of `F` to `X_S ×_S ∐ S_f` is flat over `∐ S_f`. -/
theorem relativeFlat_flatteningStrata :
    relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) (flatteningStrataι ι s n e hF))
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s)
        (flatteningStrataι ι s n e hF))).obj F) :=
  relativeFlat_of_exists_lift_flatteningStrataι ι s n e hF _ (𝟙 _) (Category.id_comp _)

/-- The disjoint union of the strata is locally Noetherian. -/
instance isLocallyNoetherian_flatteningStrata :
    IsLocallyNoetherian (flatteningStrata ι s n e hF) :=
  (isLocallyNoetherian_iff_openCover (sigmaOpenCover _)).mpr
    fun (f : Set.range (fiberHilbertPolynomialAt ι s F)) => by
      have h : IsLocallyNoetherian (flatteningStratum ι s n e hF f) := inferInstance
      exact h

include e hF in
/-- **The universal property of `S_f` read on `P^n_A ×_{Spec A} T`** (the form in which a Hilbert
functor over `T` combines with the stratum): for locally Noetherian `T`, `g : T ⟶ S` factors
through `S_f` if and only if the pullback `F_T` of `F` along `pullbackBaseChange ι s g` is flat
over `T` and every fibre Hilbert polynomial of `F_T`, at the points of `T`, is `f`. This is
`exists_lift_flatteningStratumι_iff` with `relativeFlat_pullbackBaseChange_iff` and
`fiberHilbertPolynomialAt_pullbackBaseChange`. -/
theorem exists_lift_flatteningStratumι_iff_pullbackBaseChange (f : Polynomial ℚ)
    {T : Scheme.{u}} [IsLocallyNoetherian T] (g : T ⟶ S) :
    (∃ h : T ⟶ flatteningStratum ι s n e hF f, h ≫ flatteningStratumι ι s n e hF f = g) ↔
      relativeFlat (pullback.snd (toSpec A ι) (g ≫ s))
          ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj F) ∧
        ∀ t : T, fiberHilbertPolynomialAt ι (g ≫ s)
          ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj F) t = f := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  rw [exists_lift_flatteningStratumι_iff, relativeFlat_pullbackBaseChange_iff]
  simp only [fiberHilbertPolynomialAt_pullbackBaseChange]

include e hF in
/-- **Theorem 4.3 (ii) read on `P^n_A ×_{Spec A} T`**: for locally Noetherian `T`, `g : T ⟶ S`
factors through `∐ S_f` if and only if the pullback `F_T` of `F` along
`pullbackBaseChange ι s g` is flat over `T`. -/
theorem exists_lift_flatteningStrataι_iff_pullbackBaseChange {T : Scheme.{u}}
    [IsLocallyNoetherian T] (g : T ⟶ S) :
    (∃ h : T ⟶ flatteningStrata ι s n e hF, h ≫ flatteningStrataι ι s n e hF = g) ↔
      relativeFlat (pullback.snd (toSpec A ι) (g ≫ s))
        ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj F) := by
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  rw [exists_lift_flatteningStrataι_iff, relativeFlat_pullbackBaseChange_iff]

/-! ### Theorem 4.3 (iii) -/

include e hF in
/-- **Nitsure's Theorem 4.3 (iii)** (arXiv:math/0504590v1, p. 19, and proof, p. 23) over the
locally Noetherian base `S`: the closure of `|S_f|` lies in the union of the `|S_g|` over the
polynomials `g` that occur with `f ≤ g`, that is, `f(m) ≤ g(m)` for all `m ≫ 0`. A point `y` of
the closure is read in an affine open `U ∋ y`, where `|S_f| ∩ U` is the affine stratum of the
restriction of `F` (Theorem 4.3 (i) on both sides) and the affine statement
`closure_range_hilbertPolynomialStratumι_subset` applies. -/
theorem closure_range_flatteningStratumι_subset (f : Polynomial ℚ) :
    closure (Set.range (flatteningStratumι ι s n e hF f)) ⊆
      ⋃ g ∈ {g ∈ Set.range (fiberHilbertPolynomialAt ι s F) |
          ∀ᶠ m : ℕ in Filter.atTop, f.eval (m : ℚ) ≤ g.eval (m : ℚ)},
        Set.range (flatteningStratumι ι s n e hF g) := by
  intro y hy
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hFU := affineLocallyFiniteType_affineBaseModule ι s n e hF hU
  obtain ⟨N, hN⟩ := exists_isFiberBaseChangeBound n e _ hFU
  obtain ⟨y', rfl⟩ : y ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hyU
  have hpt : ∀ z : Spec Γ(S, U), hU.fromSpec z ∈ Set.range (flatteningStratumι ι s n e hF f) ↔
      fiberHilbertPolynomial (affineBaseModule ι s F hU) z = f := fun z =>
    (Set.ext_iff.mp (range_flatteningStratumι ι s n e hF f) (hU.fromSpec z)).trans
      (congrArg (· = f) (fiberHilbertPolynomialAt_fromSpec ι s F hU z)).to_iff
  have hcl : y' ∈ closure (hU.fromSpec ⁻¹' Set.range (flatteningStratumι ι s n e hF f)) := by
    rw [← hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      hU.fromSpec.isOpenEmbedding.continuous]
    exact hy
  by_cases hf : f ∈ Set.range (fiberHilbertPolynomial (affineBaseModule ι s F hU))
  · have hset : hU.fromSpec ⁻¹' Set.range (flatteningStratumι ι s n e hF f) =
        Set.range (hilbertPolynomialStratumι n e _ hFU N f) := Set.ext fun z =>
      (hpt z).trans (Set.ext_iff.mp (range_hilbertPolynomialStratumι n e _ hFU hN f hf) z).symm
    have hcl' : y' ∈ closure (Set.range (hilbertPolynomialStratumι n e _ hFU N f)) := by
      rw [← hset]
      exact hcl
    obtain ⟨g, ⟨hg, hfg⟩, hyg⟩ := Set.mem_iUnion₂.mp
      (closure_range_hilbertPolynomialStratumι_subset n e _ hFU hN f hf hcl')
    have hyg' : fiberHilbertPolynomial (affineBaseModule ι s F hU) y' = g :=
      (Set.ext_iff.mp (range_hilbertPolynomialStratumι n e _ hFU hN g hg) y').mp hyg
    have hPy : fiberHilbertPolynomialAt ι s F (hU.fromSpec y') = g :=
      (fiberHilbertPolynomialAt_fromSpec ι s F hU y').trans hyg'
    exact Set.mem_iUnion₂.mpr ⟨g, ⟨⟨_, hPy⟩, hfg⟩,
      (Set.ext_iff.mp (range_flatteningStratumι ι s n e hF g) _).mpr hPy⟩
  · have hempty : hU.fromSpec ⁻¹' Set.range (flatteningStratumι ι s n e hF f) = ∅ :=
      Set.eq_empty_of_forall_notMem fun z hz => hf ⟨z, (hpt z).mp hz⟩
    rw [hempty, closure_empty] at hcl
    exact absurd hcl (Set.notMem_empty _)

end AlgebraicGeometry.Scheme.Cohomology

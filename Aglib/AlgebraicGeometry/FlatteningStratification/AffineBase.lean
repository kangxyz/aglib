/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.StratumFlatness
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.PullbackSquare
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.AffineOpen
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Fiber

/-!
# A projective family over the affine opens of its base

Let `A` be a ring, `s : S ⟶ Spec A` a scheme over `Spec A`, `X_S = P^n_A ×_{Spec A} S`
(`pullback (toSpec A ι) s`) and `F` a module on `X_S`. Over an affine open `U` of `S`, with
`B = Γ(S, U)`, the family restricts to the polynomial projective space `P^n_B` through
`ProjectiveSpace.affineBaseMap ι s hU` (`ProjectiveSpace/BaseChange/AffineOpen`):

* `affineBaseModule ι s F hU`, the pullback of `F` to `P^n_{Γ(S, U)}`, coherent when `F` is and
  `S` is locally Noetherian (`affineLocallyFiniteType_affineBaseModule`);
* flatness over a test scheme `g' : T ⟶ Spec Γ(S, U)` of the pullback of `F` to `X_S ×_S T` is
  flatness of the pullback of `affineBaseModule ι s F hU` to
  `P^n_{Γ(S, U)} ×_{Spec Γ(S, U)} T` (`relativeFlat_pullback_affineBaseMap_iff`).

**Fibre Hilbert polynomials on `S`.** For `y ∈ S`, `fiberHilbertPolynomialAt ι s F y` is the
fibre Hilbert polynomial of `affineBaseModule ι s F hU` at the point of `Spec Γ(S, U)` over `y`,
for a chosen affine open `U ∋ y`. For quasi-coherent `F` it does not depend on the choice
(`fiberHilbertPolynomialAt_eq`): for affine opens `W ⊆ U`, the restriction of the family over `U`
to `W` is the base change of `P^n_{Γ(S, U)}` along `Γ(S, U) → Γ(S, W)`
(`ProjectiveSpace.affineBaseMap_restrict`), and fibre Hilbert polynomials are unchanged by base
change (`projectiveHilbertPolynomial_fiber_pullback_map`). For coherent `F` over a quasi-compact
locally Noetherian `S` only finitely many occur (`finite_range_fiberHilbertPolynomialAt`, from (A)
on finitely many affine opens; Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, proof of Thm 4.3, pp. 20–21).

**Base change of the base.** For `g : T ⟶ S`, let `F_T` be the pullback of `F` to
`P^n_A ×_{Spec A} T` along `ProjectiveSpace.pullbackBaseChange ι s g`. Then the fibre Hilbert
polynomial of `F_T` at `t ∈ T` is that of `F` at `g t`
(`fiberHilbertPolynomialAt_pullbackBaseChange`, chart by chart over affine opens `V ≤ g ⁻¹ U`,
along `g.appLE U V`), and `F_T` is flat over `T` exactly when the pullback of `F` to `X_S ×_S T`
is (`relativeFlat_pullbackBaseChange_iff`). With these, conditions on the fibres of `F_T` over the
points of `T` read as conditions on `F` at the image points in `S`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] (ι : Type u) {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of A))

/-- The pullback of `F` to `P^n_{Γ(S, U)}`, for an affine open `U` of `S`. -/
def affineBaseModule (F : (pullback (toSpec A ι) s).Modules) {U : S.Opens} (hU : IsAffineOpen U) :
    (ProjectiveSpace Γ(S, U) ι).Modules :=
  (Scheme.Modules.pullback (affineBaseMap ι s hU)).obj F

/-- **The fibre Hilbert polynomial of `F` at a point `y` of `S`**: that of
`affineBaseModule ι s F hU` at the point over `y`, for a chosen affine open `U ∋ y`. For
quasi-coherent `F` it does not depend on `U` (`fiberHilbertPolynomialAt_eq`). -/
def fiberHilbertPolynomialAt (F : (pullback (toSpec A ι) s).Modules) (y : S) : Polynomial ℚ :=
  fiberHilbertPolynomial (affineBaseModule ι s F
      (exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)).choose_spec.1)
    (IsAffineOpen.primeIdealOf
      (exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)).choose_spec.1
      ⟨y, (exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top y)).choose_spec.2.1⟩)

/-- The relative flatness of a base change of `F` over a test scheme of an affine open `U`,
read on `P^n_{Γ(S, U)}`. -/
theorem relativeFlat_pullback_affineBaseMap_iff (F : (pullback (toSpec A ι) s).Modules)
    [F.IsQuasicoherent] {U : S.Opens} (hU : IsAffineOpen U) {T : Scheme.{u}}
    (g' : T ⟶ Spec Γ(S, U)) :
    relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) (g' ≫ hU.fromSpec))
        ((Scheme.Modules.pullback
          (pullback.fst (pullback.snd (toSpec A ι) s) (g' ≫ hU.fromSpec))).obj F) ↔
      relativeFlat (pullback.snd (toSpec Γ(S, U) ι) g')
        ((Scheme.Modules.pullback (pullback.fst (toSpec Γ(S, U) ι) g')).obj
          (affineBaseModule ι s F hU)) :=
  relativeFlat_pullback_comp_iff_of_isPullback (isPullback_affineBaseMap ι s hU) F g'

/-- **Flatness on `P^n_A ×_{Spec A} T` against flatness on `X_S ×_S T`**: for `g : T ⟶ S` and
quasi-coherent `F`, the pullback `F_T` of `F` along `pullbackBaseChange ι s g` is flat over `T`
if and only if the pullback of `F` to `X_S ×_S T` is. Both are base changes of `F` along `g`. -/
theorem relativeFlat_pullbackBaseChange_iff (F : (pullback (toSpec A ι) s).Modules)
    [F.IsQuasicoherent] {T : Scheme.{u}} (g : T ⟶ S) :
    relativeFlat (pullback.snd (toSpec A ι) (g ≫ s))
        ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj F) ↔
      relativeFlat (pullback.snd (pullback.snd (toSpec A ι) s) g)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) s) g)).obj F) :=
  relativeFlat_iff_of_isPullback (isPullback_pullbackBaseChange ι s g)
    (IsPullback.of_hasPullback _ _) F

section QuasiCoherent

variable [Finite ι] (F : (pullback (toSpec A ι) s).Modules) [F.IsQuasicoherent]

/-- **Restriction of fibre Hilbert polynomials** to a smaller affine open: for affine opens
`W ≤ U` and `y ∈ W`, the fibre Hilbert polynomials of the restrictions of `F` over `W` and over
`U` at the points over `y` agree. -/
theorem fiberHilbertPolynomial_affineBaseModule_restrict {U W : S.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (hWU : W ≤ U) (y : S) (hy : y ∈ W) :
    fiberHilbertPolynomial (affineBaseModule ι s F hW) (hW.primeIdealOf ⟨y, hy⟩) =
      fiberHilbertPolynomial (affineBaseModule ι s F hU) (hU.primeIdealOf ⟨y, hWU hy⟩) := by
  have : (affineBaseModule ι s F hU).IsQuasicoherent := quasicoherent_pullback _ F
  have hpq : PrimeSpectrum.comap (S.presheaf.map (homOfLE hWU).op).hom
      (hW.primeIdealOf ⟨y, hy⟩) = hU.primeIdealOf ⟨y, hWU hy⟩ := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [IsAffineOpen.fromSpec_primeIdealOf]
    change (Spec.map (S.presheaf.map (homOfLE hWU).op) ≫ hU.fromSpec)
      (hW.primeIdealOf ⟨y, hy⟩) = y
    rw [hU.map_fromSpec hW (homOfLE hWU).op, IsAffineOpen.fromSpec_primeIdealOf]
  have E : affineBaseModule ι s F hW ≅ (Scheme.Modules.pullback
      (map (S.presheaf.map (homOfLE hWU).op).hom ι)).obj (affineBaseModule ι s F hU) :=
    (Scheme.Modules.pullbackCongr (affineBaseMap_restrict ι s hU hW hWU)).app F ≪≫
      ((Scheme.Modules.pullbackComp (map (S.presheaf.map (homOfLE hWU).op).hom ι)
        (affineBaseMap ι s hU)).app F).symm
  rw [← hpq]
  exact (projectiveHilbertPolynomial_congr _ ι ((Scheme.Modules.pullback
      (map (algebraMap _ (hW.primeIdealOf ⟨y, hy⟩).asIdeal.ResidueField) ι)).mapIso E)).trans
    (projectiveHilbertPolynomial_fiber_pullback_map ι (S.presheaf.map (homOfLE hWU).op).hom
      (affineBaseModule ι s F hU) (hW.primeIdealOf ⟨y, hy⟩))

/-- **The fibre Hilbert polynomial at `y ∈ S` is computed in any affine open around `y`.** -/
theorem fiberHilbertPolynomialAt_eq {U : S.Opens} (hU : IsAffineOpen U) (y : S) (hy : y ∈ U) :
    fiberHilbertPolynomialAt ι s F y =
      fiberHilbertPolynomial (affineBaseModule ι s F hU) (hU.primeIdealOf ⟨y, hy⟩) := by
  have key : ∀ (U V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hyU : y ∈ U)
      (hyV : y ∈ V),
      fiberHilbertPolynomial (affineBaseModule ι s F hU) (hU.primeIdealOf ⟨y, hyU⟩) =
        fiberHilbertPolynomial (affineBaseModule ι s F hV) (hV.primeIdealOf ⟨y, hyV⟩) := by
    intro U V hU hV hyU hyV
    obtain ⟨W, hW, hyW, hWsub⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ U ⊓ V from ⟨hyU, hyV⟩)
    have hWU : W ≤ U := fun x hx => (hWsub hx).1
    have hWV : W ≤ V := fun x hx => (hWsub hx).2
    rw [← fiberHilbertPolynomial_affineBaseModule_restrict ι s F hU hW hWU y hyW,
      fiberHilbertPolynomial_affineBaseModule_restrict ι s F hV hW hWV y hyW]
  exact key _ _ _ _ _ hy

/-- The fibre Hilbert polynomial at the image of a point of `Spec Γ(S, U)`. -/
theorem fiberHilbertPolynomialAt_fromSpec {U : S.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(S, U)) :
    fiberHilbertPolynomialAt ι s F (hU.fromSpec y) =
      fiberHilbertPolynomial (affineBaseModule ι s F hU) y := by
  have hy : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨y, rfl⟩
  rw [fiberHilbertPolynomialAt_eq ι s F hU _ hy]
  congr 1
  exact hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

/-- **Fibre Hilbert polynomials are unchanged by base change of the base**: for `g : T ⟶ S`,
quasi-coherent `F` and `t ∈ T`, the fibre Hilbert polynomial at `t` of the pullback `F_T` of `F`
to `P^n_A ×_{Spec A} T` (along `pullbackBaseChange ι s g`) is the fibre Hilbert polynomial of
`F` at `g t`. Over affine opens `V ∋ t` and `U ∋ g t` with `V ≤ g ⁻¹ U`, the restriction of
`F_T` over `V` is the base change of that of `F` over `U` along `g.appLE U V`
(`affineBaseMap_pullbackBaseChange`), and `projectiveHilbertPolynomial_fiber_pullback_map`
applies. -/
theorem fiberHilbertPolynomialAt_pullbackBaseChange {T : Scheme.{u}} (g : T ⟶ S) (t : T) :
    fiberHilbertPolynomialAt ι (g ≫ s)
        ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj F) t =
      fiberHilbertPolynomialAt ι s F (g t) := by
  obtain ⟨U, hU, htU, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (g t))
  obtain ⟨V, hV, htV, hVsub⟩ := exists_isAffineOpen_mem_and_subset
    (show t ∈ g ⁻¹ᵁ U from htU)
  have hVU : V ≤ g ⁻¹ᵁ U := hVsub
  rw [fiberHilbertPolynomialAt_eq ι (g ≫ s) _ hV t htV, fiberHilbertPolynomialAt_eq ι s F hU _ htU]
  have : (affineBaseModule ι s F hU).IsQuasicoherent := quasicoherent_pullback _ F
  have hpq : PrimeSpectrum.comap (g.appLE U V hVU).hom (hV.primeIdealOf ⟨t, htV⟩) =
      hU.primeIdealOf ⟨g t, htU⟩ :=
    IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU htV
  have E : affineBaseModule ι (g ≫ s) ((Scheme.Modules.pullback (pullbackBaseChange ι s g)).obj F)
      hV ≅ (Scheme.Modules.pullback (map (g.appLE U V hVU).hom ι)).obj
        (affineBaseModule ι s F hU) :=
    (Scheme.Modules.pullbackComp (affineBaseMap ι (g ≫ s) hV) (pullbackBaseChange ι s g)).app F ≪≫
      (Scheme.Modules.pullbackCongr (affineBaseMap_pullbackBaseChange ι s g hU hV hVU)).app F ≪≫
      ((Scheme.Modules.pullbackComp (map (g.appLE U V hVU).hom ι)
        (affineBaseMap ι s hU)).app F).symm
  rw [← hpq]
  exact (projectiveHilbertPolynomial_congr _ ι ((Scheme.Modules.pullback
      (map (algebraMap _ (hV.primeIdealOf ⟨t, htV⟩).asIdeal.ResidueField) ι)).mapIso E)).trans
    (projectiveHilbertPolynomial_fiber_pullback_map ι (g.appLE U V hVU).hom
      (affineBaseModule ι s F hU) (hV.primeIdealOf ⟨t, htV⟩))

end QuasiCoherent

section Coherent

variable [IsLocallyNoetherian S] (n : ℕ) (e : ι ≃ Fin (n + 1))
  {F : (pullback (toSpec A ι) s).Modules} (hF : affineLocallyFiniteType (pullback (toSpec A ι) s) F)

include e hF in
/-- The restriction of a coherent `F` to `P^n_{Γ(S, U)}` is coherent. -/
theorem affineLocallyFiniteType_affineBaseModule {U : S.Opens} (hU : IsAffineOpen U) :
    affineLocallyFiniteType (ProjectiveSpace Γ(S, U) ι) (affineBaseModule ι s F hU) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact affineLocallyFiniteType_pullback (affineBaseMap ι s hU) hF

include e hF in
/-- **Only finitely many fibre Hilbert polynomials occur over a quasi-compact base** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, (A), pp. 20–21): finitely many affine opens cover `S`, and
over each only finitely many occur (`finite_range_projectiveHilbertPolynomial_fiber`). -/
theorem finite_range_fiberHilbertPolynomialAt [CompactSpace S] :
    (Set.range (fiberHilbertPolynomialAt ι s F)).Finite := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : S.affineOpens => (U.1 : Set S))
    (fun U => U.1.isOpen) (fun y _ => Set.mem_iUnion.mpr (by
      obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
        (TopologicalSpace.Opens.mem_top y)
      exact ⟨⟨U, hU⟩, hyU⟩))
  have hfin : (⋃ U ∈ t, Set.range (fiberHilbertPolynomial
      (affineBaseModule ι s F (U.2 : IsAffineOpen U.1)))).Finite :=
    t.finite_toSet.biUnion fun U _ => by
      have : IsNoetherianRing Γ(S, U.1) := IsLocallyNoetherian.component_noetherian U
      exact finite_range_projectiveHilbertPolynomial_fiber n e _
        (affineLocallyFiniteType_affineBaseModule ι s n e hF U.2)
  refine hfin.subset ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨U, hUt, hyU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact Set.mem_iUnion₂.mpr ⟨U, hUt, _, (fiberHilbertPolynomialAt_eq ι s F U.2 y hyU).symm⟩

end Coherent

end AlgebraicGeometry.Scheme.Cohomology

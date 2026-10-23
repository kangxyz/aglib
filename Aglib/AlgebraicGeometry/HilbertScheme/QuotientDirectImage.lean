/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.DirectImage
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.ClosedSubscheme

/-!
# Direct images of the twisted structure module of a flat family

Let `B` be a Noetherian ring, `ι ≃ Fin (n + 1)` and `Z ⊆ P^n_B` a closed subscheme, flat over `B`,
whose fibers over the primes of `B` all have Hilbert polynomial `Φ`. With
`m = hilbertRegularityBound n Φ` and `𝒪_Z(r) = 𝒪(r) ⊗ 𝒪_Z` (`quotientTwist`), this file proves for
every `r ≥ m` (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5,
p. 25); such `r` satisfy `r ≥ -n`, since `m ≥ n + 2` (`add_two_le_hilbertRegularityBound`):

* `subsingleton_moduleCohomology_quotientTwist`: `H^q(P^n_B, 𝒪_Z(r)) = 0` for `q ≥ 1`;
* `projective_moduleCohomology_quotientTwist`: `H^0(P^n_B, 𝒪_Z(r))` is projective;
* `isIso_moduleCohomologyBaseChangeMap_quotientTwist`: its cohomology commutes with every base
  change, in every degree;
* `moduleFiberCohomologyDimension_quotientTwist`: its fiber at `p` has dimension `Φ(r)`;
* `exact_moduleCohomology_twistedShortComplex`: `0 → H^0(I_Z(r)) → H^0(𝒪(r)) → H^0(𝒪_Z(r)) → 0`
  is exact (`H^1(I_Z(r)) = 0`), as maps linear over `B`.

The fibers of `𝒪_Z(r)` are `𝒪_{Z_p}(r)` (`quotientModulePullbackIso`, which needs no flatness).
Their higher cohomology
vanishes by the sequence `0 → I_{Z_p}(r) → 𝒪(r) → 𝒪_{Z_p}(r) → 0`, the vanishing of `H^q(𝒪(r))`
for `r ≥ -n` and the regularity of `I_{Z_p}` (`isProjectiveRegular_idealModule`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u) {B : Type u} [CommRing B]

/-- The twisted structure module `𝒪_Z(r) = 𝒪(r) ⊗ 𝒪_Z` of a closed subscheme of `P^n_B`. -/
abbrev quotientTwist (Z : (ProjectiveSpace B ι).IdealSheafData) (r : ℤ) :
    (ProjectiveSpace B ι).Modules :=
  (moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι r)).obj Z.quotientModule

/-- The twisted sequence `I_Z(r) ⟶ 𝒪(r) ⊗ 𝒪 ⟶ 𝒪_Z(r)`. -/
abbrev twistedShortComplex (Z : (ProjectiveSpace B ι).IdealSheafData) (r : ℤ) :
    ShortComplex (ProjectiveSpace B ι).Modules :=
  Z.shortComplex.map (moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι r))

/-- `0 → I_Z(r) → 𝒪(r) ⊗ 𝒪 → 𝒪_Z(r) → 0` is short exact: twisting is exact. -/
theorem twistedShortComplex_shortExact (Z : (ProjectiveSpace B ι).IdealSheafData) (r : ℤ) :
    (twistedShortComplex ι Z r).ShortExact :=
  tensor_shortExact_finiteLocallyFree (twistingSheaf B ι r) Z.shortComplex
    Z.shortComplex_shortExact

/-- `H^q(P^n_B, 𝒪(r) ⊗ 𝒪) = 0` for `q ≥ 1` and `r ≥ -n`, over every ring. -/
theorem subsingleton_moduleCohomology_unitTwist (n : ℕ) (e : ι ≃ Fin (n + 1)) (r : ℤ)
    (hr : -(n : ℤ) ≤ r) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι r)).obj
        (SheafOfModules.unit (ProjectiveSpace B ι).ringCatSheaf))) q) :=
  moduleCohomology_subsingleton_of_iso (ρ_ (twistingSheaf B ι r)).symm q
    (twistingCohomology_subsingleton_of_neg_le_degree B ι n e r q hr hq)

/-- **Vanishing for the twisted structure module of a regular ideal**: if the ideal sheaf of a
closed subscheme `W ⊆ P^n_R` is `m`-regular, `R` Noetherian, then `H^q(𝒪_W(r)) = 0` for `q ≥ 1`,
`r ≥ m` and `r ≥ -n`. -/
theorem subsingleton_moduleCohomology_quotientTwist_of_isProjectiveRegular [IsNoetherianRing B]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (W : (ProjectiveSpace B ι).IdealSheafData) {m r : ℤ}
    (hreg : IsProjectiveRegular B ι (Scheme.Hom.idealModule W.subschemeι) m) (hr : m ≤ r)
    (hr' : -(n : ℤ) ≤ r) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (quotientTwist ι W r))
      q) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact moduleCohomology_subsingleton_X₃ (twistedShortComplex ι W r)
    (twistedShortComplex_shortExact ι W r) q
    (subsingleton_moduleCohomology_unitTwist ι n e r hr' q hq)
    (IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent B ι n e
      (Scheme.Hom.affineLocallyFiniteType_idealModule W.subschemeι) hreg hr (Nat.succ_pos q))

/-- **Fiber vanishing through an isomorphism on `P^n_{κ(p)}`**: if the pullback of a coherent
`M` on `P^n_B` to `P^n_{κ(p)}` is isomorphic to `N` with `H^q(N) = 0`, then `H^q` of `M` vanishes
on the native fiber over `p`. -/
theorem subsingleton_fiber_of_pullbackIso [IsNoetherianRing B] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace B ι).Modules) (hM : affineLocallyFiniteType (ProjectiveSpace B ι) M)
    (p : PrimeSpectrum B) (q : ℕ) {N : (ProjectiveSpace p.asIdeal.ResidueField ι).Modules}
    (eN : (Scheme.Modules.pullback (map (algebraMap B p.asIdeal.ResidueField) ι)).obj M ≅ N)
    (h : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace p.asIdeal.ResidueField ι) N) q)) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec B ι) (Spec.map (CommRingCat.ofHom
        (algebraMap B p.asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst (toSpec B ι) (Spec.map (CommRingCat.ofHom
        (algebraMap B p.asIdeal.ResidueField))))).obj M)) q) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hdim : moduleFiberCohomologyDimension (toSpec B ι) M q p = 0 := by
    rw [moduleFiberCohomologyDimension_toSpec ι _ q p, projectiveCohomologyDim_congr _ ι eN]
    exact projectiveCohomologyDim_eq_zero_of_subsingleton h
  let σ := Spec.map (CommRingCat.ofHom (algebraMap B p.asIdeal.ResidueField))
  let N' := (Scheme.Modules.pullback (pullback.fst (toSpec B ι) σ)).obj M
  have hN : affineLocallyFiniteType _ N' :=
    affineLocallyFiniteType_pullback (pullback.fst (toSpec B ι) σ) hM
  let := moduleCohomologyModuleOfHom _ ((pullback.snd (toSpec B ι) σ).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of p.asIdeal.ResidueField)).inv.hom) N' q
  have := moduleCohomology_finite_of_proper p.asIdeal.ResidueField (pullback.snd (toSpec B ι) σ)
    N' hN q
  have hdim' : Module.finrank p.asIdeal.ResidueField
      (Sheaf.H.{u + 1} (moduleAddSheaf (pullback (toSpec B ι) σ) N') q) = 0 := hdim
  exact Module.finrank_zero_iff.mp hdim'

variable [IsNoetherianRing B] (n : ℕ) (e : ι ≃ Fin (n + 1))
  (Z : (ProjectiveSpace B ι).IdealSheafData) {Φ : ℚ[X]}

include e in
theorem affineLocallyFiniteType_quotientTwist (r : ℤ) :
    affineLocallyFiniteType (ProjectiveSpace B ι) (quotientTwist ι Z r) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  twistingTensor_affineLocallyFiniteType B ι r _ Z.affineLocallyFiniteType_quotientModule

omit [IsNoetherianRing B] in
/-- `𝒪_Z(r)` is relatively flat over `Spec B` when `Z` is flat over `B`. -/
theorem relativeFlat_quotientTwist [Flat (Z.subschemeι ≫ toSpec B ι)] (r : ℤ) :
    relativeFlat (toSpec B ι) (quotientTwist ι Z r) := by
  exact twistingTensor_relativeFlat (toSpec B ι) _
    (Z.relativeFlat_quotientModule_of_flat (toSpec B ι)) r

/-- The fiber at `p` of the twisted structure module, in the coordinates of `P^n_{κ(p)}`. -/
def quotientTwistFiberIso (r : ℤ) (p : PrimeSpectrum B) :
    (Scheme.Modules.pullback (map (algebraMap B p.asIdeal.ResidueField) ι)).obj
        (quotientTwist ι Z r) ≅ quotientTwist ι (primeFiber ι Z p) r :=
  twistingTensorPullbackIso (algebraMap B p.asIdeal.ResidueField) ι r _ ≪≫
    (moduleTensorLeftFunctor (ProjectiveSpace p.asIdeal.ResidueField ι)
      (twistingSheaf p.asIdeal.ResidueField ι r)).mapIso
        (Z.quotientModulePullbackIso (map (algebraMap B p.asIdeal.ResidueField) ι))

include e in
/-- **Vanishing of the higher cohomology of `𝒪_Z(r)`** for `r ≥ hilbertRegularityBound n Φ`. -/
theorem subsingleton_moduleCohomology_quotientTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (quotientTwist ι Z r))
      q) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  have hr' : -(n : ℤ) ≤ r := by have := add_two_le_hilbertRegularityBound n Φ; omega
  subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper (toSpec B ι) _
    (affineLocallyFiniteType_quotientTwist ι n e Z r) (relativeFlat_quotientTwist ι Z r) q
    fun p => subsingleton_fiber_of_pullbackIso ι n e _
      (affineLocallyFiniteType_quotientTwist ι n e Z r) p q (quotientTwistFiberIso ι Z r p)
      (subsingleton_moduleCohomology_quotientTwist_of_isProjectiveRegular ι n e _
        (by have h := isProjectiveRegular_idealModule ι n e (primeFiber ι Z p)
            rwa [hfib p] at h) hr hr' q hq)

include e in
/-- **`H^0(P^n_B, 𝒪_Z(r))` is projective** for `r ≥ hilbertRegularityBound n Φ`. -/
theorem projective_moduleCohomology_quotientTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
      ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (quotientTwist ι Z r) 0
    Module.Projective B
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (quotientTwist ι Z r)) 0) :=
  moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding (i := 𝟙 _) e
    (Category.id_comp _) (affineLocallyFiniteType_quotientTwist ι n e Z r)
    (relativeFlat_quotientTwist ι Z r)
    (fun q hq => subsingleton_moduleCohomology_quotientTwist ι n e Z hfib r hr q hq)

include e in
/-- **Cohomology of `𝒪_Z(r)` commutes with base change** for `r ≥ hilbertRegularityBound n Φ`: for
every ring map `σ : B →+* C` the base-change map is an isomorphism in every degree. -/
theorem isIso_moduleCohomologyBaseChangeMap_quotientTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) (q : ℕ) {C : Type u} [CommRing C]
    (σ : B →+* C) :
    IsIso (moduleCohomologyBaseChangeMap (toSpec B ι) σ (quotientTwist ι Z r) q) :=
  moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding (i := 𝟙 _) e
    (Category.id_comp _) (affineLocallyFiniteType_quotientTwist ι n e Z r)
    (relativeFlat_quotientTwist ι Z r)
    (fun q hq => subsingleton_moduleCohomology_quotientTwist ι n e Z hfib r hr q hq) q σ

omit [IsNoetherianRing B] in
include e in
/-- **The fiber dimension of `H^0(𝒪_Z(r))`** for `r ≥ hilbertRegularityBound n Φ`: the fiber
cohomology of `𝒪_Z(r)` over a prime `p` has dimension `Φ(r)` in degree zero. -/
theorem moduleFiberCohomologyDimension_quotientTwist
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) (p : PrimeSpectrum B) :
    (moduleFiberCohomologyDimension (toSpec B ι) (quotientTwist ι Z r) 0 p : ℚ) =
      Φ.eval (r : ℚ) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hreg := isProjectiveRegular_idealModule ι n e (primeFiber ι Z p)
  rw [hfib p] at hreg
  have hW := (primeFiber ι Z p).affineLocallyFiniteType_quotientModule
  rw [moduleFiberCohomologyDimension_toSpec ι _ 0 p,
    projectiveCohomologyDim_congr _ ι (quotientTwistFiberIso ι Z r p)]
  have hχ := projectiveHilbertFunction_eq_eval _ ι n e _ hW r
  have hP : projectiveHilbertPolynomial p.asIdeal.ResidueField ι
      (primeFiber ι Z p).quotientModule = Φ := hfib p
  rw [hP, Int.cast_natCast] at hχ
  rw [← hχ]
  let M := quotientTwist ι (primeFiber ι Z p) r
  have hM : affineLocallyFiniteType _ M :=
    twistingTensor_affineLocallyFiniteType _ ι r _ hW
  have : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)
  change _ = ((projectiveEulerChar _ ι M : ℤ) : ℚ)
  rw [projectiveEulerChar_eq_sum_range _ ι n e M, Finset.sum_range_succ']
  have hpos (q : ℕ) : projectiveCohomologyDim _ ι M (q + 1) = 0 :=
    projectiveCohomologyDim_eq_zero_of_subsingleton
      (subsingleton_moduleCohomology_quotientTwist_of_isProjectiveRegular ι n e _ hreg hr
        (by omega) (q + 1) (Nat.succ_ne_zero q))
  simp only [hpos, CharP.cast_eq_zero, mul_zero, Finset.sum_const_zero, zero_add, pow_zero,
    one_mul, Int.cast_natCast]
  rfl

include e in
/-- **The exact sequence of direct images** (Nitsure, arXiv:math/0504590v1, §5, p. 25): for
`r ≥ hilbertRegularityBound n Φ`, the sequence
`0 → H^0(P^n_B, I_Z(r)) → H^0(P^n_B, 𝒪(r) ⊗ 𝒪) → H^0(P^n_B, 𝒪_Z(r)) → 0` of `B`-modules is exact. -/
theorem exact_moduleCohomology_twistedShortComplex [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI α := (toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    letI := moduleCohomologyModuleOfHom _ α (twistedShortComplex ι Z r).X₁ 0
    letI := moduleCohomologyModuleOfHom _ α (twistedShortComplex ι Z r).X₂ 0
    letI := moduleCohomologyModuleOfHom _ α (twistedShortComplex ι Z r).X₃ 0
    Function.Injective (moduleCohomologyMapOfHom _ α (twistedShortComplex ι Z r).f 0) ∧
      Function.Exact (moduleCohomologyMapOfHom _ α (twistedShortComplex ι Z r).f 0)
        (moduleCohomologyMapOfHom _ α (twistedShortComplex ι Z r).g 0) ∧
      Function.Surjective (moduleCohomologyMapOfHom _ α (twistedShortComplex ι Z r).g 0) := by
  let α := (toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let S := twistedShortComplex ι Z r
  have hS := twistedShortComplex_shortExact ι Z r
  let := moduleCohomologyModuleOfHom _ α S.X₁ 0
  let := moduleCohomologyModuleOfHom _ α S.X₂ 0
  let := moduleCohomologyModuleOfHom _ α S.X₃ 0
  let := moduleCohomologyModuleOfHom _ α S.X₁ (0 + 1)
  have : Mono S.f := hS.mono_f
  refine ⟨moduleH0MapOfHom_injective _ α S.f, moduleCohomologyMapOfHom_exact _ α S hS 0, ?_⟩
  have hvan : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) S.X₁) (0 + 1)) :=
    subsingleton_moduleCohomology_idealTwist ι n e Z hfib r hr 1 one_ne_zero
  have hex := moduleCohomologyConnectingOfHom_exact_left _ α S hS 0
  exact (LinearMap.surjective_iff_eq_zero_of_exact hex).mpr (Subsingleton.elim _ _)

end ProjectiveSpace

end AlgebraicGeometry

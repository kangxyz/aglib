/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Regularity
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Flat
public import Aglib.AlgebraicGeometry.IdealSheaf.Comap
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.ClosedSubscheme
public import Aglib.AlgebraicGeometry.Cohomology.Projective.VanishingProjective
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Fiber
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiberVanishing
public import Aglib.RingTheory.Flat.Exact
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.GlobalGeneration

/-!
# Direct images of the twisted ideal sheaf of a flat family

Let `B` be a Noetherian ring, `ι ≃ Fin (n + 1)`, and `Z ⊆ P^n_B` a closed subscheme, flat over `B`,
whose fibers `Z_p ⊆ P^n_{κ(p)}` over the primes `p` of `B` all have Hilbert polynomial `Φ`. This
is a point of the Hilbert functor over the affine test scheme `Spec B` (Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 25). With `m = hilbertRegularityBound n Φ`
and `I = I_Z` the actual ideal module of `Z`, this file proves for every `r ≥ m`:

* `idealModulePullbackIso`: for every ring map `φ : B →+* C`, the pullback of `I_Z` to `P^n_C` is
  the ideal module of the pulled-back subscheme (the quotient `Z` is flat over `B`;
  `flatQuotient_idealPullbackMap_isIso`). In particular the fibers of `I_Z` are the ideal modules
  `I_{Z_p}` of the fibers.
* `relativeFlat_idealTwist`: `I_Z(r)` is relatively flat over `Spec B`, from
  `Scheme.Modules.relativeFlat_idealModule_of_flat` (`Modules/Flat/Relative/ClosedSubscheme`): on
  an affine open `U`, `Γ(U, I_Z)` is the kernel of the surjection `Γ(U, 𝒪) ⟶ Γ(Z ∩ U, 𝒪_Z)`
  between flat `B`-modules.
* `subsingleton_moduleCohomology_idealTwist`: `H^q(P^n_B, I_Z(r)) = 0` for `q ≥ 1`, from the
  vanishing on the fibers (`IsHilbertFamily` regularity, Mumford's bound) and flatness
  (`subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper`).
* `projective_moduleCohomology_idealTwist`: `H^0(P^n_B, I_Z(r))` is a projective `B`-module.
* `isIso_moduleCohomologyBaseChangeMap_idealTwist`: for every ring map `σ : B →+* C`, the
  base-change map `C ⊗_B H^q(P^n_B, I_Z(r)) ⟶ H^q(P^n_B ×_{Spec B} Spec C, I_Z(r)_C)` is an
  isomorphism in every degree.
* `moduleFiberCohomologyDimension_idealTwist`: the fiber of `H^0(I_Z(r))` at `p` has dimension
  `C(r + n, n) - Φ(r)`; with the base-change isomorphism this is the rank of the projective module
  `H^0(P^n_B, I_Z(r))` at `p` (stated as `rankAtStalk_moduleCohomology_idealTwist` in
  `HilbertScheme/GrassmannianPoint`).
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

section BaseChange

variable {C : Type u} [CommRing C] (Z : (ProjectiveSpace B ι).IdealSheafData)
  [Flat (Z.subschemeι ≫ toSpec B ι)] (φ : B →+* C)

/-- **Base change of the ideal module of a flat family**: for a closed subscheme `Z ⊆ P^n_B` flat
over `B` and a ring map `φ : B →+* C`, the canonical map from the pullback of `I_Z` to
`P^n_C` onto the ideal module of `Z.comap (map φ ι)` is an isomorphism
(`flatQuotient_idealPullbackMap_isIso`). -/
theorem isIso_idealPullbackMap_map :
    IsIso (Scheme.Hom.idealPullbackMap Z.subschemeι (Z.comap (map φ ι)).subschemeι (map φ ι)
      (Scheme.IdealSheafData.subschemeMap (Z.comap (map φ ι)) Z (map φ ι)
        (Z.le_map_comap (map φ ι)))
      (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _)) :=
  Scheme.Hom.flatQuotient_idealPullbackMap_isIso (toSpec B ι) (Spec.map (CommRingCat.ofHom φ))
    (toSpec C ι) (map φ ι) Z.subschemeι _ _ _ (isPullback_map φ ι)
    (Z.isPullback_subschemeMap_comap _)

/-- The isomorphism `π_φ^* I_Z ≅ I_{Z_C}` of `isIso_idealPullbackMap_map`. -/
def idealModulePullbackIso :
    (Scheme.Modules.pullback (map φ ι)).obj (Scheme.Hom.idealModule Z.subschemeι) ≅
      Scheme.Hom.idealModule (Z.comap (map φ ι)).subschemeι :=
  haveI := isIso_idealPullbackMap_map ι Z φ
  asIso (Scheme.Hom.idealPullbackMap Z.subschemeι (Z.comap (map φ ι)).subschemeι (map φ ι)
    (Scheme.IdealSheafData.subschemeMap (Z.comap (map φ ι)) Z (map φ ι)
      (Z.le_map_comap (map φ ι)))
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _))

end BaseChange

/-- The twisted ideal module `I_Z(r) = 𝒪(r) ⊗ I_Z` of a closed subscheme of `P^n_B`. -/
abbrev idealTwist (Z : (ProjectiveSpace B ι).IdealSheafData) (r : ℤ) :
    (ProjectiveSpace B ι).Modules :=
  (moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι r)).obj
    (Scheme.Hom.idealModule Z.subschemeι)

variable [IsNoetherianRing B] (n : ℕ) (e : ι ≃ Fin (n + 1))
  (Z : (ProjectiveSpace B ι).IdealSheafData)

include e in
theorem affineLocallyFiniteType_idealTwist (r : ℤ) :
    affineLocallyFiniteType (ProjectiveSpace B ι) (idealTwist ι Z r) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  twistingTensor_affineLocallyFiniteType B ι r _
    (Scheme.Hom.affineLocallyFiniteType_idealModule Z.subschemeι)

include e in
/-- `I_Z(r)` is relatively flat over `Spec B` when `Z` is flat over `B`. -/
theorem relativeFlat_idealTwist [Flat (Z.subschemeι ≫ toSpec B ι)] (r : ℤ) :
    relativeFlat (toSpec B ι) (idealTwist ι Z r) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hI := Scheme.Hom.affineLocallyFiniteType_idealModule Z.subschemeι
  have : (Scheme.Hom.idealModule Z.subschemeι).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hI R j).1)
  exact twistingTensor_relativeFlat (toSpec B ι) _
    (relativeFlat_idealModule_of_flat (toSpec B ι) Z) r

variable {Φ : ℚ[X]}

/-- The fiber of `Z` over a prime `p` of `B`, a closed subscheme of `P^n_{κ(p)}`. -/
abbrev primeFiber (p : PrimeSpectrum B) :
    (ProjectiveSpace p.asIdeal.ResidueField ι).IdealSheafData :=
  Z.comap (map (algebraMap B p.asIdeal.ResidueField) ι)

/-- The fiber at `p` of the twisted ideal module, in the coordinates of `P^n_{κ(p)}`: it is the
twisted ideal module of the fiber `Z_p`. -/
def idealTwistFiberIso [Flat (Z.subschemeι ≫ toSpec B ι)] (r : ℤ) (p : PrimeSpectrum B) :
    (Scheme.Modules.pullback (map (algebraMap B p.asIdeal.ResidueField) ι)).obj
        (idealTwist ι Z r) ≅
      (moduleTensorLeftFunctor (ProjectiveSpace p.asIdeal.ResidueField ι)
        (twistingSheaf p.asIdeal.ResidueField ι r)).obj
          (Scheme.Hom.idealModule (primeFiber ι Z p).subschemeι) :=
  twistingTensorPullbackIso (algebraMap B p.asIdeal.ResidueField) ι r _ ≪≫
    (moduleTensorLeftFunctor (ProjectiveSpace p.asIdeal.ResidueField ι)
      (twistingSheaf p.asIdeal.ResidueField ι r)).mapIso
        (idealModulePullbackIso ι Z (algebraMap B p.asIdeal.ResidueField))

include e in
/-- **Vanishing on the fibers, degree by degree**: if `H^q(P^n_{κ(p)}, I_{Z_p}(r)) = 0` for the
fiber `Z_p` at a prime `p`, then `H^q` of `I_Z(r)` vanishes on the fiber of `P^n_B ⟶ Spec B`
over `p`, computed on the native fiber product. -/
theorem subsingleton_fiber_idealTwist_of [Flat (Z.subschemeι ≫ toSpec B ι)] (r : ℤ)
    (p : PrimeSpectrum B) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace p.asIdeal.ResidueField ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace p.asIdeal.ResidueField ι)
        (twistingSheaf p.asIdeal.ResidueField ι r)).obj
          (Scheme.Hom.idealModule (primeFiber ι Z p).subschemeι))) q)) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec B ι) (Spec.map (CommRingCat.ofHom
        (algebraMap B p.asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst (toSpec B ι) (Spec.map (CommRingCat.ofHom
        (algebraMap B p.asIdeal.ResidueField))))).obj (idealTwist ι Z r))) q) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hdim : moduleFiberCohomologyDimension (toSpec B ι) (idealTwist ι Z r) q p = 0 := by
    rw [moduleFiberCohomologyDimension_toSpec ι _ q p,
      projectiveCohomologyDim_congr _ ι (idealTwistFiberIso ι Z r p)]
    exact projectiveCohomologyDim_eq_zero_of_subsingleton h
  let σ := Spec.map (CommRingCat.ofHom (algebraMap B p.asIdeal.ResidueField))
  let N := (Scheme.Modules.pullback (pullback.fst (toSpec B ι) σ)).obj (idealTwist ι Z r)
  have hN : affineLocallyFiniteType _ N := affineLocallyFiniteType_pullback
    (pullback.fst (toSpec B ι) σ) (affineLocallyFiniteType_idealTwist ι n e Z r)
  let := moduleCohomologyModuleOfHom _ ((pullback.snd (toSpec B ι) σ).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of p.asIdeal.ResidueField)).inv.hom) N q
  have := moduleCohomology_finite_of_proper p.asIdeal.ResidueField (pullback.snd (toSpec B ι) σ)
    N hN q
  have hdim' : Module.finrank p.asIdeal.ResidueField
      (Sheaf.H.{u + 1} (moduleAddSheaf (pullback (toSpec B ι) σ) N) q) = 0 := hdim
  exact Module.finrank_zero_iff.mp hdim'

include e in
/-- **Vanishing on the fibers**: if every fiber `Z_p` has Hilbert polynomial `Φ`, then for
`r ≥ hilbertRegularityBound n Φ` and `q ≥ 1` the cohomology `H^q` of `I_Z(r)` on the fiber of
`P^n_B ⟶ Spec B` over `p` vanishes, on the native fiber product. The ideal sheaf of `Z_p` is
regular by Mumford's bound (`isProjectiveRegular_idealModule`). -/
theorem subsingleton_fiber_idealTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) (p : PrimeSpectrum B) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec B ι) (Spec.map (CommRingCat.ofHom
        (algebraMap B p.asIdeal.ResidueField))))
      ((Scheme.Modules.pullback (pullback.fst (toSpec B ι) (Spec.map (CommRingCat.ofHom
        (algebraMap B p.asIdeal.ResidueField))))).obj (idealTwist ι Z r))) q) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hreg := isProjectiveRegular_idealModule ι n e (primeFiber ι Z p)
  rw [hfib p] at hreg
  have hIp := Scheme.Hom.affineLocallyFiniteType_idealModule (primeFiber ι Z p).subschemeι
  exact subsingleton_fiber_idealTwist_of ι n e Z r p q
    (IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent _ ι n e hIp hreg hr
      (Nat.pos_of_ne_zero hq))

include e in
/-- **Vanishing of the higher cohomology of `I_Z(r)`** (Nitsure, arXiv:math/0504590v1, §5,
p. 25): for `Z ⊆ P^n_B` flat over `B` with all fiber Hilbert polynomials `Φ` and
`r ≥ hilbertRegularityBound n Φ`, `H^q(P^n_B, I_Z(r)) = 0` for every `q ≥ 1`. -/
theorem subsingleton_moduleCohomology_idealTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (idealTwist ι Z r)) q) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper (toSpec B ι) _
    (affineLocallyFiniteType_idealTwist ι n e Z r) (relativeFlat_idealTwist ι n e Z r) q
    fun p => subsingleton_fiber_idealTwist ι n e Z hfib r hr p q hq

include e in
/-- **`H^0(P^n_B, I_Z(r))` is projective** for `r ≥ hilbertRegularityBound n Φ` (Nitsure,
arXiv:math/0504590v1, §5, p. 25; cohomology and base change in the vanishing case). -/
theorem projective_moduleCohomology_idealTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
      ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (idealTwist ι Z r) 0
    Module.Projective B
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) (idealTwist ι Z r)) 0) :=
  moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding (i := 𝟙 _) e
    (Category.id_comp _) (affineLocallyFiniteType_idealTwist ι n e Z r)
    (relativeFlat_idealTwist ι n e Z r)
    (fun q hq => subsingleton_moduleCohomology_idealTwist ι n e Z hfib r hr q hq)

include e in
/-- **Cohomology of `I_Z(r)` commutes with base change** for `r ≥ hilbertRegularityBound n Φ`:
for every ring map `σ : B →+* C` the base-change map
`C ⊗_B H^q(P^n_B, I_Z(r)) ⟶ H^q(P^n_B ×_{Spec B} Spec C, I_Z(r)_C)` is an isomorphism in every
degree `q`. -/
theorem isIso_moduleCohomologyBaseChangeMap_idealTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) (q : ℕ) {C : Type u} [CommRing C]
    (σ : B →+* C) :
    IsIso (moduleCohomologyBaseChangeMap (toSpec B ι) σ (idealTwist ι Z r) q) :=
  moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding (i := 𝟙 _) e
    (Category.id_comp _) (affineLocallyFiniteType_idealTwist ι n e Z r)
    (relativeFlat_idealTwist ι n e Z r)
    (fun q hq => subsingleton_moduleCohomology_idealTwist ι n e Z hfib r hr q hq) q σ

omit [IsNoetherianRing B] in
include e in
/-- **The fiber dimension of `H^0(I_Z(r))`** for `r ≥ hilbertRegularityBound n Φ`: the fiber
cohomology of `I_Z(r)` over a prime `p` has dimension `C(r + n, n) - Φ(r)` in degree zero. By
`isIso_moduleCohomologyBaseChangeMap_idealTwist` at `B →+* κ(p)`, this is the dimension of
`κ(p) ⊗_B H^0(P^n_B, I_Z(r))`, the rank at `p` of the projective module `H^0(P^n_B, I_Z(r))`. -/
theorem moduleFiberCohomologyDimension_idealTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) (p : PrimeSpectrum B) :
    (moduleFiberCohomologyDimension (toSpec B ι) (idealTwist ι Z r) 0 p : ℚ) =
      ((r + n).choose n : ℚ) - Φ.eval (r : ℚ) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hreg := isProjectiveRegular_idealModule ι n e (primeFiber ι Z p)
  rw [hfib p] at hreg
  have hIp := Scheme.Hom.affineLocallyFiniteType_idealModule (primeFiber ι Z p).subschemeι
  have hχ := projectiveHilbertFunction_idealModule ι n e (primeFiber ι Z p) r
  rw [hfib p] at hχ
  rw [moduleFiberCohomologyDimension_toSpec ι _ 0 p,
    projectiveCohomologyDim_congr _ ι (idealTwistFiberIso ι Z r p), ← hχ]
  let M := (moduleTensorLeftFunctor (ProjectiveSpace p.asIdeal.ResidueField ι)
    (twistingSheaf p.asIdeal.ResidueField ι (r : ℤ))).obj
      (Scheme.Hom.idealModule (primeFiber ι Z p).subschemeι)
  have hM : affineLocallyFiniteType _ M :=
    twistingTensor_affineLocallyFiniteType _ ι r _ hIp
  have : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)
  change _ = ((projectiveEulerChar _ ι M : ℤ) : ℚ)
  rw [projectiveEulerChar_eq_sum_range _ ι n e M, Finset.sum_range_succ']
  have hpos (q : ℕ) : projectiveCohomologyDim _ ι M (q + 1) = 0 :=
    projectiveCohomologyDim_eq_zero_of_subsingleton
      (IsProjectiveRegular.cohomology_subsingleton_of_le_of_coherent _ ι n e hIp hreg hr
        (Nat.succ_pos q))
  simp only [hpos, CharP.cast_eq_zero, mul_zero, Finset.sum_const_zero, zero_add, pow_zero,
    one_mul, Int.cast_natCast]
  rfl

include e in
/-- **The ideal sheaf of a flat family is regular over the base**: for `Z ⊆ P^n_B` flat over the
Noetherian ring `B` with all fiber Hilbert polynomials `Φ`, `I_Z` is
`hilbertRegularityBound n Φ`-regular on `P^n_B`. For each `q ≥ 1`, the regularity of every fiber
`I_{Z_p}` gives `H^q` of `I_Z(m - q)` on every fiber, and flatness gives the vanishing of
`H^q(P^n_B, I_Z(m - q))` (`subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper`). -/
theorem isProjectiveRegular_idealModule_of_flat [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ) :
    IsProjectiveRegular B ι (Scheme.Hom.idealModule Z.subschemeι)
      (hilbertRegularityBound n Φ) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  intro q hq
  refine subsingleton_moduleCohomology_of_subsingleton_fiber_of_proper (toSpec B ι) _
    (affineLocallyFiniteType_idealTwist ι n e Z _) (relativeFlat_idealTwist ι n e Z _) q
    fun p => subsingleton_fiber_idealTwist_of ι n e Z _ p q ?_
  have hreg := isProjectiveRegular_idealModule ι n e (primeFiber ι Z p)
  rw [hfib p] at hreg
  exact hreg q hq

include e in
/-- **Global generation of `I_Z(r)`** (Nitsure, arXiv:math/0504590v1, Lemma 2.1 (c), over `B`):
for `Z ⊆ P^n_B` flat over `B` with all fiber Hilbert polynomials `Φ` and
`r ≥ hilbertRegularityBound n Φ`, the twist `I_Z(r)` is generated by its global sections. -/
theorem epi_globalSectionsEval_idealTwist [Flat (Z.subschemeι ≫ toSpec B ι)]
    (hfib : ∀ p : PrimeSpectrum B,
      subschemeHilbertPolynomial ι p.asIdeal.ResidueField (primeFiber ι Z p) = Φ)
    (r : ℤ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Epi (Scheme.Modules.globalSectionsEval (idealTwist ι Z r)) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  IsProjectiveRegular.epi_globalSectionsEval B ι n e
    (Scheme.Hom.affineLocallyFiniteType_idealModule Z.subschemeι)
    (isProjectiveRegular_idealModule_of_flat ι n e Z hfib) hr

end ProjectiveSpace

end AlgebraicGeometry

/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Exactness
public import Aglib.AlgebraicGeometry.Cohomology.Projective.FlatTwist
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Twisting
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Flat
public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Coherent
public import Mathlib.Algebra.FiveLemma

/-!
# Base change of global sections of large twists, without flatness

Let `A` be a Noetherian ring, `F` a coherent module on `P^n_A`, and `σ : A →+* B` a ring map to a
Noetherian ring `B`. There is a bound `N` such that for every `r ≥ N` the positive cohomology of
`F(r) = 𝒪(r) ⊗ F` vanishes, on `P^n_A` and on the fibre product `(P^n_A)_B`, and the original
cohomology base-change map
`B ⊗_A H^0(P^n_A, F(r)) ⟶ H^0((P^n_A)_B, F(r)_B)` is an isomorphism. Here `(P^n_A)_B` is the
fibre product `P^n_A ×_{Spec A} Spec B` and `F(r)_B` the pullback of `F(r)` along its first
projection, as in `FlatTwist.lean`. No flatness of `F` is assumed; the bound depends on `σ`.

This is Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Lemma 3.1,
p. 13, for affine `S = Spec A` and `T = Spec B`; its proof (pp. 14–15) is the one formalized:
a presentation `⊕ 𝒪(a) → ⊕ 𝒪(b) → F → 0`, base change for sums of twists, right exactness of
`H^0` of large twists over `A` and over `B` (Serre vanishing for the kernels), and the five lemma
(Mathlib's `AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact`). Right exactness is
guaranteed when `H^1` of the twists of the second syzygy vanishes; Nitsure's displayed four-term
sequences on p. 14 are exact at `π_* F(r)` for every `r`, but at `π_* ⊕ 𝒪(b + r)` in general only
for large `r`. Three misprints on p. 14: the pulled-back presentation prints `𝒪_{P^n_S}` for
`𝒪_{P^n_T}`; the `r ≥ r₀` sequence over `S` and the first row of the last diagram omit `π_{S*}` in
front of `⊕^q 𝒪(b + r)`.

The bound cannot be chosen independently of `B`, and `B` cannot be an arbitrary ring. For
`A = k[s, t]`, `n = 1` and `F = 𝒪_Z` with `Z = V(s X₁ - t X₀)`, one has `H^0(F(e)) = m^e` for
`e ≥ 0`, with `m = (s, t)`; for `a ≥ 2` and `B = A/(s^a, t^a)` the class of `s^(a-1) t^(a-1)` is a
nonzero element of the kernel of the base-change map in degree `a - 2`, and
`B = ∏_a A/(s^a, t^a)` defeats every bound.
These counterexamples are not formalized here.

Main results:
* `exists_twist_H0_exact_of_exact`: right exactness of `H^0` of large twists;
* `baseChangeTwistCohomologyHom`: the transport from the fibre product to `𝒪_B(d) ⊗ π^* M`
  on `P^n_B`, bijective and natural;
* `baseChangeMap_twist_isIso_of_exact`: the five-lemma step;
* `exists_twist_baseChange_isIso_of_isNoetherianRing`: the statement above;
* `exists_twist_baseChange_bijective_projectiveSpace`: the same with `𝒪_B(d) ⊗ π^* F` on `P^n_B`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-! ### Right exactness of global sections of large twists -/

section TwistExact

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type u}

/-- **Right exactness of global sections of large twists** (Nitsure, arXiv:math/0504590v1,
proof of Lemma 3.1, p. 14, the exact sequences of `π_*` for `r ≥ r₀`, over an affine Noetherian
base): for an exact sequence `E₁ → E₀ → F → 0` of coherent modules on `P^n_R`, there is a bound `N`
such that for every `d ≥ N` the sequence `H^0(E₁(d)) → H^0(E₀(d)) → H^0(F(d)) → 0` is exact.
The bound kills `H^1` of the twists of the kernel `G` of `E₀ → F` and of the kernel of `E₁ → G`.
Nitsure's displayed four-term sequences are exact at `π_* F(r)` for every `r`, and at
`π_* ⊕ 𝒪(b + r)` in general only for large `r`; the vanishing for the second kernel guarantees
it. -/
theorem exists_twist_H0_exact_of_exact (n : ℕ) (e : ι ≃ Fin (n + 1))
    {E₁ E₀ F : (ProjectiveSpace R ι).Modules} (u : E₁ ⟶ E₀) (v : E₀ ⟶ F) (huv : u ≫ v = 0)
    (hex : (ShortComplex.mk u v huv).Exact) [Epi v]
    (h₁ : affineLocallyFiniteType (ProjectiveSpace R ι) E₁)
    (h₀ : affineLocallyFiniteType (ProjectiveSpace R ι) E₀)
    (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F) :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d →
      Function.Exact
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map u)) 0)
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map v)) 0) ∧
      Function.Surjective
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map v)) 0) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  have hG : affineLocallyFiniteType (ProjectiveSpace R ι) (kernel v) :=
    (affineLocallyFiniteType (ProjectiveSpace R ι)).prop_kernel v h₀ hF
  let ρ : E₁ ⟶ kernel v := kernel.lift v u huv
  have hρ : Epi ρ := hex.epi_kernelLift
  have hK : affineLocallyFiniteType (ProjectiveSpace R ι) (kernel ρ) :=
    (affineLocallyFiniteType (ProjectiveSpace R ι)).prop_kernel ρ h₁ hG
  obtain ⟨NG, hNG⟩ := projectiveSerreVanishing R ι n e (kernel v) hG
  obtain ⟨NK, hNK⟩ := projectiveSerreVanishing R ι n e (kernel ρ) hK
  refine ⟨max NG NK, fun d hd => ?_⟩
  let T := moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)
  let S₂ := (ShortComplex.kernelSequence v).map T
  let S₁ := (ShortComplex.kernelSequence ρ).map T
  have hS₂ : S₂.ShortExact := tensor_shortExact_finiteLocallyFree (twistingSheaf R ι d)
    (ShortComplex.kernelSequence v)
    { exact := ShortComplex.kernelSequence_exact v, epi_g := inferInstanceAs (Epi v) }
  have hS₁ : S₁.ShortExact := tensor_shortExact_finiteLocallyFree (twistingSheaf R ι d)
    (ShortComplex.kernelSequence ρ)
    { exact := ShortComplex.kernelSequence_exact ρ, epi_g := hρ }
  have hG1 : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) S₂.X₁) (0 + 1)) :=
    hNG d (by have := le_max_left NG NK; omega) 1 one_ne_zero
  have hK1 : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) S₁.X₁) (0 + 1)) :=
    hNK d (by have := le_max_right NG NK; omega) 1 one_ne_zero
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S₂.X₂ 0
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S₂.X₃ 0
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S₂.X₁ 0
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S₂.X₁ (0 + 1)
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S₁.X₂ 0
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S₁.X₃ 0
  let := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α S₁.X₁ (0 + 1)
  have hv : Function.Surjective (moduleCohomologyMapOfHom (ProjectiveSpace R ι) α S₂.g 0) :=
    (LinearMap.surjective_iff_eq_zero_of_exact
      (moduleCohomologyConnectingOfHom_exact_left (ProjectiveSpace R ι) α S₂ hS₂ 0)).mpr
        (Subsingleton.elim _ _)
  have hρs : Function.Surjective (moduleCohomologyMapOfHom (ProjectiveSpace R ι) α S₁.g 0) :=
    (LinearMap.surjective_iff_eq_zero_of_exact
      (moduleCohomologyConnectingOfHom_exact_left (ProjectiveSpace R ι) α S₁ hS₁ 0)).mpr
        (Subsingleton.elim _ _)
  have hmid : Function.Exact
      (Sheaf.H.map ((SheafOfModules.toSheaf _).map (T.map (kernel.ι v))) 0)
      (Sheaf.H.map ((SheafOfModules.toSheaf _).map (T.map v)) 0) :=
    moduleCohomologyMapOfHom_exact (ProjectiveSpace R ι) α S₂ hS₂ 0
  have hv' : Function.Surjective
      (Sheaf.H.map ((SheafOfModules.toSheaf _).map (T.map v)) 0) := hv
  have hρs' : Function.Surjective
      (Sheaf.H.map ((SheafOfModules.toSheaf _).map (T.map ρ)) 0) := hρs
  have hcomp : T.map u = T.map ρ ≫ T.map (kernel.ι v) := by
    rw [← T.map_comp, kernel.lift_ι]
  have hmap : (SheafOfModules.toSheaf _).map (T.map u) =
      (SheafOfModules.toSheaf _).map (T.map ρ) ≫
        (SheafOfModules.toSheaf _).map (T.map (kernel.ι v)) := by
    rw [hcomp]
    exact Functor.map_comp _ _ _
  have happ (w : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (T.obj E₁)) 0) :
      Sheaf.H.map ((SheafOfModules.toSheaf _).map (T.map u)) 0 w =
        Sheaf.H.map ((SheafOfModules.toSheaf _).map (T.map (kernel.ι v))) 0
          (Sheaf.H.map ((SheafOfModules.toSheaf _).map (T.map ρ)) 0 w) := by
    rw [hmap]
    exact Sheaf.H.map_comp_apply _ _ _
  refine ⟨fun y => ⟨fun hy => ?_, ?_⟩, hv'⟩
  · obtain ⟨z, rfl⟩ := (hmid y).mp hy
    obtain ⟨w, rfl⟩ := hρs' z
    exact ⟨w, happ w⟩
  · rintro ⟨w, rfl⟩
    rw [happ w]
    exact (hmid _).mpr ⟨_, rfl⟩

end TwistExact

/-! ### Transport from the fibre product to `P^n_B` -/

section Transport

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The comparison `j^* p^* (𝒪_A(d) ⊗ M) ≅ 𝒪_B(d) ⊗ π^* M` on `P^n_B`, where
`p : P^n_A ×_{Spec A} Spec B ⟶ P^n_A` is the first projection, `j = baseChangeIso σ ι` identifies
`P^n_B` with the fibre product, and `π = map σ ι`. -/
def baseChangeTwistIso (σ : A →+* B) (ι : Type u) (d : ℤ) (M : (ProjectiveSpace A ι).Modules) :
    (Scheme.Modules.pullback (baseChangeIso σ ι).hom).obj
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom σ)))).obj
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj M)) ≅
      (moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).obj
        ((Scheme.Modules.pullback (map σ ι)).obj M) :=
  (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeIso_hom_fst σ ι)).app _ ≪≫
      twistingTensorPullbackIso σ ι d M

-- `X.Modules` is `SheafOfModules X.ringCatSheaf` with a `TopCat.Sheaf` of rings; rewriting in it
-- needs the Grothendieck-topology presentation of that sheaf, which is not reducible.
set_option backward.isDefEq.respectTransparency false in
/-- The comparison `baseChangeTwistIso` is natural in the module. -/
theorem baseChangeTwistIso_hom_naturality (σ : A →+* B) (ι : Type u) (d : ℤ)
    {M M' : (ProjectiveSpace A ι).Modules} (u : M ⟶ M') :
    (Scheme.Modules.pullback (baseChangeIso σ ι).hom).map
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom σ)))).map
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).map u)) ≫
      (baseChangeTwistIso σ ι d M').hom =
    (baseChangeTwistIso σ ι d M).hom ≫
      (moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).map
        ((Scheme.Modules.pullback (map σ ι)).map u) := by
  let T := moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)
  have h₁ := (Scheme.Modules.pullbackComp (baseChangeIso σ ι).hom
    (pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))).hom.naturality (T.map u)
  have h₂ := (Scheme.Modules.pullbackCongr (baseChangeIso_hom_fst σ ι)).hom.naturality (T.map u)
  simp only [Functor.comp_map] at h₁
  simp only [baseChangeTwistIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ProjectiveSpace.twistingTensorPullbackIso_hom_naturality]

/-- The transport `H^q(X_B, (𝒪_A(d) ⊗ M)_B) ⟶ H^q(P^n_B, 𝒪_B(d) ⊗ π^* M)`: pullback along the
isomorphism `baseChangeIso σ ι` followed by `baseChangeTwistIso`. -/
def baseChangeTwistCohomologyHom (σ : A →+* B) (ι : Type u) (d : ℤ)
    (M : (ProjectiveSpace A ι).Modules) (q : ℕ) :
    Sheaf.H.{u + 1} (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom σ)))).obj
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj M))) q →+
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).obj
          ((Scheme.Modules.pullback (map σ ι)).obj M))) q :=
  (Sheaf.H.map ((SheafOfModules.toSheaf _).map (baseChangeTwistIso σ ι d M).hom) q).comp
    (moduleCohomologyPullback (baseChangeIso σ ι).hom _ q)

theorem baseChangeTwistCohomologyHom_bijective (σ : A →+* B) (ι : Type u) (d : ℤ)
    (M : (ProjectiveSpace A ι).Modules) (q : ℕ) :
    Function.Bijective (baseChangeTwistCohomologyHom σ ι d M q) :=
  (bijective_sheafH_map_of_iso (baseChangeTwistIso σ ι d M) q).comp
    (moduleCohomologyPullback_bijective (baseChangeIso σ ι).hom _ q)

-- `X.Modules` is `SheafOfModules X.ringCatSheaf` with a `TopCat.Sheaf` of rings; rewriting in it
-- needs the Grothendieck-topology presentation of that sheaf, which is not reducible.
set_option backward.isDefEq.respectTransparency false in
/-- The transport is natural in the module. -/
theorem baseChangeTwistCohomologyHom_naturality (σ : A →+* B) (ι : Type u) (d : ℤ)
    {M M' : (ProjectiveSpace A ι).Modules} (u : M ⟶ M') (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom σ)))).obj
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj M))) q) :
    baseChangeTwistCohomologyHom σ ι d M' q
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom σ)))).map
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).map u))) q x) =
      Sheaf.H.map ((SheafOfModules.toSheaf _).map
        ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).map
          ((Scheme.Modules.pullback (map σ ι)).map u))) q
        (baseChangeTwistCohomologyHom σ ι d M q x) := by
  let j := (baseChangeIso σ ι).hom
  let p := pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))
  let T := moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)
  let TB := moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)
  let a := (SheafOfModules.toSheaf _).map ((Scheme.Modules.pullback j).map
    ((Scheme.Modules.pullback p).map (T.map u)))
  let b := (SheafOfModules.toSheaf _).map (baseChangeTwistIso σ ι d M').hom
  let c := (SheafOfModules.toSheaf _).map (baseChangeTwistIso σ ι d M).hom
  let k := (SheafOfModules.toSheaf _).map (TB.map ((Scheme.Modules.pullback (map σ ι)).map u))
  have hsq : a ≫ b = c ≫ k := by
    simp only [a, b, c, k, ← Functor.map_comp]
    exact congrArg (SheafOfModules.toSheaf _).map (baseChangeTwistIso_hom_naturality σ ι d u)
  simp only [baseChangeTwistCohomologyHom, AddMonoidHom.comp_apply]
  rw [moduleCohomologyPullback_map j, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun t => Sheaf.H.map t q (moduleCohomologyPullback j _ q x)) hsq

end Transport

/-! ### Nitsure's Lemma 3.1 over an affine Noetherian base -/

section LargeTwist

variable {A : Type u} [CommRing A] {ι : Type u}

-- `X.Modules` is `SheafOfModules X.ringCatSheaf` with a `TopCat.Sheaf` of rings; the cohomology
-- maps of the two rows are compared through that presentation, which is not reducible.
set_option backward.isDefEq.respectTransparency false in
/-- **The five-lemma step of Nitsure's Lemma 3.1** (arXiv:math/0504590v1, pp. 14–15): let
`E₁ → E₀ → F → 0` be a sequence on `P^n_A` and `d` a degree such that `H^0` of the `d`-th twists
is right exact on `P^n_A` and, after pullback along `π : P^n_B ⟶ P^n_A`, on `P^n_B`. If the
base-change maps of `E₁(d)` and `E₀(d)` are isomorphisms, so is the base-change map of `F(d)`. -/
theorem baseChangeMap_twist_isIso_of_exact {B : Type u} [CommRing B] (σ : A →+* B)
    {E₁ E₀ F : (ProjectiveSpace A ι).Modules} (u : E₁ ⟶ E₀) (v : E₀ ⟶ F) (d : ℤ)
    (hA : Function.Exact
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).map u)) 0)
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).map v)) 0) ∧
      Function.Surjective
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).map v)) 0))
    (hB : Function.Exact
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).map
            ((Scheme.Modules.pullback (map σ ι)).map u))) 0)
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).map
            ((Scheme.Modules.pullback (map σ ι)).map v))) 0) ∧
      Function.Surjective
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι d)).map
            ((Scheme.Modules.pullback (map σ ι)).map v))) 0))
    (h₁ : IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj E₁) 0))
    (h₀ : IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj E₀) 0)) :
    IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) := by
  let T := moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)
  let α := (toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let p := pullback.fst (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))
  let β := (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let := moduleCohomologyModuleOfHom (ProjectiveSpace A ι) α (T.obj E₁) 0
  let := moduleCohomologyModuleOfHom (ProjectiveSpace A ι) α (T.obj E₀) 0
  let := moduleCohomologyModuleOfHom (ProjectiveSpace A ι) α (T.obj F) 0
  -- the bottom row on the fibre product, through the transport to `P^n_B`
  have hbot : Function.Exact
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((Scheme.Modules.pullback p).map (T.map u))) 0)
        (Sheaf.H.map ((SheafOfModules.toSheaf _).map
          ((Scheme.Modules.pullback p).map (T.map v))) 0) ∧
      Function.Surjective (Sheaf.H.map ((SheafOfModules.toSheaf _).map
        ((Scheme.Modules.pullback p).map (T.map v))) 0) := by
    refine ⟨(AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective _ _ _ _
      (baseChangeTwistCohomologyHom σ ι d E₁ 0) (baseChangeTwistCohomologyHom σ ι d E₀ 0)
      (baseChangeTwistCohomologyHom σ ι d F 0)
      (AddMonoidHom.ext fun x => (baseChangeTwistCohomologyHom_naturality σ ι d u 0 x).symm)
      (AddMonoidHom.ext fun x => (baseChangeTwistCohomologyHom_naturality σ ι d v 0 x).symm)
      (baseChangeTwistCohomologyHom_bijective σ ι d E₁ 0).2
      (baseChangeTwistCohomologyHom_bijective σ ι d E₀ 0)
      (baseChangeTwistCohomologyHom_bijective σ ι d F 0).1).mpr hB.1, fun z => ?_⟩
    obtain ⟨n₂, hn₂⟩ := hB.2 (baseChangeTwistCohomologyHom σ ι d F 0 z)
    obtain ⟨m₂, rfl⟩ := (baseChangeTwistCohomologyHom_bijective σ ι d E₀ 0).2 n₂
    exact ⟨m₂, (baseChangeTwistCohomologyHom_bijective σ ι d F 0).1
      ((baseChangeTwistCohomologyHom_naturality σ ι d v 0 m₂).trans hn₂)⟩
  -- the top row, by right exactness of scalar extension
  have htop := ModuleCat.extendScalars_map_exact_of_surjective σ
    (ModuleCat.ofHom (moduleCohomologyMapOfHom (ProjectiveSpace A ι) α (T.map u) 0))
    (ModuleCat.ofHom (moduleCohomologyMapOfHom (ProjectiveSpace A ι) α (T.map v) 0)) hA.1 hA.2
  have sq₁ := moduleCohomologyBaseChangeMap_naturality (toSpec A ι) σ (T.map u) 0
  have sq₂ := moduleCohomologyBaseChangeMap_naturality (toSpec A ι) σ (T.map v) 0
  rw [ConcreteCategory.isIso_iff_bijective] at h₁ h₀ ⊢
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
    ((ModuleCat.extendScalars σ).map (ModuleCat.ofHom
      (moduleCohomologyMapOfHom (ProjectiveSpace A ι) α (T.map u) 0))).hom.toAddMonoidHom
    ((ModuleCat.extendScalars σ).map (ModuleCat.ofHom
      (moduleCohomologyMapOfHom (ProjectiveSpace A ι) α (T.map v) 0))).hom.toAddMonoidHom
    _ _ (moduleCohomologyBaseChangeMap (toSpec A ι) σ (T.obj E₁) 0).hom.toAddMonoidHom
    (moduleCohomologyBaseChangeMap (toSpec A ι) σ (T.obj E₀) 0).hom.toAddMonoidHom
    (moduleCohomologyBaseChangeMap (toSpec A ι) σ (T.obj F) 0).hom.toAddMonoidHom
    (by ext x; exact (ConcreteCategory.congr_hom sq₁ x).symm)
    (by ext x; exact (ConcreteCategory.congr_hom sq₂ x).symm)
    htop.1 hbot.1 h₁.2 h₀ htop.2 hbot.2

variable [IsNoetherianRing A]

-- `X.Modules` is `SheafOfModules X.ringCatSheaf` with a `TopCat.Sheaf` of rings; the pulled-back
-- presentation is matched through that presentation, which is not reducible.
set_option backward.isDefEq.respectTransparency false in
/-- **Base change of direct images of large twists, without flatness** (Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Lemma 3.1, p. 13, for
`S = Spec A` and `T = Spec B` affine Noetherian). For `F` coherent on `P^n_A` and a ring map
`σ : A →+* B` to a Noetherian ring, there is a bound `N` such that for every `d ≥ N`:
* `H^q(P^n_A, F(d)) = 0` for `q > 0`;
* `H^q((P^n_A)_B, F(d)_B) = 0` for `q > 0`;
* the base-change map `B ⊗_A H^0(P^n_A, F(d)) ⟶ H^0((P^n_A)_B, F(d)_B)` is an isomorphism.

Here `F(d) = 𝒪(d) ⊗ F`, `(P^n_A)_B = P^n_A ×_{Spec A} Spec B`, and `F(d)_B` is the pullback of
`F(d)` along the first projection. The bound depends on `σ`, as Nitsure remarks before the lemma;
it cannot be chosen uniformly in `B`, and the statement fails for some non-Noetherian `B`. -/
theorem exists_twist_baseChange_isIso_of_isNoetherianRing (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace A ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (σ : A →+* B) :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d →
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)) q)) ∧
      (∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom σ)))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))) q)) ∧
      IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨N₀, -, L₁, -, I, hI, J, hJ, u, v, huv, hex, hv⟩ :=
    exists_uniformNegativeTwistTwoStepPresentation A ι F hF 0
  have h₁ := twistingCoproduct_affineLocallyFiniteType A ι (fun _ : J => -(L₁ : ℤ))
  have h₀ := twistingCoproduct_affineLocallyFiniteType A ι (fun _ : I => -(N₀ : ℤ))
  obtain ⟨NA, hNA⟩ := exists_twist_H0_exact_of_exact n e u v huv hex h₁ h₀ hF
  let P := Scheme.Modules.pullback (map σ ι)
  have huv' : P.map u ≫ P.map v = 0 := by rw [← P.map_comp, huv, P.map_zero]
  have hex' : (ShortComplex.mk (P.map u) (P.map v) huv').Exact :=
    hex.map_of_epi_of_preservesCokernel P hv inferInstance
  have : Epi (P.map v) := inferInstance
  obtain ⟨NB, hNB⟩ := exists_twist_H0_exact_of_exact n e (P.map u) (P.map v) huv' hex'
    (affineLocallyFiniteType_pullback (map σ ι) h₁)
    (affineLocallyFiniteType_pullback (map σ ι) h₀)
    (affineLocallyFiniteType_pullback (map σ ι) hF)
  obtain ⟨N₁, hN₁⟩ := exists_twist_baseChange_isIso_and_projective_of_relativeFlat n e _ h₁
    (twistingCoproduct_relativeFlat A ι _)
  obtain ⟨N₂, hN₂⟩ := exists_twist_baseChange_isIso_and_projective_of_relativeFlat n e _ h₀
    (twistingCoproduct_relativeFlat A ι _)
  obtain ⟨NF, hNF⟩ := projectiveSerreVanishing A ι n e F hF
  obtain ⟨NF', hNF'⟩ := projectiveSerreVanishing B ι n e (P.obj F)
    (affineLocallyFiniteType_pullback (map σ ι) hF)
  refine ⟨NA + NB + N₁ + N₂ + NF + NF', fun d hd =>
    ⟨fun q hq => hNF d (by omega) q hq, fun q hq => ?_, ?_⟩⟩
  · have := hNF' d (by omega) q hq
    exact (baseChangeTwistCohomologyHom_bijective σ ι d F q).1.subsingleton
  · exact baseChangeMap_twist_isIso_of_exact σ u v d (hNA d (by omega)) (hNB d (by omega))
      ((hN₁ d (by omega)).1 0 B σ) ((hN₂ d (by omega)).1 0 B σ)

/-- **Nitsure's Lemma 3.1 with the twist taken on `P^n_B`** (arXiv:math/0504590v1, p. 13): under
the hypotheses of `exists_twist_baseChange_isIso_of_isNoetherianRing`, for every `d ≥ N` the
composite of the base-change map with the transport `baseChangeTwistCohomologyHom`,
`B ⊗_A H^0(P^n_A, F(d)) ⟶ H^0((P^n_A)_B, F(d)_B) ⟶ H^0(P^n_B, 𝒪_B(d) ⊗ π^* F)`, is bijective;
here `π = map σ ι : P^n_B ⟶ P^n_A`. -/
theorem exists_twist_baseChange_bijective_projectiveSpace (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace A ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (σ : A →+* B) :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d →
      Function.Bijective (baseChangeTwistCohomologyHom σ ι d F 0 ∘
        moduleCohomologyBaseChangeMap (toSpec A ι) σ
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0) := by
  obtain ⟨N, hN⟩ := exists_twist_baseChange_isIso_of_isNoetherianRing n e F hF σ
  refine ⟨N, fun d hd => ?_⟩
  have h := (hN d hd).2.2
  rw [ConcreteCategory.isIso_iff_bijective] at h
  exact (baseChangeTwistCohomologyHom_bijective σ ι d F 0).comp h

end LargeTwist

end AlgebraicGeometry.Scheme.Cohomology

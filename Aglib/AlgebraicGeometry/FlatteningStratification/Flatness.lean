/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.HilbertPolynomial
public import Aglib.AlgebraicGeometry.Cohomology.Projective.BaseChangeComparison
public import Aglib.AlgebraicGeometry.Cohomology.Projective.BaseChangeTwistLinear
public import Aglib.AlgebraicGeometry.Cohomology.Projective.FlatOfSections
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.AlgebraicGeometry.Limits.Monomorphisms
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.LocalOnBase
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.PullbackSpec
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The universal property of the flattening stratification

Let `A` be a Noetherian ring, `ι ≃ Fin (n + 1)`, `F` a coherent module on `P^n_A` and `N` a bound
beyond which the fibre statements of (B) and (C) hold (`IsFiberBaseChangeBound F N`), with the
strata `S_f = hilbertPolynomialStratum n e F hF N f` of `HilbertPolynomial`. This file proves
Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Thm 4.3 (ii), proof
pp. 22–23, over `S = Spec A`, for locally Noetherian test schemes.

The pullback of `F` to a test scheme `g : T ⟶ Spec A` is taken on the native fibre product
`P^n_A ×_{Spec A} T`: the module `(pullback (pullback.fst (toSpec A ι) g)).obj F`, flat over `T`
through `pullback.snd (toSpec A ι) g` (`Scheme.Modules.relativeFlat`), as in
`relativeFlat_pullback_snd` and in the comparison of `BaseChangeComparison`. On affine pieces
`Spec B` the square `isPullback_map σ ι` (with `P^n_B`) is used instead.

* `hilbertPolynomialStrata n e F hF N = ∐ S_f`, `f` ranging over the polynomials that occur, and
  `hilbertPolynomialStrataι : ∐ S_f ⟶ Spec A`, a monomorphism for `N` beyond the fibre statements of
  (B) and (C) (`mono_hilbertPolynomialStrataι`; the `S_f` are immersions with disjoint images).
* **Theorem 4.3 (ii)** (`exists_lift_hilbertPolynomialStrataι_iff`): for `T` locally Noetherian,
  `g` factors through `∐ S_f` if and only if the pullback of `F` to `P^n_A ×_{Spec A} T` is flat
  over `T`. The direction "⇒" holds for every `T`
  (`relativeFlat_of_exists_lift_hilbertPolynomialStrataι`); flatness over `∐ S_f` itself is
  `relativeFlat_hilbertPolynomialStrata`.
* `exists_iso_hilbertPolynomialStrata`: for two bounds `N`, `N'` beyond the fibre statements of (B)
  and (C), the two schemes `∐ S_f` are isomorphic over `Spec A`.

The route, following Nitsure p. 22:
* "⇒". On an affine open `Spec B` of the locally Noetherian `S_f`, every `π_* F(N + i)` pulls
  back to a finite locally free sheaf, so `B ⊗_A H^0(F(d))` is projective for `d ≥ N`
  (`isFiniteLocallyFree_pullback_directImageTwist_iff`). Lemma 3.1, with a bound depending on
  `Spec B ⟶ Spec A`, identifies it with `H^0(P^n_B, F_B(d))` for large `d`
  (`baseChangeTwistCohomologyLinearEquiv` for the `B`-linear transport), and Lemma 3.2 gives
  flatness of `F_B` (`relativeFlat_map_of_isFiniteLocallyFree_pullback_directImageTwist`).
  Flatness is local on the base (`relativeFlat_of_isPullback_of_forall_exists`) and stable under
  base change (`relativeFlat_of_isPullback_comp`).
* "⇐". On an affine open `Spec B` of `T`, the comparison of `BaseChangeComparison` makes
  `B ⊗_A H^0(F(m)) ≅ H^0(X_B, F(m)_B)` projective for every `m ≥ N`
  (`moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_isFiberBaseChangeBound`, the
  bound being uniform in `B`), so every `g^* π_* F(m)`, `m ≥ N`, is finite locally free
  (`isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat_pullback`). Their fibre ranks
  `P_{g t}(N + j)`, `j ≤ n`, are locally constant and determine `P_{g t}`, so near each point `g`
  factors through one `S_f` (`exists_lift_hilbertPolynomialStratumι_iff`); the local
  factorizations glue because `∐ S_f ⟶ Spec A` is a monomorphism
  (`Scheme.exists_lift_of_mono_of_forall_exists`).

Two steps of Nitsure's printed proof are made explicit. The converse factorization (p. 22, last
lines) needs `φ^* π_* F(m) ≅ π_{T*} F_T(m)` for every `m ≥ N`, because `S_f` imposes a rank
condition on every `π_* F(N + i)`; it is proved here for locally Noetherian `T`, whence that
hypothesis. Local constancy of the Hilbert polynomials over `T` is replaced by local constancy of
the ranks of the locally free `g^* π_* F(N + j)`, `j ≤ n`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {ι : Type u}

/-! ### Global sections of the direct images over affine test schemes -/

variable [IsNoetherianRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace A ι).Modules)
  (hF : affineLocallyFiniteType (ProjectiveSpace A ι) F)

include e hF in
/-- **Local freeness of `σ^* π_* F(d)` is projectivity of `B ⊗_A H^0(P^n_A, F(d))`**: for a ring
map `σ : A →+* B` to a Noetherian ring, `(Spec σ)^* π_* F(d)` is finite locally free on `Spec B`
if and only if `B ⊗_A H^0(P^n_A, F(d))` is a projective `B`-module. -/
theorem isFiniteLocallyFree_pullback_directImageTwist_iff {B : Type u} [CommRing B]
    [IsNoetherianRing B] (σ : A →+* B) (d : ℤ) :
    IsFiniteLocallyFree (Spec (CommRingCat.of B))
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom σ))).obj (directImageTwist F d)) ↔
      (letI := moduleCohomologyModuleOfHom (ProjectiveSpace A ι)
        ((toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0
       Module.Projective B ((ModuleCat.extendScalars σ).obj (ModuleCat.of A
        (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)) 0)))) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have hE := affineLocallyFiniteType_directImageTwist n e F hF d
  have : (directImageTwist F d).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hE R j).1)
  let := moduleCohomologyModuleOfHom (ProjectiveSpace A ι)
    ((toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F) 0
  let eΓ := directImageTwistSectionsLinearEquiv F hF d
  have : Module.Finite A (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)) 0) :=
    moduleCohomology_finite_of_proper A (toSpec A ι) _
      (twistingTensor_affineLocallyFiniteType A ι d F hF) 0
  have : Module.Finite A (moduleSpecΓFunctor.obj (directImageTwist F d)) :=
    Module.Finite.equiv eΓ.symm
  rw [isFiniteLocallyFree_pullback_specMap_iff_projective (CommRingCat.ofHom σ)]
  let := σ.toAlgebra
  let eB : (ModuleCat.extendScalars (algebraMap A B)).obj
      (moduleSpecΓFunctor.obj (directImageTwist F d)) ≃ₗ[B]
      (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A
        (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F)) 0)) :=
    (ModuleCat.extendScalarsAlgebraObjIso A B
      (moduleSpecΓFunctor.obj (directImageTwist F d))).toLinearEquiv.trans
      ((eΓ.baseChange A B _ _).trans (ModuleCat.extendScalarsAlgebraObjIso A B (ModuleCat.of A
        (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι d)).obj F))
            0))).toLinearEquiv.symm)
  exact ⟨fun h => Module.Projective.of_equiv eB, fun h => Module.Projective.of_equiv eB.symm⟩

include e hF in
/-- **Flatness over an affine piece of a stratum** (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3 (ii), p. 22, "`F` is flat over `S_f`", on an affine open `Spec B`): for a ring map
`σ : A →+* B` to a Noetherian ring such that every `(Spec σ)^* π_* F(N + i)`, `i ≥ 0`, is finite
locally free, the pullback `F_B` of `F` to `P^n_B` is flat over `B`. Lemma 3.1
(`exists_twist_baseChange_isIso_of_isNoetherianRing`, with a bound depending on `σ`) identifies
`B ⊗_A H^0(F(d))` with `H^0(P^n_B, F_B(d))` for large `d`, and Lemma 3.2
(`relativeFlat_of_projective_twistedSections`) concludes. -/
theorem relativeFlat_map_of_isFiniteLocallyFree_pullback_directImageTwist (N : ℕ)
    {B : Type u} [CommRing B] [IsNoetherianRing B] (σ : A →+* B)
    (h : ∀ i : ℕ, IsFiniteLocallyFree (Spec (CommRingCat.of B))
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom σ))).obj
        (directImageTwist F ((N + i : ℕ) : ℤ)))) :
    relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  obtain ⟨N₁, hN₁⟩ := exists_twist_baseChange_isIso_of_isNoetherianRing n e F hF σ
  refine relativeFlat_of_projective_twistedSections _ ((max N N₁ : ℕ) : ℤ) fun d hd => ?_
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, d = ((N + i : ℕ) : ℤ) := ⟨(d - N).toNat, by omega⟩
  have hP := (isFiniteLocallyFree_pullback_directImageTwist_iff n e F hF σ _).mp (h i)
  have hiso := (hN₁ ((N + i : ℕ) : ℤ) (by omega)).2.2
  intro α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace A ι)
    ((toSpec A ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι ((N + i : ℕ) : ℤ))).obj F)
    0
  have hP' : Module.Projective B ((ModuleCat.extendScalars σ).obj (ModuleCat.of A
      (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι)
          (twistingSheaf A ι ((N + i : ℕ) : ℤ))).obj F)) 0))) := hP
  let := moduleCohomologyModuleOfHom (ProjectiveSpace B ι) α
    ((moduleTensorLeftFunctor (ProjectiveSpace B ι) (twistingSheaf B ι ((N + i : ℕ) : ℤ))).obj
      ((Scheme.Modules.pullback (map σ ι)).obj F)) 0
  exact Module.Projective.of_equiv ((asIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
    ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι ((N + i : ℕ) : ℤ))).obj F)
    0)).toLinearEquiv.trans (baseChangeTwistCohomologyLinearEquiv σ ι ((N + i : ℕ) : ℤ) F 0))

include e hF in
/-- **Base change of global sections beyond the bound of the fibre statements of (B) and (C),
uniformly in the test ring** (Nitsure, arXiv:math/0504590v1, proof of Thm 4.3 (ii), pp. 22–23): for
`N` beyond the fibre statements of (B) and (C), every Noetherian `B` with `σ : A →+* B` and `F_B`
flat on `P^n_B`, and every `m ≥ N`, the base-change map `B ⊗_A H^0(P^n_A, F(m)) ⟶ H^0(X_B, F(m)_B)`
is an isomorphism and its target is projective. The bound does not depend on `B`, unlike that of
Lemma 3.1. -/
theorem moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_isFiberBaseChangeBound
    {N : ℕ} (hN : IsFiberBaseChangeBound F N) {B : Type u} [CommRing B] [IsNoetherianRing B]
    (σ : A →+* B) (hflat : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F))
    (m : ℤ) (hm : (N : ℤ) ≤ m) :
    IsIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
        ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F) 0) ∧
      (let β := (pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
       letI := moduleCohomologyModuleOfHom _ β ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
         (Spec.map (CommRingCat.ofHom σ)))).obj
         ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F)) 0
       Module.Projective B (Sheaf.H.{u + 1}
         (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
          ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
            (Spec.map (CommRingCat.ofHom σ)))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F)))
              0)) :=
  moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_fiberwise σ n e F hF m
    (fun s => (hN m hm s).2) (fun s => (hN m hm s).1) hflat

include e hF in
/-- **Local freeness of the direct images over a flat affine test scheme** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3 (ii), p. 22, converse direction, on an affine open
`Spec B` of `T`): for `N` beyond the fibre statements of (B) and (C), a Noetherian `B` with
`σ : A →+* B` and `F_B` flat on `P^n_B`, every `(Spec σ)^* π_* F(m)`, `m ≥ N`, is finite locally
free. -/
theorem isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat {N : ℕ}
    (hN : IsFiberBaseChangeBound F N) {B : Type u} [CommRing B] [IsNoetherianRing B]
    (σ : A →+* B) (hflat : relativeFlat (toSpec B ι) ((Scheme.Modules.pullback (map σ ι)).obj F))
    (m : ℤ) (hm : (N : ℤ) ≤ m) :
    IsFiniteLocallyFree (Spec (CommRingCat.of B))
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom σ))).obj (directImageTwist F m)) := by
  obtain ⟨hiso, hproj⟩ :=
    moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_isFiberBaseChangeBound n e F hF hN
      σ hflat m hm
  refine (isFiniteLocallyFree_pullback_directImageTwist_iff n e F hF σ m).mpr ?_
  let := moduleCohomologyModuleOfHom _
    ((pullback.snd (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
    ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
      (Spec.map (CommRingCat.ofHom σ)))).obj
      ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F)) 0
  have hproj' : Module.Projective B (Sheaf.H.{u + 1}
      (moduleAddSheaf (pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)))
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
          (Spec.map (CommRingCat.ofHom σ)))).obj
          ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F))) 0) :=
    hproj
  exact Module.Projective.of_equiv (asIso (moduleCohomologyBaseChangeMap (toSpec A ι) σ
    ((moduleTensorLeftFunctor (ProjectiveSpace A ι) (twistingSheaf A ι m)).obj F)
    0)).toLinearEquiv.symm

/-! ### Flatness over the strata -/

include e hF in
/-- **`F` is flat over every stratum** (Nitsure, arXiv:math/0504590v1, proof of Thm 4.3 (ii),
p. 22): for `N` beyond the fibre statements of (B) and (C) and a polynomial `f` that occurs, the
pullback of `F` to `P^n_A ×_{Spec A} S_f` is flat over `S_f`. On an affine open `Spec B` of the
locally Noetherian `S_f`, every `π_* F(N + i)` pulls back to a finite locally free sheaf, so
`relativeFlat_map_of_isFiniteLocallyFree_pullback_directImageTwist` applies; relative flatness
is local on the base (`relativeFlat_of_isPullback_of_forall_exists`). -/
theorem relativeFlat_hilbertPolynomialStratum {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    (f : Polynomial ℚ) (hf : f ∈ Set.range (fiberHilbertPolynomial F)) :
    relativeFlat (pullback.snd (toSpec A ι) (hilbertPolynomialStratumι n e F hF N f))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (hilbertPolynomialStratumι n e F hF N f))).obj F) := by
  have : IsLocallyNoetherian (hilbertPolynomialStratum n e F hF N f) :=
    LocallyOfFiniteType.isLocallyNoetherian (hilbertPolynomialStratumι n e F hF N f)
  have hfree (i : ℕ) : IsFiniteLocallyFree (hilbertPolynomialStratum n e F hF N f)
      ((Scheme.Modules.pullback (hilbertPolynomialStratumι n e F hF N f)).obj
        (directImageTwist F ((N + i : ℕ) : ℤ))) :=
    ((exists_lift_hilbertPolynomialStratumι_iff n e F hF hN f hf
      (hilbertPolynomialStratumι n e F hF N f)).mp ⟨𝟙 _, Category.id_comp _⟩ i).isFiniteLocallyFree
  refine relativeFlat_of_isPullback_of_forall_exists (IsPullback.of_hasPullback _ _) F fun s => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    (hilbertPolynomialStratum n e F hF N f).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ s) isOpen_univ
  have : IsNoetherianRing Γ(hilbertPolynomialStratum n e F hF N f, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let φ : CommRingCat.of A ⟶ Γ(hilbertPolynomialStratum n e F hF N f, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (hilbertPolynomialStratumι n e F hF N f).appLE ⊤ V (by simp)
  have hφ : Spec.map (CommRingCat.ofHom φ.hom) =
      hV.fromSpec ≫ hilbertPolynomialStratumι n e F hF N f :=
    SpecMap_affineOpen_baseRingHom (hilbertPolynomialStratumι n e F hF N f) hV
  refine ⟨Spec (CommRingCat.of Γ(hilbertPolynomialStratum n e F hF N f, V)), hV.fromSpec,
    hV.isOpenImmersion_fromSpec, ?_, ProjectiveSpace Γ(hilbertPolynomialStratum n e F hF N f, V) ι,
    map φ.hom ι, toSpec Γ(hilbertPolynomialStratum n e F hF N f, V) ι, ?_, ?_⟩
  · rw [hV.range_fromSpec]
    exact hsV
  · have h := isPullback_map φ.hom ι
    rwa [hφ] at h
  · refine relativeFlat_map_of_isFiniteLocallyFree_pullback_directImageTwist n e F hF N φ.hom
      fun i => ?_
    have := hfree i
    have h' : IsFiniteLocallyFree _
        ((Scheme.Modules.pullback (hilbertPolynomialStratumι n e F hF N f) ⋙
          Scheme.Modules.pullback hV.fromSpec).obj (directImageTwist F ((N + i : ℕ) : ℤ))) :=
      finiteLocallyFree_pullback hV.fromSpec _
    exact finiteLocallyFree_of_iso ((Scheme.Modules.pullbackComp hV.fromSpec
      (hilbertPolynomialStratumι n e F hF N f)).app _ ≪≫
        (Scheme.Modules.pullbackCongr hφ.symm).app _)

/-! ### The disjoint union of the strata -/

/-- The disjoint union `∐ S_f` of Nitsure's strata, over the polynomials `f` that occur. -/
abbrev hilbertPolynomialStrata (N : ℕ) : Scheme.{u} :=
  ∐ fun f : Set.range (fiberHilbertPolynomial F) => hilbertPolynomialStratum n e F hF N f

/-- The morphism `∐ S_f ⟶ Spec A` induced by the immersions of the strata. -/
def hilbertPolynomialStrataι (N : ℕ) :
    hilbertPolynomialStrata n e F hF N ⟶ Spec (CommRingCat.of A) :=
  Sigma.desc fun f : Set.range (fiberHilbertPolynomial F) =>
    hilbertPolynomialStratumι n e F hF N f

@[reassoc (attr := simp)]
theorem sigmaι_hilbertPolynomialStrataι (N : ℕ) (f : Set.range (fiberHilbertPolynomial F)) :
    Sigma.ι (fun f : Set.range (fiberHilbertPolynomial F) =>
        hilbertPolynomialStratum n e F hF N f) f ≫ hilbertPolynomialStrataι n e F hF N =
      hilbertPolynomialStratumι n e F hF N f :=
  Sigma.ι_comp_desc _ _

include e hF in
/-- **The disjoint union of the strata is a monomorphism** into `Spec A`, for `N` beyond the fibre
statements of (B) and (C): the strata are immersions with pairwise disjoint images (Thm 4.3 (i)). -/
theorem mono_hilbertPolynomialStrataι {N : ℕ} (hN : IsFiberBaseChangeBound F N) :
    Mono (hilbertPolynomialStrataι n e F hF N) :=
  Scheme.mono_sigmaDesc_of_pairwise_disjoint _ fun f g hfg => by
    dsimp only
    rw [range_hilbertPolynomialStratumι n e F hF hN f f.2,
      range_hilbertPolynomialStratumι n e F hF hN g g.2]
    exact Set.disjoint_left.mpr fun s h₁ h₂ => hfg (Subtype.ext (h₁.symm.trans h₂))

include e hF in
/-- **Flatness after factoring through the strata** (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3 (ii), p. 22): if `g : T ⟶ Spec A` factors through `∐ S_f`, the pullback of `F` to
`P^n_A ×_{Spec A} T` is flat over `T`. Each point of `T` has an open neighbourhood mapping to one
stratum, over which flatness is the base change of `relativeFlat_hilbertPolynomialStratum`. -/
theorem relativeFlat_of_exists_lift_hilbertPolynomialStrataι {N : ℕ}
    (hN : IsFiberBaseChangeBound F N) {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (h : T ⟶ hilbertPolynomialStrata n e F hF N)
    (hg : h ≫ hilbertPolynomialStrataι n e F hF N = g) :
    relativeFlat (pullback.snd (toSpec A ι) g)
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj F) := by
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  refine relativeFlat_of_isPullback_of_forall_exists (IsPullback.of_hasPullback _ _) F fun t => ?_
  obtain ⟨f, y, hy⟩ := Scheme.exists_sigmaι_eq (h t)
  let ιf := Sigma.ι (fun f : Set.range (fiberHilbertPolynomial F) =>
    hilbertPolynomialStratum n e F hF N f) f
  let U : T.Opens := h ⁻¹ᵁ ιf.opensRange
  have hsub : Set.range (U.ι ≫ h) ⊆ Set.range ιf := by
    rintro _ ⟨u, rfl⟩
    exact u.2
  let l := IsOpenImmersion.lift ιf (U.ι ≫ h) hsub
  have hl : l ≫ hilbertPolynomialStratumι n e F hF N f = U.ι ≫ g := by
    rw [← sigmaι_hilbertPolynomialStrataι n e F hF N f, ← Category.assoc,
      IsOpenImmersion.lift_fac, Category.assoc, hg]
  refine ⟨U.toScheme, U.ι, inferInstance, ⟨⟨t, show h t ∈ Set.range ιf from ⟨y, hy⟩⟩, rfl⟩,
    pullback (toSpec A ι) (l ≫ hilbertPolynomialStratumι n e F hF N f), pullback.fst _ _,
    pullback.snd _ _, ?_, ?_⟩
  · rw [← hl]
    exact IsPullback.of_hasPullback _ _
  · exact relativeFlat_of_isPullback_comp (IsPullback.of_hasPullback _ _)
      (IsPullback.of_hasPullback _ _) F (relativeFlat_hilbertPolynomialStratum n e F hF hN f f.2)

/-! ### The converse: flat test schemes factor through the strata -/

include e hF in
/-- **The direct images pull back to finite locally free sheaves on a flat test scheme** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3 (ii), p. 22, converse direction): for `N` beyond the fibre
statements of (B) and (C), a locally Noetherian `T` and `g : T ⟶ Spec A` such that the pullback of
`F` to `P^n_A ×_{Spec A} T` is flat over `T`, every `g^* π_* F(m)`, `m ≥ N`, is finite locally free.
On an affine open `Spec B` of `T` this is
`isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat`. -/
theorem isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat_pullback {N : ℕ}
    (hN : IsFiberBaseChangeBound F N) {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ Spec (CommRingCat.of A))
    (hflat : relativeFlat (pullback.snd (toSpec A ι) g)
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj F))
    (m : ℤ) (hm : (N : ℤ) ≤ m) :
    IsFiniteLocallyFree T ((Scheme.Modules.pullback g).obj (directImageTwist F m)) := by
  have : F.IsQuasicoherent := quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  have : ∀ V : T.affineOpens, IsOpenImmersion V.2.fromSpec := fun V => V.2.isOpenImmersion_fromSpec
  refine finiteLocallyFree_of_openImmersionCover _ (fun V : T.affineOpens => Spec Γ(T, V))
    (fun V => V.2.fromSpec) (fun t => ?_) (fun V => ?_)
  · obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
    obtain ⟨y, hy⟩ : t ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      exact htV
    exact ⟨⟨V, hV⟩, y, hy⟩
  · have : IsNoetherianRing Γ(T, V) := IsLocallyNoetherian.component_noetherian V
    let φ : CommRingCat.of A ⟶ Γ(T, V) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ V.1 (by simp)
    have hφ : Spec.map (CommRingCat.ofHom φ.hom) = V.2.fromSpec ≫ g :=
      SpecMap_affineOpen_baseRingHom g V.2
    have hflatB :
        relativeFlat (toSpec Γ(T, V) ι) ((Scheme.Modules.pullback (map φ.hom ι)).obj F) := by
      have h := isPullback_map φ.hom ι
      rw [hφ] at h
      exact relativeFlat_of_isPullback_comp (IsPullback.of_hasPullback _ _) h F hflat
    have := isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat n e F hF hN φ.hom hflatB
      m hm
    exact finiteLocallyFree_of_iso ((Scheme.Modules.pullbackCongr hφ).app _ ≪≫
      ((Scheme.Modules.pullbackComp V.2.fromSpec g).app _).symm ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback V.2.fromSpec).app _).symm)

include e hF in
/-- **Flat test schemes factor through the strata** (Nitsure, arXiv:math/0504590v1, proof of
Thm 4.3 (ii), p. 22, converse direction): for `N` beyond the fibre statements of (B) and (C), a
locally Noetherian `T` and `g : T ⟶ Spec A` such that the pullback of `F` to `P^n_A ×_{Spec A} T` is
flat over `T`, `g` factors through `∐ S_f`. The sheaves `g^* π_* F(N + j)` are finite locally free,
so their fibre ranks `P_{g t}(N + j)` are locally constant; near each point the fibre Hilbert
polynomial is therefore constant, equal to some `f`, and the universal property of `S_f`
(`exists_lift_hilbertPolynomialStratumι_iff`) gives a local lift. The local lifts glue because
`∐ S_f ⟶ Spec A` is a monomorphism. -/
theorem exists_lift_hilbertPolynomialStrataι_of_relativeFlat {N : ℕ}
    (hN : IsFiberBaseChangeBound F N) {T : Scheme.{u}} [IsLocallyNoetherian T]
    (g : T ⟶ Spec (CommRingCat.of A))
    (hflat : relativeFlat (pullback.snd (toSpec A ι) g)
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj F)) :
    ∃ h : T ⟶ hilbertPolynomialStrata n e F hF N, h ≫ hilbertPolynomialStrataι n e F hF N = g := by
  have hE := fun i : ℕ => affineLocallyFiniteType_directImageTwist n e F hF ((N + i : ℕ) : ℤ)
  have : ∀ i : ℕ, (directImageTwist F ((N + i : ℕ) : ℤ)).IsFinitePresentation :=
    fun i => affineLocallyFiniteType_finitePresentation (hE i)
  have hfree (i : ℕ) : IsFiniteLocallyFree T
      ((Scheme.Modules.pullback g).obj (directImageTwist F ((N + i : ℕ) : ℤ))) :=
    isFiniteLocallyFree_pullback_directImageTwist_of_relativeFlat_pullback n e F hF hN g hflat _
      (by omega)
  have := mono_hilbertPolynomialStrataι n e F hF hN
  refine Scheme.exists_lift_of_mono_of_forall_exists _ g fun t => ?_
  let W : T.Opens := ⟨⋂ j ∈ Finset.range (n + 1), {t' | sheafRank ((Scheme.Modules.pullback g).obj
      (directImageTwist F ((N + j : ℕ) : ℤ))) t' = sheafRank ((Scheme.Modules.pullback g).obj
        (directImageTwist F ((N + j : ℕ) : ℤ))) t},
    isOpen_biInter_finset fun j _ => by
      have := hfree j
      exact (sheafRank_locallyConstant _).isOpen_fiber _⟩
  have htW : t ∈ W := Set.mem_iInter₂.mpr fun j _ => rfl
  have hP (w : W.toScheme) :
      fiberHilbertPolynomial F (g (W.ι w)) = fiberHilbertPolynomial F (g t) :=
    fiberHilbertPolynomial_eq_of_sheafRank_eq n e F hF hN _ _ fun j hj => by
      have hw : W.ι w ∈ (W : Set T) := w.2
      have h := Set.mem_iInter₂.mp hw j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      change sheafRank _ (W.ι w) = sheafRank _ t at h
      rwa [sheafRank_pullback, sheafRank_pullback] at h
  let f : Set.range (fiberHilbertPolynomial F) := ⟨fiberHilbertPolynomial F (g t), g t, rfl⟩
  obtain ⟨l, hl⟩ := (exists_lift_hilbertPolynomialStratumι_iff n e F hF hN f f.2
    (W.ι ≫ g)).mpr fun i => by
      have := hfree i
      have h' : IsFiniteLocallyFree W ((Scheme.Modules.pullback g ⋙
          Scheme.Modules.pullback W.ι).obj (directImageTwist F ((N + i : ℕ) : ℤ))) :=
        finiteLocallyFree_pullback W.ι _
      have : IsFiniteLocallyFree W ((Scheme.Modules.pullback (W.ι ≫ g)).obj
          (directImageTwist F ((N + i : ℕ) : ℤ))) :=
        finiteLocallyFree_of_iso ((Scheme.Modules.pullbackComp W.ι g).app _)
      refine (sheafHasRank_iff_rank_eq _ _).mpr fun w => ?_
      change _ = hilbertPolynomialRank N (fiberHilbertPolynomial F (g t)) i
      have h₁ := hilbertPolynomialRank_fiberHilbertPolynomial n e F hF hN (g (W.ι w)) i
      rw [hP w] at h₁
      rw [sheafRank_pullback, Scheme.Hom.comp_apply]
      exact h₁.symm
  exact ⟨W, htW, l ≫ Sigma.ι (fun f : Set.range (fiberHilbertPolynomial F) =>
    hilbertPolynomialStratum n e F hF N f) f, by
      rw [Category.assoc, sigmaι_hilbertPolynomialStrataι, hl]⟩

include e hF in
/-- **The universal property of the flattening stratification** (Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Thm 4.3 (ii), proof
pp. 22–23), over the affine Noetherian base `S = Spec A`, for locally Noetherian test schemes:
for `N` beyond the fibre statements of (B) and (C), a locally Noetherian `T` and `g : T ⟶ Spec A`,
the morphism `g` factors through the disjoint union `∐ S_f ⟶ Spec A` of the strata, `f` ranging over
the polynomials that occur, if and only if the pullback of `F` to `P^n_A ×_{Spec A} T` is flat over
`T`. The factorization is unique (`mono_hilbertPolynomialStrataι`). The direction "⇒" holds for
every `T` (`relativeFlat_of_exists_lift_hilbertPolynomialStrataι`). -/
theorem exists_lift_hilbertPolynomialStrataι_iff {N : ℕ} (hN : IsFiberBaseChangeBound F N)
    {T : Scheme.{u}} [IsLocallyNoetherian T] (g : T ⟶ Spec (CommRingCat.of A)) :
    (∃ h : T ⟶ hilbertPolynomialStrata n e F hF N, h ≫ hilbertPolynomialStrataι n e F hF N = g) ↔
      relativeFlat (pullback.snd (toSpec A ι) g)
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj F) :=
  ⟨fun ⟨h, hg⟩ => relativeFlat_of_exists_lift_hilbertPolynomialStrataι n e F hF hN g h hg,
    exists_lift_hilbertPolynomialStrataι_of_relativeFlat n e F hF hN g⟩

include e hF in
/-- **`F` is flat over the disjoint union of the strata** (Nitsure, arXiv:math/0504590v1,
Thm 4.3 (ii), first assertion): for `N` beyond the fibre statements of (B) and (C), the pullback of
`F` to `P^n_A ×_{Spec A} ∐ S_f` is flat over `∐ S_f`. -/
theorem relativeFlat_hilbertPolynomialStrata {N : ℕ} (hN : IsFiberBaseChangeBound F N) :
    relativeFlat (pullback.snd (toSpec A ι) (hilbertPolynomialStrataι n e F hF N))
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι)
        (hilbertPolynomialStrataι n e F hF N))).obj F) :=
  relativeFlat_of_exists_lift_hilbertPolynomialStrataι n e F hF hN _ (𝟙 _) (Category.id_comp _)

/-- The disjoint union of the strata is locally Noetherian. -/
instance isLocallyNoetherian_hilbertPolynomialStrata (N : ℕ) :
    IsLocallyNoetherian (hilbertPolynomialStrata n e F hF N) := by
  refine (isLocallyNoetherian_iff_openCover (sigmaOpenCover _)).mpr
    fun (f : Set.range (fiberHilbertPolynomial F)) => ?_
  have h := LocallyOfFiniteType.isLocallyNoetherian (hilbertPolynomialStratumι n e F hF N f)
  exact h

include e hF in
/-- **The disjoint union of the strata does not depend on the bound** (compare Nitsure,
arXiv:math/0504590v1, Thm 4.3 (ii), "the subscheme `S_f` is uniquely determined"): for two
bounds `N`, `N'` beyond the fibre statements of (B) and (C), the schemes `∐ S_f` built from `N` and
from `N'` are isomorphic over `Spec A`. Both represent flatness of the pullback of `F` on locally
Noetherian schemes, and both are locally Noetherian. -/
theorem exists_iso_hilbertPolynomialStrata {N N' : ℕ} (hN : IsFiberBaseChangeBound F N)
    (hN' : IsFiberBaseChangeBound F N') :
    ∃ φ : hilbertPolynomialStrata n e F hF N ≅ hilbertPolynomialStrata n e F hF N',
      φ.hom ≫ hilbertPolynomialStrataι n e F hF N' = hilbertPolynomialStrataι n e F hF N := by
  have := mono_hilbertPolynomialStrataι n e F hF hN
  have := mono_hilbertPolynomialStrataι n e F hF hN'
  obtain ⟨a, ha⟩ := (exists_lift_hilbertPolynomialStrataι_iff n e F hF hN' _).mpr
    (relativeFlat_hilbertPolynomialStrata n e F hF hN)
  obtain ⟨b, hb⟩ := (exists_lift_hilbertPolynomialStrataι_iff n e F hF hN _).mpr
    (relativeFlat_hilbertPolynomialStrata n e F hF hN')
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · rw [← cancel_mono (hilbertPolynomialStrataι n e F hF N), Category.assoc, hb, ha,
      Category.id_comp]
  · rw [← cancel_mono (hilbertPolynomialStrataι n e F hF N'), Category.assoc, ha, hb,
      Category.id_comp]

end AlgebraicGeometry.Scheme.Cohomology

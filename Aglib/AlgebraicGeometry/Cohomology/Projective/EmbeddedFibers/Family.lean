/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Projective
public import Aglib.AlgebraicGeometry.Cohomology.Fibers.BaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Proper.Semicontinuity
public import Aglib.AlgebraicGeometry.Cohomology.Proper.EulerCharacteristic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.Topology.NoetherianSpace
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Fibre conditions on twisted line bundles in a projective family

Let `i : X ⟶ P^N_A` be a morphism with `f = i ≫ toSpec A ι` proper and flat, let `T` be a locally
Noetherian scheme over `Spec A` and `L` a line bundle on `X_T = X ×_{Spec A} T`. For `t ∈ T` write
`L_t` for the pullback of `L` to `X_{κ(t)} = X ×_{Spec A} Spec κ(t)`
(`residueFieldBaseChange`). Then:

* **Base change.** For `b : T' ⟶ T` over `Spec A` (no Noetherian or flatness hypothesis, `f`
  proper), `h^q(X_{t'}, O(n) ⊗ (b^* L)_{t'}) = h^q(X_{b t'}, O(n) ⊗ L_{b t'})`, and likewise for
  `χ` (`embeddedFiberTwistDim_familyBaseChange`, `embeddedFiberTwistEulerChar_familyBaseChange`),
  through the fibre identification of `Cohomology/Fibers/BaseChange` and field extension; the base
  change of a twist is the twist of the base change (`familyBaseChangePulledTwistIso`).
* `t ↦ h^q(X_t, O(n) ⊗ L_t)` is upper semicontinuous
  (`upperSemicontinuous_embeddedFiberTwistDim`) and `t ↦ χ(X_t, O(n) ⊗ L_t)` is locally constant
  (`isLocallyConstant_embeddedFiberTwistEulerChar`), from the proper theorems
  `upperSemicontinuous_modulePointFiberCohomologyDimension_of_proper` and
  `isLocallyConstant_modulePointFiberEulerChar_of_proper` (Stacks, Tag 0B9T, for the latter)
  applied to the twist, a line bundle flat over `T`, through the identification of point fibres
  (`modulePointFiberCohomologyDimension_pulledTwist`).
* For every `c : ℤ → ℚ`, the locus where `χ(X_t, O(n) ⊗ L_t) = c(n)` for all `n` is open and
  closed (`isClopen_setOf_embeddedFiberTwistEulerChar_eq`): all the functions
  `t ↦ χ(X_t, O(n) ⊗ L_t)` are jointly locally constant on a locally Noetherian scheme
  (`Scheme.isLocallyConstant_pi_of_isLocallyNoetherian`).
* For a closed immersion `i` and `ι ≃ Fin (N + 1)`, the locus where `h^q(X_t, O(n) ⊗ L_t) = 0`
  for all `q ≥ 1` and `n ≥ m` is open (`isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero`): it is
  cut out by the finitely many `(q, n)` with `1 ≤ q ≤ N`, `m ≤ n < m + N`
  (`embeddedFiberTwistDim_vanishing_iff`).
* On that locus `h^0(X_t, O(m) ⊗ L_t) = χ(X_t, O(m) ⊗ L_t)` is locally constant, so the loci
  where additionally `h^0 ≠ 0`, `h^0 = 0`, or `h^0 = r` for a fixed `r`, are open
  (`isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_ne_zero`,
  `isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_eq_zero`,
  `isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_eq`).

These are the openness statements in the proof of Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 4.8, pp. 28–29 (for (4.8.1) Kleiman cites EGA III₂ 7.9.11, for (4.8.3)
Serre's theorem), with the nonvanishing condition of the plan's repair of `Pic^φ_m`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry

/-- **Families of locally constant functions on a locally Noetherian scheme are jointly locally
constant**, by the Noetherian case (`TopologicalSpace.NoetherianSpace.isLocallyConstant_pi`) on
affine opens. -/
theorem Scheme.isLocallyConstant_pi_of_isLocallyNoetherian {T : Scheme.{u}}
    [IsLocallyNoetherian T] {I : Type*} {β : I → Type*} {g : ∀ j, T → β j}
    (hg : ∀ j, IsLocallyConstant (g j)) : IsLocallyConstant (fun t j => g j t) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro t
  obtain ⟨W, hW, htW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show t ∈ (⊤ : T.Opens) from trivial)
  have := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hN : TopologicalSpace.NoetherianSpace W := noetherianSpace_of_isAffineOpen W hW
  have hloc : IsLocallyConstant (fun (w : W) j => g j w) :=
    @TopologicalSpace.NoetherianSpace.isLocallyConstant_pi W _ hN _ _ _
      (fun j => (hg j).comp_continuous continuous_subtype_val)
  obtain ⟨V, hV, hwV, hconst⟩ := (IsLocallyConstant.iff_exists_open _).mp hloc ⟨t, htW⟩
  refine ⟨Subtype.val '' V, W.isOpen.isOpenEmbedding_subtypeVal.isOpenMap V hV,
    ⟨_, hwV, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hconst w hw

namespace Scheme.Cohomology

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)

variable {T : Scheme.{u}} (g : T ⟶ Spec (.of A))

section BaseChange

/-- Field-point base change with an arbitrary base point equal to `Spec σ ≫ k`: twisted fibre
dimensions are unchanged (`embeddedFiberTwistDim_fieldBaseChange`). -/
theorem embeddedFiberTwistDim_pullbackMap_of_eq [QuasiCompact (i ≫ toSpec A ι)]
    [QuasiSeparated (i ≫ toSpec A ι)] {K K' : Type u} [Field K] [Field K']
    (k : Spec (.of K) ⟶ Spec (.of A)) (φ : CommRingCat.of K ⟶ CommRingCat.of K')
    (k' : Spec (.of K') ⟶ Spec (.of A)) (hk : Spec.map φ ≫ k = k')
    (M : (pullback (i ≫ toSpec A ι) k).Modules) (n : ℤ)
    [(pulledTwist (pullback.fst (i ≫ toSpec A ι) k ≫ i) n M).IsQuasicoherent] (q : ℕ) :
    embeddedFiberTwistDim i k'
        ((Scheme.Modules.pullback (pullback.map (i ≫ toSpec A ι) k' (i ≫ toSpec A ι) k (𝟙 X)
          (Spec.map φ) (𝟙 _) (by simp) (by simp [hk]))).obj M) n q =
      embeddedFiberTwistDim i k M n q := by
  subst hk
  exact embeddedFiberTwistDim_fieldBaseChange i k φ.hom M n q

variable {T' : Scheme.{u}} (s' : T' ⟶ Spec (.of A)) (b : T' ⟶ T) (hb : b ≫ g = s')

/-- **Base change of the family does not change the fibre invariants** (the condition
`holds_map` of the open-subsheaf lemma): for `b : T' ⟶ T` over `Spec A`, `t' ∈ T'` and a line
bundle `L` on `X_T`, `h^q(X_{t'}, O(n) ⊗ (b^* L)_{t'}) = h^q(X_{b t'}, O(n) ⊗ L_{b t'})`. The
fibre of `b^* L` at `t'` is the base change of the fibre of `L` at `b t'` along
`κ(b t') ⟶ κ(t')`, and cohomology commutes with this field extension. -/
theorem embeddedFiberTwistDim_familyBaseChange [IsProper (i ≫ toSpec A ι)]
    (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) g)) (t' : T') (n : ℤ) (q : ℕ) :
    embeddedFiberTwistDim i (K := T'.residueField t') (T'.fromSpecResidueField t' ≫ s')
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) s' t')).obj
          ((Scheme.Modules.pullback (familyBaseChange (i ≫ toSpec A ι) g s' b hb)).obj L.val)) n q =
      embeddedFiberTwistDim i (K := T.residueField (b t')) (T.fromSpecResidueField (b t') ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g (b t'))).obj L.val) n q := by
  have : (pulledTwist (pullback.fst (i ≫ toSpec A ι) (T.fromSpecResidueField (b t') ≫ g) ≫ i) n
      ((Scheme.Modules.pullback
        (residueFieldBaseChange (i ≫ toSpec A ι) g (b t'))).obj L.val)).IsQuasicoherent :=
    Invertible.lineBundle_isQuasicoherent ⟨_, isLocallyRankOne_pulledTwist _ n
      (Invertible.pullback_locallyRankOne _ _ L.property)⟩
  rw [← embeddedFiberTwistDim_pullbackMap_of_eq i (K := T.residueField (b t'))
    (K' := T'.residueField t') _ (b.residueFieldMap t') _
    (specMap_residueFieldMap_comp_eq g s' b hb t') _ n q]
  exact embeddedFiberTwistDim_congr _ _
    ((familyBaseChangeFiberNatIso (i ≫ toSpec A ι) g s' b hb t').app L.val) n q

/-- **Base change of the family does not change the fibre Euler characteristics.** -/
theorem embeddedFiberTwistEulerChar_familyBaseChange [IsProper (i ≫ toSpec A ι)]
    (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) g)) (t' : T') (n : ℤ) :
    embeddedFiberTwistEulerChar i (K := T'.residueField t') (T'.fromSpecResidueField t' ≫ s')
        ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) s' t')).obj
          ((Scheme.Modules.pullback (familyBaseChange (i ≫ toSpec A ι) g s' b hb)).obj L.val)) n =
      embeddedFiberTwistEulerChar i (K := T.residueField (b t'))
        (T.fromSpecResidueField (b t') ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g (b t'))).obj L.val) n := by
  rw [embeddedFiberTwistEulerChar_eq, embeddedFiberTwistEulerChar_eq]
  congr 1
  funext q
  rw [embeddedFiberTwistDim_familyBaseChange i g s' b hb L t' n q]

/-- The base change of a twist is the twist of the base change. -/
def familyBaseChangePulledTwistIso (n : ℤ) (M : (pullback (i ≫ toSpec A ι) g).Modules) :
    (Scheme.Modules.pullback (familyBaseChange (i ≫ toSpec A ι) g s' b hb)).obj
        (pulledTwist (pullback.fst (i ≫ toSpec A ι) g ≫ i) n M) ≅
      pulledTwist (pullback.fst (i ≫ toSpec A ι) s' ≫ i) n
        ((Scheme.Modules.pullback (familyBaseChange (i ≫ toSpec A ι) g s' b hb)).obj M) :=
  pulledTwistPullbackIso _ _ _ (by simp [familyBaseChange]) n M

end BaseChange

/-- The pullback `L_t` of a line bundle is coherent. -/
theorem affineLocallyFiniteType_residueFieldBaseChange
    (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) g)) (t : T) :
    affineLocallyFiniteType _
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) :=
  affineLocallyFiniteType_of_isLocallyRankOne
    (Invertible.pullback_locallyRankOne _ _ L.property)

section Family

variable [IsProper (i ≫ toSpec A ι)] [Flat (i ≫ toSpec A ι)] [IsLocallyNoetherian T]
  (L : Invertible.LineBundle (pullback (i ≫ toSpec A ι) g))

/-- **Upper semicontinuity on the fibres of a family**: `t ↦ h^q(X_t, O(n) ⊗ L_t)`. -/
theorem upperSemicontinuous_embeddedFiberTwistDim (n : ℤ) (q : ℕ) :
    UpperSemicontinuous (fun t : T => embeddedFiberTwistDim i (K := T.residueField t)
      (T.fromSpecResidueField t ≫ g)
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q) := by
  have hrank := isLocallyRankOne_pulledTwist (pullback.fst (i ≫ toSpec A ι) g ≫ i) n L.property
  have := Invertible.lineBundle_isLocallyFree _ ⟨_, hrank⟩
  have h := upperSemicontinuous_modulePointFiberCohomologyDimension_of_proper
    (pullback.snd (i ≫ toSpec A ι) g) (pulledTwist (pullback.fst (i ≫ toSpec A ι) g ≫ i) n L.val)
    (affineLocallyFiniteType_of_isLocallyRankOne hrank)
    (Scheme.Modules.relativeFlat_of_isLocallyFree_of_flat _ _) q
  convert h using 1
  funext t
  exact (modulePointFiberCohomologyDimension_pulledTwist i g L.val n q t).symm

/-- **Local constancy on the fibres of a family**: `t ↦ χ(X_t, O(n) ⊗ L_t)`. -/
theorem isLocallyConstant_embeddedFiberTwistEulerChar (n : ℤ) :
    IsLocallyConstant (fun t : T => embeddedFiberTwistEulerChar i (K := T.residueField t)
      (T.fromSpecResidueField t ≫ g)
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n) := by
  have hrank := isLocallyRankOne_pulledTwist (pullback.fst (i ≫ toSpec A ι) g ≫ i) n L.property
  have := Invertible.lineBundle_isLocallyFree _ ⟨_, hrank⟩
  have h := isLocallyConstant_modulePointFiberEulerChar_of_proper
    (pullback.snd (i ≫ toSpec A ι) g) (pulledTwist (pullback.fst (i ≫ toSpec A ι) g ≫ i) n L.val)
    (affineLocallyFiniteType_of_isLocallyRankOne hrank)
    (Scheme.Modules.relativeFlat_of_isLocallyFree_of_flat _ _)
  convert h using 1
  funext t
  exact (modulePointFiberEulerChar_pulledTwist i g L.val n t).symm

/-- **The Euler-characteristic condition is open and closed**: for `c : ℤ → ℚ`, the set of
`t ∈ T` with `χ(X_t, O(n) ⊗ L_t) = c(n)` for every `n : ℤ` (Kleiman, arXiv:math/0504020v1,
(4.8.1), p. 28, for `c` a polynomial and `L` replaced by its dual). -/
theorem isClopen_setOf_embeddedFiberTwistEulerChar_eq (c : ℤ → ℚ) :
    IsClopen {t : T | ∀ n : ℤ, (embeddedFiberTwistEulerChar i (K := T.residueField t)
      (T.fromSpecResidueField t ≫ g)
      ((Scheme.Modules.pullback
        (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n : ℚ) = c n} := by
  have hloc := Scheme.isLocallyConstant_pi_of_isLocallyNoetherian
    (g := fun (n : ℤ) (t : T) => (embeddedFiberTwistEulerChar i (K := T.residueField t)
      (T.fromSpecResidueField t ≫ g)
      ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n : ℚ))
    (fun n => (isLocallyConstant_embeddedFiberTwistEulerChar i g L n).comp _)
  convert hloc.isClopen_fiber c using 1
  ext t
  simp only [Set.mem_ofPred_eq, funext_iff]

/-- **The vanishing condition is open** (Kleiman, arXiv:math/0504020v1, (4.8.3), p. 29): for a
closed immersion `i : X ⟶ P^N_A`, the set of `t ∈ T` with `h^q(X_t, O(n) ⊗ L_t) = 0` for all
`q ≥ 1` and `n ≥ m`. It is the finite intersection over `1 ≤ q ≤ N` and `m ≤ n < m + N` of the
open loci of upper semicontinuity. -/
theorem isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero [IsClosedImmersion i] (N : ℕ)
    (e : ι ≃ Fin (N + 1)) (m : ℤ) :
    IsOpen {t : T | ∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0} := by
  let D : T → ℤ → ℕ → ℕ := fun t n q => embeddedFiberTwistDim i (K := T.residueField t)
    (T.fromSpecResidueField t ≫ g)
    ((Scheme.Modules.pullback (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q
  have hset : {t : T | ∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n → D t n q = 0} =
      ⋂ q ∈ Finset.Icc 1 N, ⋂ n ∈ Finset.Ico m (m + N), {t : T | D t n q = 0} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Icc, Finset.mem_Ico]
    rw [embeddedFiberTwistDim_vanishing_iff i _ N e _
      (affineLocallyFiniteType_residueFieldBaseChange i g L t) m]
    constructor
    · intro h q hq n hn
      exact h q (by omega) hq.2 n hn.1 hn.2
    · intro h q hq hqN n hmn hn
      exact h q ⟨by omega, hqN⟩ n ⟨hmn, hn⟩
  change IsOpen {t : T | ∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n → D t n q = 0}
  rw [hset]
  refine isOpen_biInter_finset fun q _ => isOpen_biInter_finset fun n _ => ?_
  have h := (upperSemicontinuous_embeddedFiberTwistDim i g L n q).isOpen_preimage 1
  convert h using 1
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio, Nat.lt_one_iff, D]

/-- **The nonvanishing condition is open on the vanishing locus**: the set of `t` with
`h^q(X_t, O(n) ⊗ L_t) = 0` for `q ≥ 1`, `n ≥ m`, and `h^0(X_t, O(m) ⊗ L_t) ≠ 0`. On the vanishing
locus `h^0 = χ`, which is locally constant. -/
theorem isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_ne_zero [IsClosedImmersion i]
    (N : ℕ) (e : ι ≃ Fin (N + 1)) (m : ℤ) :
    IsOpen {t : T | (∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0) ∧
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m 0 ≠ 0} := by
  have hset : {t : T | (∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0) ∧
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m 0 ≠ 0} =
      {t : T | ∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
        embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
          ((Scheme.Modules.pullback
            (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0} ∩
      {t : T | embeddedFiberTwistEulerChar i (K := T.residueField t)
        (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m = 0}ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    refine and_congr_right fun hV => ?_
    rw [← embeddedFiberTwistDim_zero_eq_eulerChar i _ _ m (fun q hq => hV q hq m le_rfl)]
    exact_mod_cast Iff.rfl
  rw [hset]
  exact (isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero i g L N e m).inter
    ((isLocallyConstant_embeddedFiberTwistEulerChar i g L m).isClosed_fiber 0).isOpen_compl

/-- On the vanishing locus, the locus `h^0(X_t, O(m) ⊗ L_t) = 0` is open as well, so the
nonvanishing condition is open and closed in the vanishing locus. -/
theorem isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_eq_zero [IsClosedImmersion i]
    (N : ℕ) (e : ι ≃ Fin (N + 1)) (m : ℤ) :
    IsOpen {t : T | (∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0) ∧
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m 0 = 0} := by
  have hset : {t : T | (∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0) ∧
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m 0 = 0} =
      {t : T | ∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
        embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
          ((Scheme.Modules.pullback
            (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0} ∩
      {t : T | embeddedFiberTwistEulerChar i (K := T.residueField t)
        (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m = 0} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    refine and_congr_right fun hV => ?_
    rw [← embeddedFiberTwistDim_zero_eq_eulerChar i _ _ m (fun q hq => hV q hq m le_rfl)]
    exact_mod_cast Iff.rfl
  rw [hset]
  exact (isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero i g L N e m).inter
    ((isLocallyConstant_embeddedFiberTwistEulerChar i g L m).isOpen_fiber 0)

/-- **Refinement by the number of sections** (ST3): for every `r`, the set of `t` with
`h^q(X_t, O(n) ⊗ L_t) = 0` for `q ≥ 1`, `n ≥ m`, and `h^0(X_t, O(m) ⊗ L_t) = r` is open; these
sets, for varying `r`, are open and closed in the vanishing locus. -/
theorem isOpen_setOf_vanishing_and_embeddedFiberTwistDim_zero_eq [IsClosedImmersion i]
    (N : ℕ) (e : ι ≃ Fin (N + 1)) (m : ℤ) (r : ℕ) :
    IsOpen {t : T | (∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0) ∧
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m 0 = r} := by
  have hset : {t : T | (∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0) ∧
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m 0 = r} =
      {t : T | ∀ q : ℕ, 0 < q → ∀ n : ℤ, m ≤ n →
        embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
          ((Scheme.Modules.pullback
            (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) n q = 0} ∩
      {t : T | embeddedFiberTwistEulerChar i (K := T.residueField t)
        (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ toSpec A ι) g t)).obj L.val) m = r} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    refine and_congr_right fun hV => ?_
    rw [← embeddedFiberTwistDim_zero_eq_eulerChar i _ _ m (fun q hq => hV q hq m le_rfl)]
    exact_mod_cast Iff.rfl
  rw [hset]
  exact (isOpen_setOf_forall_embeddedFiberTwistDim_eq_zero i g L N e m).inter
    ((isLocallyConstant_embeddedFiberTwistEulerChar i g L m).isOpen_fiber (r : ℤ))

end Family

end Scheme.Cohomology

end AlgebraicGeometry

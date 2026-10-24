/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Fibers.FieldPoint
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# Twisted cohomology on the fibres of a projective embedding

Let `i : X ⟶ P^N_A = ProjectiveSpace A ι` be a morphism and `f = i ≫ toSpec A ι`. For a field
point `k : Spec K ⟶ Spec A` write `X_K = X ×_{Spec A} Spec K` (`pullback f k`) and
`O_{X_K}(n)` for the pullback of the twisting sheaf `O(n)` along `X_K ⟶ X ⟶ P^N_A`. This file
defines the dimensions `h^q(X_K, O(n) ⊗ M) = embeddedFiberTwistDim i k M n q` and the Euler
characteristic `χ(X_K, O(n) ⊗ M) = embeddedFiberTwistEulerChar i k M n`, with the structural
`K`-action through `X_K ⟶ Spec K` (`moduleCohomologyDimension`, `moduleEulerChar` of
`Cohomology/Fibers/FieldPoint`), and compares them with the point-fibre invariants of a family:

* `pulledTwist h n M = h^* O(n) ⊗ M` for `h : Y ⟶ P^N_A`; twisting commutes with pullback
  (`pulledTwistPullbackIso`).
* For `g : T ⟶ Spec A` and a module `M` on `X_T = X ×_{Spec A} T`, the point-fibre dimension
  of `O(n) ⊗ M` at `t ∈ T` (`modulePointFiberCohomologyDimension`) equals
  `h^q(X_{κ(t)}, O(n) ⊗ M_t)` for `M_t` the pullback of `M` along
  `residueFieldBaseChange : X_{κ(t)} ⟶ X_T` (`modulePointFiberCohomologyDimension_pulledTwist`),
  and similarly for the Euler characteristic (`modulePointFiberEulerChar_pulledTwist`).
* Field extension `K ⟶ K'` leaves `h^q(X_K, O(n) ⊗ M)` unchanged for quasicoherent twists
  (`embeddedFiberTwistDim_fieldBaseChange`).

These are the fibre invariants in the definition of the strata of the Picard functor
(Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, (4.8.1) on p. 28 and
(4.8.3) on p. 29), where Kleiman notes that they commute with field extension by flat base
change (p. 28, citing Hartshorne, Prop. III.9.3). No Noetherian, flatness or properness
hypothesis enters the definitions or the transports; field extension uses quasi-compactness and
quasi-separatedness of `f` (hence of `X_K ⟶ Spec K`) and quasicoherence of the twist.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

section Twist

variable {A : Type u} [CommRing A] {ι : Type u}

/-- The pullback `h^* O(n)` of the twisting sheaf along `h : Y ⟶ P^N_A`. -/
abbrev pulledTwistingSheaf {Y : Scheme.{u}} (h : Y ⟶ ProjectiveSpace A ι) (n : ℤ) : Y.Modules :=
  (Scheme.Modules.pullback h).obj (ProjectiveSpace.twistingSheaf A ι n)

theorem isLocallyRankOne_pulledTwistingSheaf {Y : Scheme.{u}} (h : Y ⟶ ProjectiveSpace A ι)
    (n : ℤ) : Invertible.IsLocallyRankOne Y (pulledTwistingSheaf h n) :=
  Invertible.pullback_locallyRankOne h _ (ProjectiveSpace.isLocallyRankOne_twistingSheaf A ι n)

/-- The twist `h^* O(n) ⊗ M` of a module `M` on `Y` along `h : Y ⟶ P^N_A`. -/
abbrev pulledTwist {Y : Scheme.{u}} (h : Y ⟶ ProjectiveSpace A ι) (n : ℤ) (M : Y.Modules) :
    Y.Modules :=
  (moduleTensorLeftFunctor Y (pulledTwistingSheaf h n)).obj M

/-- **Twisting commutes with pullback**: `u^*(h^* O(n) ⊗ M) ≅ h'^* O(n) ⊗ u^* M` for
`u ≫ h = h'`. The first map is the canonical tensor comparison, invertible because `h^* O(n)`
is locally of rank one; the second is the pullback composition on the twisting factor. -/
def pulledTwistPullbackIso {Y Y' : Scheme.{u}} (u : Y' ⟶ Y) (h : Y ⟶ ProjectiveSpace A ι)
    (h' : Y' ⟶ ProjectiveSpace A ι) (w : u ≫ h = h') (n : ℤ) (M : Y.Modules) :
    (Scheme.Modules.pullback u).obj (pulledTwist h n M) ≅
      pulledTwist h' n ((Scheme.Modules.pullback u).obj M) :=
  haveI := Invertible.PullbackTensor.Local.pullbackTensorMap_isIso u (pulledTwistingSheaf h n) M
    (isLocallyRankOne_pulledTwistingSheaf h n)
  asIso (pullbackTensorMap u (pulledTwistingSheaf h n) M) ≪≫
    (moduleTensorRightFunctor Y' ((Scheme.Modules.pullback u).obj M)).mapIso
      ((Scheme.Modules.pullbackComp u h).app _ ≪≫ (Scheme.Modules.pullbackCongr w).app _)

/-- Twists of isomorphic modules are isomorphic. -/
def pulledTwistCongr {Y : Scheme.{u}} (h : Y ⟶ ProjectiveSpace A ι) (n : ℤ) {M N : Y.Modules}
    (e : M ≅ N) : pulledTwist h n M ≅ pulledTwist h n N :=
  (moduleTensorLeftFunctor Y (pulledTwistingSheaf h n)).mapIso e

end Twist

section EmbeddedFiber

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι)

/-- `h^q(X_K, O(n) ⊗ M)` for a field point `k : Spec K ⟶ Spec A`, on
`X_K = X ×_{Spec A} Spec K` with `f = i ≫ toSpec A ι`, where `O(n)` is pulled back along
`X_K ⟶ X ⟶ P^N_A` and `K` acts through `X_K ⟶ Spec K`. -/
def embeddedFiberTwistDim {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of A))
    (M : (pullback (i ≫ ProjectiveSpace.toSpec A ι) k).Modules) (n : ℤ) (q : ℕ) : ℕ :=
  moduleCohomologyDimension (pullback.snd (i ≫ ProjectiveSpace.toSpec A ι) k)
    (pulledTwist (pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) k ≫ i) n M) q

/-- `χ(X_K, O(n) ⊗ M)` for a field point `k : Spec K ⟶ Spec A`. -/
def embeddedFiberTwistEulerChar {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of A))
    (M : (pullback (i ≫ ProjectiveSpace.toSpec A ι) k).Modules) (n : ℤ) : ℤ :=
  moduleEulerChar (pullback.snd (i ≫ ProjectiveSpace.toSpec A ι) k)
    (pulledTwist (pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) k ≫ i) n M)

/-- The Euler characteristic is the alternating sum of the dimensions. -/
theorem embeddedFiberTwistEulerChar_eq {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of A))
    (M : (pullback (i ≫ ProjectiveSpace.toSpec A ι) k).Modules) (n : ℤ) :
    embeddedFiberTwistEulerChar i k M n =
      ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (embeddedFiberTwistDim i k M n q : ℤ) :=
  rfl

/-- Isomorphic modules have the same twisted fibre dimensions. -/
theorem embeddedFiberTwistDim_congr {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of A))
    {M N : (pullback (i ≫ ProjectiveSpace.toSpec A ι) k).Modules} (e : M ≅ N) (n : ℤ) (q : ℕ) :
    embeddedFiberTwistDim i k M n q = embeddedFiberTwistDim i k N n q :=
  moduleCohomologyDimension_congr _ (pulledTwistCongr _ n e) q

/-- Isomorphic modules have the same twisted fibre Euler characteristics. -/
theorem embeddedFiberTwistEulerChar_congr {K : Type u} [Field K]
    (k : Spec (.of K) ⟶ Spec (.of A))
    {M N : (pullback (i ≫ ProjectiveSpace.toSpec A ι) k).Modules} (e : M ≅ N) (n : ℤ) :
    embeddedFiberTwistEulerChar i k M n = embeddedFiberTwistEulerChar i k N n :=
  moduleEulerChar_congr _ (pulledTwistCongr _ n e)

variable {T : Scheme.{u}} (g : T ⟶ Spec (.of A))

/-- **Point fibres of a family.** For a module `M` on `X_T = X ×_{Spec A} T`, the point-fibre
dimension of the twist `O(n) ⊗ M` at `t ∈ T` is `h^q(X_{κ(t)}, O(n) ⊗ M_t)` for the pullback
`M_t` of `M` to `X_{κ(t)}`. -/
theorem modulePointFiberCohomologyDimension_pulledTwist
    (M : (pullback (i ≫ ProjectiveSpace.toSpec A ι) g).Modules) (n : ℤ) (q : ℕ) (t : T) :
    modulePointFiberCohomologyDimension (pullback.snd (i ≫ ProjectiveSpace.toSpec A ι) g)
        (pulledTwist (pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) g ≫ i) n M) q t =
      embeddedFiberTwistDim i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ ProjectiveSpace.toSpec A ι) g t)).obj M) n q := by
  rw [modulePointFiberCohomologyDimension_eq_pullbackMap]
  exact moduleCohomologyDimension_congr _
    (pulledTwistPullbackIso _ _ _
      (residueFieldBaseChange_fst_assoc (i ≫ ProjectiveSpace.toSpec A ι) g t i) n M) q

/-- The point-fibre Euler characteristic of `O(n) ⊗ M` at `t ∈ T` is `χ(X_{κ(t)}, O(n) ⊗ M_t)`. -/
theorem modulePointFiberEulerChar_pulledTwist
    (M : (pullback (i ≫ ProjectiveSpace.toSpec A ι) g).Modules) (n : ℤ) (t : T) :
    modulePointFiberEulerChar (pullback.snd (i ≫ ProjectiveSpace.toSpec A ι) g)
        (pulledTwist (pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) g ≫ i) n M) t =
      embeddedFiberTwistEulerChar i (K := T.residueField t) (T.fromSpecResidueField t ≫ g)
        ((Scheme.Modules.pullback
          (residueFieldBaseChange (i ≫ ProjectiveSpace.toSpec A ι) g t)).obj M) n := by
  unfold modulePointFiberEulerChar
  rw [embeddedFiberTwistEulerChar_eq]
  congr 1
  funext q
  rw [modulePointFiberCohomologyDimension_pulledTwist]

end EmbeddedFiber

section FieldExtension

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι)

/-- The base-change map `X_{K'} ⟶ X_K` of a field map `σ : K →+* K'`. -/
abbrev fieldExtensionBaseChange {K K' : Type u} [Field K] [Field K']
    (k : Spec (.of K) ⟶ Spec (.of A)) (σ : K →+* K') :
    pullback (i ≫ ProjectiveSpace.toSpec A ι) (Spec.map (CommRingCat.ofHom σ) ≫ k) ⟶
      pullback (i ≫ ProjectiveSpace.toSpec A ι) k :=
  pullback.map (i ≫ ProjectiveSpace.toSpec A ι) (Spec.map (CommRingCat.ofHom σ) ≫ k)
    (i ≫ ProjectiveSpace.toSpec A ι) k (𝟙 X) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem fieldExtensionBaseChange_fst {K K' : Type u} [Field K] [Field K']
    (k : Spec (.of K) ⟶ Spec (.of A)) (σ : K →+* K') :
    fieldExtensionBaseChange i k σ ≫ pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) k =
      pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) (Spec.map (CommRingCat.ofHom σ) ≫ k) := by
  simp [fieldExtensionBaseChange]

/-- **Twisted fibre dimensions are unchanged by field extension**, for a quasicoherent twist
and a quasi-compact quasi-separated `f = i ≫ toSpec A ι` (Kleiman, arXiv:math/0504020v1, p. 28:
cohomology commutes with flat base change). -/
theorem embeddedFiberTwistDim_fieldBaseChange [QuasiCompact (i ≫ ProjectiveSpace.toSpec A ι)]
    [QuasiSeparated (i ≫ ProjectiveSpace.toSpec A ι)] {K K' : Type u} [Field K] [Field K']
    (k : Spec (.of K) ⟶ Spec (.of A)) (σ : K →+* K')
    (M : (pullback (i ≫ ProjectiveSpace.toSpec A ι) k).Modules) (n : ℤ)
    [(pulledTwist (pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) k ≫ i) n M).IsQuasicoherent]
    (q : ℕ) :
    embeddedFiberTwistDim i (Spec.map (CommRingCat.ofHom σ) ≫ k)
        ((Scheme.Modules.pullback (fieldExtensionBaseChange i k σ)).obj M) n q =
      embeddedFiberTwistDim i k M n q := by
  unfold embeddedFiberTwistDim
  rw [← moduleCohomologyDimension_fieldBaseChange
    (pullback.snd (i ≫ ProjectiveSpace.toSpec A ι) k) σ,
    moduleCohomologyDimension_pullback_snd_pullback_snd]
  exact (moduleCohomologyDimension_congr _
    (pulledTwistPullbackIso _ _ _ (fieldExtensionBaseChange_fst_assoc i k σ i) n M) q).symm

end FieldExtension

end AlgebraicGeometry.Scheme.Cohomology

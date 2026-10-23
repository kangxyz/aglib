/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.Fiber
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.LocalOnTarget
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Tensor
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.AffineOpen
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.Tensor
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.CategoryTheory.Abelian.KernelCompEpi
public import Aglib.AlgebraicGeometry.IdealSheaf.FiniteType

/-!
# The direct image of the twisted ideal sheaf of a Hilbert family

Let `T` be locally Noetherian over `Spec A`, `Z` a point of `Hilb^Φ(T)` and
`π : X_T = P^n_A ×_{Spec A} T ⟶ T`. For a natural `r ≥ hilbertRegularityBound n Φ`, following
Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, pp. 25–26:

* `affineLocallyFiniteType_familyIdealTwist`: `I_Z(r)` is coherent;
* `IsHilbertFamily.relativeFlat_idealModule` and `IsHilbertFamily.relativeFlat_familyIdealTwist`
  (both for any `T`): `I_Z` and `I_Z(r)` are flat over `T`. Over an affine open `Spec B ⊆ T` the
  pullback of `I_Z` to `P^n_B` is `I_{Z_B}` (`pointMapIdealPullbackIso`), on affine opens the
  kernel of a surjection of flat `B`-modules (`relativeFlat_idealModule_of_flat`); flatness is
  local on the target (`relativeFlat_of_forall_isPullback`). Then `I_Z(r) = 𝒪(r) ⊗ I_Z` is flat
  because `𝒪(r)` is locally trivial (`relativeFlat_tensor_of_locallyTrivial`);
* `IsHilbertFamily.sheafHasRank_pushforward_familyIdealTwist`,
  `IsHilbertFamily.isFiniteLocallyFree_pushforward_familyIdealTwist`: `π_* I_Z(r)` is finite locally
  free of rank `(n + r).choose r - ⌊Φ(r)⌋₊`;
* `IsHilbertFamily.isIso_moduleBaseChangeMap_familyIdealTwist`: `π_* I_Z(r)` commutes with base
  change along every `T' ⟶ T`: the base-change map `f^* π_* I_Z(r) ⟶ π'_* (I_Z(r)|_{X_T ×_T T'})`
  is an isomorphism.

The last three apply `Cohomology/BaseChange/NoetherianPushforward` to the fiber concentration
`IsHilbertFamily.fibreCohomologyConcentrated_familyIdealTwist`. Finally
`familyTwistedShortComplex_shortExact` and `isLimitPushforwardFamilyTwistedKernelFork` say that
`0 → I_Z(r) → 𝒪(r) ⊗ 𝒪 → 𝒪_Z(r) → 0` is short exact and that `π_* I_Z(r)` is the kernel of
`π_*(𝒪(r) ⊗ 𝒪) ⟶ π_* 𝒪_Z(r)`, since `π_*` is a right adjoint.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Cohomology Scheme.Modules.QuasiCoherent

variable (ι : Type u) {A : Type u} [CommRing A] {Φ : ℚ[X]} {T : Scheme.{u}}
  {g : T ⟶ Spec (CommRingCat.of A)}

section Coherence

variable (n : ℕ) (e : ι ≃ Fin (n + 1)) (Z : (pullback (toSpec A ι) g).IdealSheafData)

include e in
/-- `I_Z(r)` is coherent on `X_T` for locally Noetherian `T`: `𝒪(r)` is finite locally free and
`X_T` is locally Noetherian. -/
theorem affineLocallyFiniteType_familyIdealTwist [IsLocallyNoetherian T] (r : ℤ) :
    affineLocallyFiniteType (pullback (toSpec A ι) g) (familyIdealTwist ι g Z r) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact affineLocallyFiniteType_tensor _ _
    (affineLocallyFiniteType_of_finitePresentation (familyTwistingSheaf ι g r))
    (Scheme.Hom.affineLocallyFiniteType_idealModule Z.subschemeι)

/-- `0 → I_Z(r) → 𝒪(r) ⊗ 𝒪 → 𝒪_Z(r) → 0` is short exact on `X_T`: twisting by the finite
locally free `𝒪(r)` is exact. -/
theorem familyTwistedShortComplex_shortExact (r : ℤ) :
    (familyTwistedShortComplex ι g Z r).ShortExact :=
  Scheme.Modules.tensor_shortExact_finiteLocallyFree (familyTwistingSheaf ι g r) Z.shortComplex
    Z.shortComplex_shortExact

/-- **`π_* I_Z(r)` is the kernel of `π_*(𝒪(r) ⊗ 𝒪) ⟶ π_* 𝒪_Z(r)`**: the image under the right
adjoint `π_*` of the kernel fork of the twisted sequence is a limit. -/
def isLimitPushforwardFamilyTwistedKernelFork (r : ℤ) :
    IsLimit ((KernelFork.ofι _ (familyTwistedShortComplex ι g Z r).zero).map
      (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g))) :=
  haveI : PreservesLimitsOfSize.{0, 0}
      (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.snd (toSpec A ι) g)).rightAdjoint_preservesLimits
  KernelFork.mapIsLimit _ (familyTwistedShortComplex_shortExact ι Z r).fIsKernel _

/-- **Comparison with a kernel over an epimorphism onto `π_*(𝒪(r) ⊗ 𝒪)`**: for an epimorphism
`μ : F ⟶ π_*(𝒪(r) ⊗ 𝒪)` (for instance from the monomials of degree `r`) and a kernel
`ιK : K ⟶ F` of `μ ≫ π_*(𝒪(r) ⊗ 𝒪 ⟶ 𝒪_Z(r))`, every `k : K ⟶ π_* I_Z(r)` compatible with `μ` is
an epimorphism (`Abelian.epi_of_isKernel_comp`). -/
theorem epi_of_isKernel_pushforward_familyTwistedShortComplex (r : ℤ) {F K : T.Modules}
    (μ : F ⟶ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
      (familyTwistedShortComplex ι g Z r).X₂) [Epi μ] {ιK : K ⟶ F}
    {wK : ιK ≫ μ ≫ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).map
      (familyTwistedShortComplex ι g Z r).g = 0}
    (hK : IsLimit (KernelFork.ofι ιK wK))
    (k : K ⟶ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
      (familyIdealTwist ι g Z r))
    (hk : k ≫ (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).map
      (familyTwistedShortComplex ι g Z r).f = ιK ≫ μ) :
    Epi k :=
  Abelian.epi_of_isKernel_comp
    (wi := (KernelFork.ofι _ (familyTwistedShortComplex ι g Z r).zero).map_condition _)
    (isLimitPushforwardFamilyTwistedKernelFork ι Z r) μ hK k hk

end Coherence

variable {Z : (pullback (toSpec A ι) g).IdealSheafData} (n : ℕ) (e : ι ≃ Fin (n + 1))

/-- **`I_Z` is flat over `T`** for a point `Z` of `Hilb^Φ(T)`, `T` any scheme over `Spec A`: over
an affine open `Spec B ⊆ T` its pullback to `P^n_B` is the ideal module of the flat family `Z_B`
(`pointMapIdealPullbackIso`), the kernel of a surjection of flat `B`-modules on affine opens
(`relativeFlat_idealModule_of_flat`). -/
theorem IsHilbertFamily.relativeFlat_idealModule (hZ : IsHilbertFamily ι Φ g Z) :
    Scheme.Modules.relativeFlat (pullback.snd (toSpec A ι) g)
      (Scheme.Hom.idealModule Z.subschemeι) := by
  have := hZ.flat
  refine Scheme.Modules.relativeFlat_of_forall_isPullback _ _ fun t => ?_
  obtain ⟨U, hU, htU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show t ∈ (⊤ : T.Opens) from trivial)
  have hfl := hZ.flat_comap_pointMap ι (B := Γ(T, U)) hU.fromSpec
  have := (Z.comap (pointMap ι g (K := Γ(T, U)) hU.fromSpec)).idealModule_isQuasicoherent
  refine ⟨_, hU.fromSpec, inferInstance, by rwa [hU.range_fromSpec], _,
    pointMap ι g (K := Γ(T, U)) hU.fromSpec, toSpec Γ(T, U) ι,
    isPullback_pointMap ι g (K := Γ(T, U)) hU.fromSpec, ?_⟩
  exact Scheme.Modules.relativeFlat_of_iso _
    (pointMapIdealPullbackIso ι Z (B := Γ(T, U)) hU.fromSpec)
    (Scheme.Modules.relativeFlat_idealModule_of_flat (toSpec Γ(T, U) ι) _)

/-- **`I_Z(r)` is flat over `T`** for a point `Z` of `Hilb^Φ(T)`, `T` any scheme over `Spec A`:
`I_Z` is flat over `T` (`IsHilbertFamily.relativeFlat_idealModule`) and `𝒪(r)` is locally trivial
(`relativeFlat_tensor_of_locallyTrivial`). -/
theorem IsHilbertFamily.relativeFlat_familyIdealTwist (hZ : IsHilbertFamily ι Φ g Z) (r : ℤ) :
    Scheme.Modules.relativeFlat (pullback.snd (toSpec A ι) g) (familyIdealTwist ι g Z r) :=
  Scheme.Modules.relativeFlat_tensor_of_locallyTrivial _ _ _
    ((Scheme.Modules.Invertible.isLocallyRankOne_iff_restrict_unit _).mp
      (isLocallyRankOne_familyTwistingSheaf ι g r))
    (hZ.relativeFlat_idealModule ι)

include e in
/-- **The direct image `π_* I_Z(r)` has rank `(n + r).choose r - ⌊Φ(r)⌋₊`** (Nitsure,
arXiv:math/0504590v1, §5, p. 25, (*)), with local bases of that size: for a point `Z` of
`Hilb^Φ(T)`, `T` locally Noetherian, and a natural `r ≥ hilbertRegularityBound n Φ`. -/
theorem IsHilbertFamily.sheafHasRank_pushforward_familyIdealTwist [IsLocallyNoetherian T]
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Scheme.Modules.SheafHasRank
      ((Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj (familyIdealTwist ι g Z r))
      ((n + r).choose r - ⌊Φ.eval (r : ℚ)⌋₊) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact Scheme.Modules.pushforward_hasRank_of_geometric_concentration _ _
    (affineLocallyFiniteType_familyIdealTwist ι n e Z r) (hZ.relativeFlat_familyIdealTwist ι r)
    _ (hZ.fibreCohomologyConcentrated_familyIdealTwist ι n e r hr)

include e in
/-- **The direct image `π_* I_Z(r)` is finite locally free** for a point `Z` of `Hilb^Φ(T)`, `T`
locally Noetherian, and a natural `r ≥ hilbertRegularityBound n Φ`. -/
theorem IsHilbertFamily.isFiniteLocallyFree_pushforward_familyIdealTwist [IsLocallyNoetherian T]
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    Scheme.Modules.IsFiniteLocallyFree T
      ((Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj
        (familyIdealTwist ι g Z r)) :=
  (hZ.sheafHasRank_pushforward_familyIdealTwist ι n e r hr).isFiniteLocallyFree

include e in
/-- **The direct image `π_* I_Z(r)` commutes with base change** (Nitsure, arXiv:math/0504590v1,
§5, p. 25, from (*) via Theorem 3.7): for a point `Z` of `Hilb^Φ(T)`, `T` locally Noetherian, a
natural `r ≥ hilbertRegularityBound n Φ` and every morphism `f : T' ⟶ T`, the base-change map
`f^* π_* I_Z(r) ⟶ π'_* (I_Z(r)|_{X_T ×_T T'})` is an isomorphism. -/
theorem IsHilbertFamily.isIso_moduleBaseChangeMap_familyIdealTwist [IsLocallyNoetherian T]
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r)
    {T' : Scheme.{u}} (f : T' ⟶ T) :
    IsIso (Scheme.Modules.moduleBaseChangeMap (pullback.snd (toSpec A ι) g) f
      (familyIdealTwist ι g Z r)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  exact Scheme.Modules.moduleBaseChangeMap_isIso_of_geometric_concentration _ _
    (affineLocallyFiniteType_familyIdealTwist ι n e Z r) (hZ.relativeFlat_familyIdealTwist ι r)
    _ (hZ.fibreCohomologyConcentrated_familyIdealTwist ι n e r hr) f

end AlgebraicGeometry.ProjectiveSpace

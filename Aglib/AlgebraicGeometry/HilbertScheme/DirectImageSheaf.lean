/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.QuotientDirectImage
public import Aglib.AlgebraicGeometry.HilbertScheme.FieldCohomology
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.FamilyTwist
public import Aglib.AlgebraicGeometry.HilbertScheme.Functor
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.TwistedRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Affine
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.Tensor
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Tensor
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.AffineOpen

/-!
# The direct image of the twisted structure module of a Hilbert family

Let `T` be a scheme over `Spec A`, `π : P^n_A ×_{Spec A} T ⟶ T` the second projection and
`Z ⊆ P^n_A ×_{Spec A} T` a closed subscheme. On `P^n_A ×_{Spec A} T` the twisting sheaf
`𝒪(r)` is the pullback of `𝒪(r)` on `P^n_A` along the first projection (`familyTwistingSheaf`,
`ProjectiveSpace/BaseChange/FamilyTwist`), and the twisted structure module is
`𝒪_Z(r) = 𝒪(r) ⊗ 𝒪_Z` (`familyQuotientTwist`). This file proves,
for a point `Z` of `Hilb^Φ(T)` (`IsHilbertFamily`), `ι ≃ Fin (n + 1)` and a natural number
`r ≥ hilbertRegularityBound n Φ`, the local freeness part of the input (*) of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 25, for `𝒪_Z(r)` over a
locally Noetherian `T`, and the base change of `π_* 𝒪_Z(r)`, which Nitsure derives on p. 25 by
Theorem 3.7:

* `IsHilbertFamily.fibreCohomologyConcentrated`: on every geometric fiber of `π`, `𝒪_Z(r)` has
  no higher cohomology and an `H^0` of dimension `Φ(r)`;
* `IsHilbertFamily.sheafHasRank_directImageSheaf`: `π_* 𝒪_Z(r)` is finite locally free of
  constant rank `⌊Φ(r)⌋₊`;
* `IsHilbertFamily.isIso_moduleBaseChangeMap_directImageSheaf`: the formation of `π_* 𝒪_Z(r)`
  commutes with every base change `T' ⟶ T`.

The fiber of `𝒪_Z(r)` over a point `x : Spec K ⟶ T`, through `pointMap ι g x : P^n_K ⟶ P_T`, is
`𝒪_{Z_x}(r)` on `P^n_K` (`familyQuotientTwistPointIso`): the pullback tensor comparison is
invertible, `𝒪(r)` pulls back to `𝒪(r)` (`twistingPullbackIso`), and `𝒪_Z` to `𝒪_{Z_x}`
(`quotientModulePullbackIso`); together, `IdealSheafData.pullbackTensorQuotientIso`. Over a
field the fiber `Z_x` has Hilbert polynomial `Φ`, so its ideal is `m`-regular and
`H^0(𝒪_{Z_x}(r))` has dimension `Φ(r)` (`projectiveCohomologyDim_quotientTwist_zero_cast`,
`HilbertScheme/FieldCohomology`). The
direct-image statements are `pushforward_hasRank_of_geometric_concentration` and
`moduleBaseChangeMap_isIso_of_geometric_concentration`
(`Cohomology/BaseChange/NoetherianPushforward`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

open Scheme.Cohomology

section Definitions

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

/-- The twisted structure module `𝒪_Z(r) = 𝒪(r) ⊗ 𝒪_Z` of a closed subscheme
`Z ⊆ P^n_A ×_{Spec A} T`. -/
abbrev familyQuotientTwist (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) :
    (pullback (toSpec A ι) g).Modules :=
  familyTwistingSheaf ι g r ⊗ Z.quotientModule

/-- The direct image `π_* 𝒪_Z(r)` on `T`, for the projection `π : P^n_A ×_{Spec A} T ⟶ T`. -/
abbrev directImageSheaf (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) : T.Modules :=
  (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g)).obj (familyQuotientTwist ι g Z r)

/-- `𝒪_Z(r)` is coherent on `P^n_A ×_{Spec A} T` for locally Noetherian `T`. -/
theorem affineLocallyFiniteType_familyQuotientTwist [Finite ι] [IsLocallyNoetherian T]
    (Z : (pullback (toSpec A ι) g).IdealSheafData) (r : ℤ) :
    affineLocallyFiniteType (pullback (toSpec A ι) g) (familyQuotientTwist ι g Z r) :=
  affineLocallyFiniteType_tensor _ _ (affineLocallyFiniteType_of_finitePresentation _)
    Z.affineLocallyFiniteType_quotientModule

/-- `𝒪_Z(r)` is relatively flat over `T` when `Z` is flat over `T`. -/
theorem relativeFlat_familyQuotientTwist (Z : (pullback (toSpec A ι) g).IdealSheafData)
    [Flat (Z.subschemeι ≫ pullback.snd (toSpec A ι) g)] (r : ℤ) :
    relativeFlat (pullback.snd (toSpec A ι) g) (familyQuotientTwist ι g Z r) :=
  relativeFlat_tensor_of_locallyTrivial _ _ _
    ((Invertible.isLocallyRankOne_iff_restrict_unit _).mp
      (isLocallyRankOne_familyTwistingSheaf ι g r))
    (Z.relativeFlat_quotientModule_of_flat _)

/-- **The twisted structure module over a point**: for `x : Spec K ⟶ T`, the pullback of
`𝒪_Z(r)` along `pointMap ι g x : P^n_K ⟶ P^n_A ×_{Spec A} T` is `𝒪_{Z_x}(r)` on `P^n_K`, for
`Z_x = Z.comap (pointMap ι g x)`. No flatness is needed. -/
def familyQuotientTwistPointIso (Z : (pullback (toSpec A ι) g).IdealSheafData)
    {K : Type u} [CommRing K] (x : Spec (CommRingCat.of K) ⟶ T) (r : ℤ) :
    (Scheme.Modules.pullback (pointMap ι g x)).obj (familyQuotientTwist ι g Z r) ≅
      twistingSheaf K ι r ⊗ (Z.comap (pointMap ι g x)).quotientModule :=
  Z.pullbackTensorQuotientIso (pointMap ι g x) (pointMapTwistingPullbackIso ι g x r)

end Definitions

/-- `𝒪_W(r)` in its two presentations: the monoidal tensor product `𝒪(r) ⊗ 𝒪_W` and
`quotientTwist`. The conversion is checked once here, at variable data. -/
def quotientTwistIso (ι : Type u) {K : Type u} [CommRing K]
    (W : (ProjectiveSpace K ι).IdealSheafData) (r : ℤ) :
    twistingSheaf K ι r ⊗ W.quotientModule ≅ quotientTwist ι W r :=
  Iso.refl _


section Concentration

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
  {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of A)}
  {Z : (pullback (toSpec A ι) g).IdealSheafData}

include e in
/-- **Geometric fibers of `𝒪_Z(r)`** (Nitsure, arXiv:math/0504590v1, §5, p. 25): for a point `Z`
of `Hilb^Φ(T)` and a natural number `r ≥ hilbertRegularityBound n Φ`, on every geometric fiber of
`π : P^n_A ×_{Spec A} T ⟶ T` the module `𝒪_Z(r)` has an `H^0` of dimension `Φ(r)` and no higher
cohomology. The fiber over `t : Spec K ⟶ T` is `P^n_K` through `isPullback_pointMap`, with
coefficient `𝒪_{Z_t}(r)` (`familyQuotientTwistPointIso`). -/
theorem IsHilbertFamily.fibreCohomologyConcentrated (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    FibreCohomologyConcentrated (pullback.snd (toSpec A ι) g) (familyQuotientTwist ι g Z r)
      ⌊Φ.eval (r : ℚ)⌋₊ := by
  intro K _ _ t
  have hsq := isPullback_pointMap ι g t
  let E := hsq.isoPullback
  let M := familyQuotientTwist ι g Z r
  let W := Z.comap (pointMap ι g t)
  have hW : subschemeHilbertPolynomial ι K W = Φ := hZ.subschemeHilbertPolynomial_fiber K t
  let C : (Scheme.Modules.pullback E.hom).obj
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) g) t)).obj M) ≅
      quotientTwist ι W r :=
    (Scheme.Modules.pullbackComp E.hom (pullback.fst (pullback.snd (toSpec A ι) g) t)).app M ≪≫
      (Scheme.Modules.pullbackCongr hsq.isoPullback_hom_fst).app M ≪≫
        familyQuotientTwistPointIso ι g Z t r ≪≫ quotientTwistIso ι W r
  refine ⟨?_, fun q hq => ?_⟩
  · have h := finrank_moduleCohomology_eq_of_isIso E.hom
      (pullback.snd (pullback.snd (toSpec A ι) g) t) (toSpec K ι) hsq.isoPullback_hom_snd _ C 0
    have hdim := projectiveCohomologyDim_quotientTwist_zero_cast ι n e W hW r hr
    refine h.trans ?_
    change projectiveCohomologyDim K ι (quotientTwist ι W r) 0 = _
    rw [← hdim, Nat.floor_natCast]
  · have hv := subsingleton_moduleCohomology_quotientTwist_of_field ι n e K W hW r hr q
      (Nat.pos_iff_ne_zero.mp hq)
    have : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _ ((Scheme.Modules.pullback E.hom).obj
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) g) t)).obj M))) q) :=
      moduleCohomology_subsingleton_of_iso C.symm q hv
    exact (moduleCohomologyPullback_bijective E.hom _ q).injective.subsingleton

end Concentration

section DirectImage

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
  {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
  {Z : (pullback (toSpec A ι) g).IdealSheafData}

include e in
/-- **The direct image `π_* 𝒪_Z(r)` is finite locally free of rank `Φ(r)`** (Nitsure,
arXiv:math/0504590v1, §5, p. 25, (*)): for a locally Noetherian `T`, a point `Z` of `Hilb^Φ(T)`
and a natural number `r ≥ hilbertRegularityBound n Φ`. -/
theorem IsHilbertFamily.sheafHasRank_directImageSheaf (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    SheafHasRank (directImageSheaf ι g Z r) ⌊Φ.eval (r : ℚ)⌋₊ :=
  have : Finite ι := Finite.of_equiv _ e.symm
  have := hZ.flat
  pushforward_hasRank_of_geometric_concentration _ _
    (affineLocallyFiniteType_familyQuotientTwist ι g Z r)
    (relativeFlat_familyQuotientTwist ι g Z r) _ (hZ.fibreCohomologyConcentrated ι n e r hr)

include e in
/-- `π_* 𝒪_Z(r)` is finite locally free. -/
theorem IsHilbertFamily.isFiniteLocallyFree_directImageSheaf (hZ : IsHilbertFamily ι Φ g Z)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    IsFiniteLocallyFree T (directImageSheaf ι g Z r) :=
  (hZ.sheafHasRank_directImageSheaf ι n e r hr).isFiniteLocallyFree

include e in
/-- **The formation of `π_* 𝒪_Z(r)` commutes with base change** (Nitsure, arXiv:math/0504590v1,
§5, p. 25, via Theorem 3.7): for a locally Noetherian `T`, a point `Z` of `Hilb^Φ(T)`, a
natural number `r ≥ hilbertRegularityBound n Φ` and every morphism `t : T' ⟶ T`, the base-change
map `t^* π_* 𝒪_Z(r) ⟶ π'_* (𝒪_Z(r))_{T'}` is an isomorphism. -/
theorem IsHilbertFamily.isIso_moduleBaseChangeMap_directImageSheaf (hZ : IsHilbertFamily ι Φ g Z)
    (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {T' : Scheme.{u}} (t : T' ⟶ T) :
    IsIso (moduleBaseChangeMap (pullback.snd (toSpec A ι) g) t (familyQuotientTwist ι g Z r)) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  have := hZ.flat
  moduleBaseChangeMap_isIso_of_geometric_concentration _ _
    (affineLocallyFiniteType_familyQuotientTwist ι g Z r)
    (relativeFlat_familyQuotientTwist ι g Z r) _ (hZ.fibreCohomologyConcentrated ι n e r hr) t

end DirectImage

end ProjectiveSpace

end AlgebraicGeometry

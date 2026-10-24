/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.DivisorLocus
public import Aglib.AlgebraicGeometry.Picard.Strata.Conditions
public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Representability
public import Aglib.RingTheory.Grassmannian.BaseChangeFormula

/-!
# The linear system `LinSys_{𝒪(W)}` over the divisor locus `Z`

Let `A` be a ring, `i : X ⟶ P^n_A` a preimmersion over `S = Spec A` (`hi : i ≫ toSpec A ι = πX`),
`C` a fibre condition, `E` a representation of `Div^θ_X` on locally Noetherian test schemes, and
`Z = C.abelPreimageOver E` (`Picard/Abel/Divisor`). The universal divisor of `Z` is the divisor
`W_Z ⊆ X ×_S Z` classified by the identity of `Z` (`FiberCondition.abelPreimageUniversalDivisor`),
and `𝒪(W_Z) = I_{W_Z}^∨` (`FiberCondition.abelPreimageDivisorLineBundle`) is a line bundle on
`X_Z = X ×_S Z` whose class is the Abel class of `W_Z` (by definition) and satisfies `C` at every
point of `Z` (`FiberCondition.holds_classOf_abelPreimageDivisorLineBundle`); its fppf class is the
universal class `α_Z` of `Z`.

On the fine stratum `C = fineCondition i N e φ₀ ψ 0 (k + 1)` (Kleiman's `P_0^{φ0}`, refined by `ψ`
and `r = k + 1 ≥ 1`) with `θ = ψ − φ₀`, `i` a closed immersion with `ι ≃ Fin (N + 1)` and
`πX = i ≫ toSpec A ι` flat:

* `Strata.sheafHasRank_pushforward_abelPreimageDivisorLineBundle`,
  `Strata.isIso_moduleBaseChangeMap_abelPreimageDivisorLineBundle`: the direct image
  `E_Z = p_{Z*} 𝒪(W_Z)` along `p_Z : X_Z ⟶ Z` is locally free of rank `k + 1`, and every
  base-change map of `𝒪(W_Z)` is an isomorphism (the fine condition at `m = 0` at every point of
  `Z`, through `sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds`). These
  are the hypotheses of the representability of `LinSys_{𝒪(W_Z)/X_Z/Z}` by the Grassmannian
  bundle `Gr(E_Z, k)` (`LinearSystem.linearSystemRepresentableBy`, Kleiman Thm 3.13, pp. 25–26).
* `Strata.abelRelationBundle e k E`: the Grassmannian bundle `Gr(E_Z, k)` over `Z`, which
  represents the linear system, the scheme `Z ×_{P_0^{φ0}} Z = LinSys_{L′/X_{T′}/T′}` with
  `T′ = Z` of Kleiman's proof of Thm 4.8 (p. 30), and
  `Strata.abelRelationLinearSystemDivisor e k E`, the universal divisor of the linear system on
  `X_Z ×_Z Gr(E_Z, k)`.

In Kleiman's proof (p. 30: "Now, `m = 0`, so `H^1(X_t, L_t) = 0` for all `t ∈ T′` owing to
(4.8.3)") this vanishing makes the module `Q` of his Subsection 3.10 locally free. Here the fibre
condition of the stratum also fixes `h^0(X_z, 𝒪(W_Z)_z) = k + 1`, so that `p_{Z*}𝒪(W_Z)` has
constant rank `k + 1` and every base-change map is an isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

open Modules.Invertible ProjectiveSpace

namespace FiberCondition

variable {ι : Type u} {A : Type u} [CommRing A] {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} {i : X ⟶ ProjectiveSpace A ι} {hi : i ≫ toSpec A ι = πX}
  [IsPreimmersion i] {θ : Polynomial ℚ} (C : FiberCondition πX)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy D)

/-- **The universal divisor of `Z`**: the divisor `W_Z ⊆ X ×_S Z` classified by the identity of
`Z = C.abelPreimageOver E` (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30: "the universal
relative effective divisor on `X_Z/Z`"). -/
def abelPreimageUniversalDivisor : (pullback πX (C.abelPreimageOver E).obj.hom).IdealSheafData :=
  ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1.1

/-- The universal divisor of `Z` is a relative effective Cartier divisor over `Z`. -/
theorem isRelativeEffectiveCartier_abelPreimageUniversalDivisor :
    Hom.IsRelativeEffectiveCartier (C.abelPreimageUniversalDivisor E).subschemeι
      (pullback.snd πX (C.abelPreimageOver E).obj.hom) :=
  ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1.2.isRelativeEffectiveCartier

/-- **The line bundle `𝒪(W_Z) = I_{W_Z}^∨`** of the universal divisor of `Z`, on `X ×_S Z`. -/
def abelPreimageDivisorLineBundle : LineBundle (pullback πX (C.abelPreimageOver E).obj.hom) :=
  dualLineBundle _ (C.isRelativeEffectiveCartier_abelPreimageUniversalDivisor E).idealLineBundle

/-- The class of `𝒪(W_Z)` is the Abel class of the universal divisor of `Z`. -/
theorem classOf_abelPreimageDivisorLineBundle :
    classOf _ (C.abelPreimageDivisorLineBundle E) =
      abelClass πX (T := (C.abelPreimageOver E).obj) (C.abelPreimageUniversalDivisor E)
        (C.isRelativeEffectiveCartier_abelPreimageUniversalDivisor E) :=
  rfl

/-- **`𝒪(W_Z)` satisfies the fibre condition at every point of `Z`.** -/
theorem holds_classOf_abelPreimageDivisorLineBundle (z : (C.abelPreimageOver E).obj.left) :
    C.Holds (C.abelPreimageOver E).obj (classOf _ (C.abelPreimageDivisorLineBundle E)) z :=
  (C.mem_abelPreimage_obj_iff_forall_holds i hi θ
    ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).1).mp
      ((C.abelPreimageRepresentableBy E).homEquiv (𝟙 _)).2 z

/-- The fppf class of `𝒪(W_Z)` is the universal class `α_Z` of `Z`. -/
theorem app_classOf_abelPreimageDivisorLineBundle :
    (quotientProjection πX ≫ toFppfPicardSheaf πX).app (op (C.abelPreimageOver E).obj)
        (classOf _ (C.abelPreimageDivisorLineBundle E)) = C.abelPreimageFppfAbelClass E :=
  (C.abelPreimageFppfAbelClass_eq E).symm

end FiberCondition

namespace Strata

open LinearSystem Grassmannian

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : Polynomial ℚ} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- **The direct image of `𝒪(W_Z)` has rank `k + 1`** on the fine stratum
`Pic^{φ₀,ψ,k+1}_0 ×_P Div^{ψ − φ₀}_X`: the fine condition at `m = 0` holds at every point of `Z`
(Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 30). -/
theorem sheafHasRank_pushforward_abelPreimageDivisorLineBundle :
    Modules.SheafHasRank ((Modules.pushforward (pullback.snd (i ≫ toSpec A ι)
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom)).obj
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E).val) (k + 1) :=
  (sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).holds_classOf_abelPreimageDivisorLineBundle E)).1

/-- **Every base-change map of `𝒪(W_Z)` is an isomorphism** on the fine stratum at `m = 0`. -/
theorem isIso_moduleBaseChangeMap_abelPreimageDivisorLineBundle (T : Scheme.{u})
    (g : T ⟶ ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.left) :
    IsIso (Modules.moduleBaseChangeMap (pullback.snd (i ≫ toSpec A ι)
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom) g
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E).val) :=
  (sheafHasRank_and_isIso_moduleBaseChangeMap_of_forall_fineCondition_holds
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).holds_classOf_abelPreimageDivisorLineBundle E)).2 T g

/-- **The scheme `R`** of the proof of Kleiman's Thm 4.8 (arXiv:math/0504020v1, p. 30): the
Grassmannian bundle `Gr(E_Z, k)` over `Z` of the rank-`k` locally free quotients of
`E_Z = p_{Z*} 𝒪(W_Z)`, which represents `LinSys_{𝒪(W_Z)/X_Z/Z}` (Thm 3.13, pp. 25–26). -/
def abelRelationBundle : Over ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.left :=
  grassmannianBundle ((Modules.pushforward (pullback.snd (i ≫ toSpec A ι)
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom)).obj
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E).val) k (k + 1)
    (sheafHasRank_pushforward_abelPreimageDivisorLineBundle e k E)

/-- `Gr(E_Z, k) ⟶ Z` is proper. -/
instance isProper_abelRelationBundle_hom : IsProper (abelRelationBundle e k E).hom :=
  isProper_grassmannianBundle_hom _ k (k + 1) _

/-- `Gr(E_Z, k) ⟶ Z` is flat. -/
instance flat_abelRelationBundle_hom : Flat (abelRelationBundle e k E).hom :=
  flat_grassmannianBundle_hom _ k (k + 1) _

/-- `Gr(E_Z, k) ⟶ Z` is locally of finite type. -/
instance locallyOfFiniteType_abelRelationBundle_hom :
    LocallyOfFiniteType (abelRelationBundle e k E).hom :=
  locallyOfFiniteType_grassmannianBundle_hom _ k (k + 1) _

variable [GeometricallyIntegral (i ≫ toSpec A ι)]

/-- **`LinSys_{𝒪(W_Z)/X_Z/Z}` is represented by `Gr(E_Z, k)`** (Kleiman, arXiv:math/0504020v1,
Thm 3.13, pp. 25–26, and proof of Thm 4.8, p. 30), for `πX` flat and geometrically integral. -/
def abelRelationBundleRepresentableBy :
    (linearSystemFunctor (pullback.snd (i ≫ toSpec A ι)
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom)
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E)).RepresentableBy
        (abelRelationBundle e k E) :=
  have : Finite ι := Finite.of_equiv _ e.symm
  linearSystemRepresentableBy _ _ (isIso_moduleBaseChangeMap_abelPreimageDivisorLineBundle e k E)
    (sheafHasRank_pushforward_abelPreimageDivisorLineBundle e k E)

/-- **The universal divisor of the linear system** on `X_Z ×_Z Gr(E_Z, k)`. -/
def abelRelationLinearSystemDivisor :
    (linearSystemFunctor (pullback.snd (i ≫ toSpec A ι)
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom)
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E)).obj
        (op (abelRelationBundle e k E)) :=
  (abelRelationBundleRepresentableBy e k E).homEquiv (𝟙 _)

/-- The divisor of the linear system classified by `c : T ⟶ Gr(E_Z, k)` over `Z` is the pullback
of the universal divisor along `X_Z ×_Z T ⟶ X_Z ×_Z Gr(E_Z, k)`. -/
theorem abelRelationBundleRepresentableBy_homEquiv_coe
    {T : Over ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.left}
    (c : T ⟶ abelRelationBundle e k E) :
    ((abelRelationBundleRepresentableBy e k E).homEquiv c).1 =
      (abelRelationLinearSystemDivisor e k E).1.comap (LinearSystem.familyMap _ c) := by
  rw [Functor.RepresentableBy.homEquiv_eq]
  rfl

end Strata

end AlgebraicGeometry.Scheme.RelativePicard

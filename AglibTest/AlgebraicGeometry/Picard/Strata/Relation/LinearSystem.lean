/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.LinearSystem

/-!
# Consumer checks for the linear system `LinSys_{𝒪(W)}` over `Z`

The line bundle `𝒪(W_Z)` of the universal divisor of `Z` satisfies the fibre condition at every
point; on a fine stratum at `m = 0` its direct image has rank `k + 1` with base change, and the
Grassmannian bundle `Gr(p_{Z*}𝒪(W_Z), k)` represents `LinSys_{𝒪(W_Z)/X_Z/Z}` (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, Thm 3.13, pp. 25–26, and proof of Thm 4.8, p. 30); with axiom
guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.Modules.Invertible Scheme.RelativePicard
open Scheme.RelativePicard.Strata Scheme.LinearSystem
open scoped Polynomial

universe u

namespace AglibTest.StrataRelationLinearSystem

section General

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {πX : X ⟶ Spec (CommRingCat.of A)} {i : X ⟶ ProjectiveSpace A ι} {hi : i ≫ toSpec A ι = πX}
  [IsPreimmersion i] {θ : ℚ[X]} (C : FiberCondition πX)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i hi θ).RepresentableBy D)

/-- `𝒪(W_Z)` has the Abel class of `W_Z`, satisfies `C` everywhere, and has fppf class `α_Z`. -/
example (z : (C.abelPreimageOver E).obj.left) :
    classOf _ (C.abelPreimageDivisorLineBundle E) =
        abelClass πX (T := (C.abelPreimageOver E).obj) (C.abelPreimageUniversalDivisor E)
          (C.isRelativeEffectiveCartier_abelPreimageUniversalDivisor E) ∧
      C.Holds (C.abelPreimageOver E).obj (classOf _ (C.abelPreimageDivisorLineBundle E)) z ∧
      (quotientProjection πX ≫ toFppfPicardSheaf πX).app (op (C.abelPreimageOver E).obj)
          (classOf _ (C.abelPreimageDivisorLineBundle E)) = C.abelPreimageFppfAbelClass E :=
  ⟨C.classOf_abelPreimageDivisorLineBundle E, C.holds_classOf_abelPreimageDivisorLineBundle E z,
    C.app_classOf_abelPreimageDivisorLineBundle E⟩

end General

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : ℚ[X]} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- On the fine stratum at `m = 0`, `p_{Z*}𝒪(W_Z)` has rank `k + 1` with base change, and its
Grassmannian bundle is proper, flat and locally of finite type over `Z`. -/
example (T : Scheme.{u})
    (g : T ⟶ ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.left) :
    Scheme.Modules.SheafHasRank ((Scheme.Modules.pushforward (pullback.snd (i ≫ toSpec A ι)
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom)).obj
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E).val) (k + 1) ∧
      IsIso (Scheme.Modules.moduleBaseChangeMap (pullback.snd (i ≫ toSpec A ι)
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom) g
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E).val) ∧
      IsProper (abelRelationBundle e k E).hom ∧ Flat (abelRelationBundle e k E).hom ∧
      LocallyOfFiniteType (abelRelationBundle e k E).hom :=
  ⟨sheafHasRank_pushforward_abelPreimageDivisorLineBundle e k E,
    isIso_moduleBaseChangeMap_abelPreimageDivisorLineBundle e k E T g, inferInstance,
    inferInstance, inferInstance⟩

/-- With geometrically integral fibres, `Gr(p_{Z*}𝒪(W_Z), k)` represents the linear system, and the
divisor classified by `c` is the pullback of the universal divisor. -/
example [GeometricallyIntegral (i ≫ toSpec A ι)]
    {T : Over ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.left}
    (c : T ⟶ abelRelationBundle e k E) :
    Nonempty ((linearSystemFunctor (pullback.snd (i ≫ toSpec A ι)
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom)
      ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageDivisorLineBundle E)).RepresentableBy
        (abelRelationBundle e k E)) ∧
      ((abelRelationBundleRepresentableBy e k E).homEquiv c).1 =
        (abelRelationLinearSystemDivisor e k E).1.comap (Scheme.LinearSystem.familyMap _ c) :=
  ⟨⟨abelRelationBundleRepresentableBy e k E⟩, abelRelationBundleRepresentableBy_homEquiv_coe e k E c⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.holds_classOf_abelPreimageDivisorLineBundle'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiberCondition.holds_classOf_abelPreimageDivisorLineBundle

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.sheafHasRank_pushforward_abelPreimageDivisorLineBundle'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sheafHasRank_pushforward_abelPreimageDivisorLineBundle

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.isIso_moduleBaseChangeMap_abelPreimageDivisorLineBundle'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isIso_moduleBaseChangeMap_abelPreimageDivisorLineBundle

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelRelationBundleRepresentableBy' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abelRelationBundleRepresentableBy

end AglibTest.StrataRelationLinearSystem

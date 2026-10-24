/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.Representability

/-!
# Consumer checks for the representability of `R = Z ×_P Z`

The comparisons `X ×_S U ≅ X_V ×_V U` are natural; the Grassmannian bundle `R` over `Z`, with its
projections, represents the pairs of points of `Z` with the same class in `Pic_{X/S,(fppf)}`
(Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 30); with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.Modules.Invertible Scheme.RelativePicard
open Scheme.RelativePicard.Strata
open scoped Polynomial

universe u

namespace AglibTest.StrataRelationRepresentability

/-- The comparison `X ×_S U ≅ X_V ×_V U` is natural in `U`. -/
example {S X : Scheme.{u}} (p : X ⟶ S) {U₁ U₂ V : Over S} (c : U₁ ⟶ U₂) (g : U₂ ⟶ V) :
    Scheme.LinearSystem.familyMap p c ≫
        (Scheme.LinearSystem.isPullback_familyMap p g).isoPullback.hom =
      (Scheme.LinearSystem.isPullback_familyMap p (c ≫ g)).isoPullback.hom ≫
        Scheme.LinearSystem.familyMap (pullback.snd p V.hom)
          (Over.homMk c.left rfl : Over.mk (c ≫ g).left ⟶ Over.mk g.left) :=
  familyMap_comp_isoPullback_hom p c g

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : ℚ[X]} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- `pr₁` is the structure map of the bundle; the transported universal divisor has class
`pr₁^* α_Z` and is classified by `pr₂`; `pr₁^* α_Z = pr₂^* α_Z`. -/
example :
    (abelRelationFst e k E).hom.left = (abelRelationBundle e k E).hom ∧
      fppfAbelClass (i ≫ toSpec A ι) (T := (abelRelationOver e k E).obj)
          (abelRelationSndDivisor e k E) (isRelativeEffectiveCartier_abelRelationSndDivisor e k E) =
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelRelationFst e k E).hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) ∧
      (((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageRepresentableBy E).homEquiv
          (abelRelationSnd e k E)).1.1 = abelRelationSndDivisor e k E ∧
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelRelationFst e k E).hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelRelationSnd e k E).hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) :=
  ⟨abelRelationFst_hom_left e k E, fppfAbelClass_abelRelationSndDivisor e k E,
    homEquiv_abelRelationSnd_coe e k E,
    fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd e k E⟩

/-- The pair `(pr₁, pr₂)` and its components. -/
example :
    abelRelationι e k E ≫ pullback.fst _ _ = (abelRelationFst e k E).hom.left ∧
      abelRelationι e k E ≫ pullback.snd _ _ = (abelRelationSnd e k E).hom.left :=
  ⟨abelRelationι_fst e k E, abelRelationι_snd e k E⟩

/-- **`R` represents `Z ×_P Z`**: injectivity, the description of the image, and the packaged
representation. -/
example [IsNoetherianRing A] {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E)
    {c c' : T ⟶ abelRelationOver e k E} :
    (c ≫ abelRelationFst e k E = c' ≫ abelRelationFst e k E →
        c ≫ abelRelationSnd e k E = c' ≫ abelRelationSnd e k E → c = c') ∧
      ((∃ c : T ⟶ abelRelationOver e k E,
          c ≫ abelRelationFst e k E = a ∧ c ≫ abelRelationSnd e k E = b) ↔
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
            ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
          (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map b.hom.op
            ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)) ∧
      ((abelRelationRepresentableBy e k E).homEquiv c).1 =
        (c ≫ abelRelationFst e k E, c ≫ abelRelationSnd e k E) :=
  ⟨abelRelation_hom_ext e k E, exists_comp_abelRelationFst_and_comp_abelRelationSnd_iff e k E a b,
    abelRelationRepresentableBy_homEquiv_coe e k E c⟩

/-- The packaged representation of `Z ×_P Z` by `R`. -/
example [IsNoetherianRing A] :
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelRelation E).RepresentableBy
      (abelRelationOver e k E) :=
  abelRelationRepresentableBy e k E

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.familyMap_comp_isoPullback_hom' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms familyMap_comp_isoPullback_hom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fppfAbelClass_abelRelationSndDivisor' depends
  on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfAbelClass_abelRelationSndDivisor

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelRelationSnd' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abelRelationSnd

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.homEquiv_comp_abelRelationSnd_coe' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms homEquiv_comp_abelRelationSnd_coe

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelRelation_hom_ext' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abelRelation_hom_ext

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.exists_comp_abelRelationFst_and_comp_abelRelationSnd_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_comp_abelRelationFst_and_comp_abelRelationSnd_iff

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelRelationRepresentableBy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abelRelationRepresentableBy

end AglibTest.StrataRelationRepresentability

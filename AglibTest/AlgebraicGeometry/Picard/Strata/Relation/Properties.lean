/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.Properties
public import Aglib.AlgebraicGeometry.Sites.FppfQuotient

/-!
# Consumer checks for the properties of `R = Z ×_P Z`

Both projections of `R` are proper and flat, `R ⟶ Z ×_S Z` is a closed immersion, and `R` is an
equivalence relation on `Z`, internally and on locally Noetherian points (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, proof of Thm 4.8 and of Lemma 4.9, p. 30). Also: the input shape of
the quotient of `Z` by `R` (Nitsure, arXiv:math/0504590v1, Thm 6.8), and hypotheses (h₁), (h₂) of
`Scheme.representableByOfFppfQuotient` for `z = α_Z` and a quotient `q : Z ⟶ Q` with
`R ≅ Z ×_Q Z`; with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.Modules.Invertible Scheme.RelativePicard
open Scheme.RelativePicard.Strata
open scoped Polynomial

universe u

namespace AglibTest.StrataRelationProperties

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : ℚ[X]} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- Both projections are proper and flat; the symmetry exchanges them and is an involution. -/
example :
    IsProper (abelRelationFst e k E).hom.left ∧ Flat (abelRelationFst e k E).hom.left ∧
      IsProper (abelRelationSnd e k E).hom.left ∧ Flat (abelRelationSnd e k E).hom.left ∧
      abelRelationSwap e k E ≫ abelRelationFst e k E = abelRelationSnd e k E ∧
      abelRelationSwap e k E ≫ abelRelationSwap e k E = 𝟙 _ :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, abelRelationSwap_fst e k E,
    abelRelationSwap_swap e k E⟩

/-- The input shape of the quotient of `Z` by `R`: the projections agree over `S`, the second is
proper and flat, `R(T) ⟶ Z(T) × Z(T)` is injective and its image is an equivalence relation for
every locally Noetherian scheme `T`. -/
example :
    (abelRelationFst e k E).hom.left ≫
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom =
      (abelRelationSnd e k E).hom.left ≫
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom ∧
    IsProper (abelRelationSnd e k E).hom.left ∧ Flat (abelRelationSnd e k E).hom.left ∧
    (∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (r r' : T ⟶ (abelRelationOver e k E).obj.left),
      r ≫ (abelRelationFst e k E).hom.left = r' ≫ (abelRelationFst e k E).hom.left →
        r ≫ (abelRelationSnd e k E).hom.left = r' ≫ (abelRelationSnd e k E).hom.left → r = r') ∧
    (∀ (T : Scheme.{u}) [IsLocallyNoetherian T], _root_.Equivalence
      (pointsRelation (abelRelationFst e k E).hom.left (abelRelationSnd e k E).hom.left T)) :=
  ⟨(Over.w (abelRelationFst e k E).hom).trans (Over.w (abelRelationSnd e k E).hom).symm,
    inferInstance, inferInstance, abelRelation_left_injective e k E,
    fun T _ => equivalence_pointsRelation_abelRelation e k E T⟩

/-- For `D` H-quasi-projective (hence separated and locally of finite type), `R ⟶ Z ×_S Z` is a
closed immersion, `pr₁, pr₂` is an equivalence relation, and `R` is Noetherian. -/
example [IsHQuasiProjective D.obj.hom] :
    IsClosedImmersion (abelRelationι e k E) ∧
      IsEquivalenceRelation (abelRelationFst e k E).hom.left (abelRelationSnd e k E).hom.left ∧
      IsNoetherian (abelRelationOver e k E).obj.left :=
  ⟨inferInstance, isEquivalenceRelation_abelRelation e k E, inferInstance⟩

/-- Hypotheses (h₁) and (h₂) of `Scheme.representableByOfFppfQuotient` for `z = α_Z`, given a
quotient `q : Z ⟶ Q` whose kernel pair is `R` (the cartesian square of the quotient of `Z` by
`R`). -/
example {Q : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (q : (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E ⟶ Q)
    (hR : IsPullback (abelRelationFst e k E).hom.left (abelRelationSnd e k E).hom.left
      q.hom.left q.hom.left) :
    (∀ ⦃T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))⦄
        (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E),
        ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
            a.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
            b.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) →
        a ≫ q = b ≫ q) ∧
    (∀ ⦃T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))⦄
        (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E), a ≫ q = b ≫ q →
        ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
            a.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
            b.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)) :=
  ⟨fun _ a b hab =>
    comp_eq_comp_of_fppfPicardSheaf_map_eq_of_abelRelationFst_comp_eq_abelRelationSnd_comp e k E q
      hR.w a b hab,
    Scheme.map_eq_map_of_comp_eq_of_isPullback
      (F := (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat) q _
      (abelRelationFst e k E).hom (abelRelationSnd e k E).hom hR
      (fppfPicardSheaf_map_abelRelationFst_eq_map_abelRelationSnd e k E)⟩

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.isProper_abelRelationSnd_hom_left' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isProper_abelRelationSnd_hom_left

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.flat_abelRelationSnd_hom_left' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms flat_abelRelationSnd_hom_left

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelRelation_left_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abelRelation_left_injective

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.isClosedImmersion_abelRelationι' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isClosedImmersion_abelRelationι

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.equivalence_pointsRelation_abelRelation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms equivalence_pointsRelation_abelRelation

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.isEquivalenceRelation_abelRelation' depends
  on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isEquivalenceRelation_abelRelation

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.isNoetherian_abelRelationOver' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isNoetherian_abelRelationOver

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.comp_eq_comp_of_fppfPicardSheaf_map_eq_of_abelRelationFst_comp_eq_abelRelationSnd_comp' depends
  on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  comp_eq_comp_of_fppfPicardSheaf_map_eq_of_abelRelationFst_comp_eq_abelRelationSnd_comp

end AglibTest.StrataRelationProperties

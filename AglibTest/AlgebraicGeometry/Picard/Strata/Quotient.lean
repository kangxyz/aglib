/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Quotient

/-!
# Consumer checks for the representation of the fine strata by `Q = Z / R`

The public statements of `Picard/Strata/Quotient` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, end of the proof of Thm 4.8, p. 30, and Lemma 4.9, pp. 30–31, fppf form on
locally Noetherian test schemes) are exercised: the compatibility of the projections of `R`; the
chosen quotient `Q` with `q` flat, surjective, proper, locally of finite presentation and
`R = Z ×_Q Z`; the identification `Z ×_Q Z = Z ×_P Z` on locally Noetherian points; the
descended class `λ` with `q^* λ = α_Z`, its uniqueness and its membership in the stratum; the
representation `f ↦ f^* λ` under the local lifting hypothesis, also in the literal form
`restrictSubfunctor (locallyNoetherianOver _) C.subfunctor` of the subfunctor; the
correspondence of `q` with `α_Z`; and the existence statement. With axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.RelativePicard Scheme.RelativePicard.Strata
open scoped Polynomial

universe u

namespace AglibTest.StrataQuotient

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : ℚ[X]} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} [IsHQuasiProjective D.obj.hom]
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- The input compatibility of the quotient theorem, and the chosen quotient: `Q` is
H-quasi-projective over `Spec A`, `q` is flat, surjective, proper and locally of finite
presentation, and `R = Z ×_Q Z`. -/
theorem abelQuotient_properties :
    (abelRelationFst e k E).hom.left ≫
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom =
      (abelRelationSnd e k E).hom.left ≫
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E).obj.hom ∧
    IsHQuasiProjective (abelQuotient e k E).quotientOver.obj.hom ∧
    Flat (abelQuotient e k E).quotientπ.hom.left ∧
    Surjective (abelQuotient e k E).quotientπ.hom.left ∧
    IsProper (abelQuotient e k E).quotientπ.hom.left ∧
    LocallyOfFinitePresentation (abelQuotient e k E).quotientπ.hom.left ∧
    IsPullback (abelRelationFst e k E).hom.left (abelRelationSnd e k E).hom.left
      (abelQuotient e k E).quotientπ.hom.left (abelQuotient e k E).quotientπ.hom.left :=
  ⟨abelRelation_w e k E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (abelQuotient e k E).isPullback_quotientπ⟩

/-- `Z ×_Q Z = Z ×_P Z` on locally Noetherian points. -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E) :
    a ≫ (abelQuotient e k E).quotientπ = b ≫ (abelQuotient e k E).quotientπ ↔
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map b.hom.op
          ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) :=
  comp_abelQuotientπ_eq_iff e k E a b

/-- The descended class: `q^* λ = α_Z`, `λ` is unique with this property, and it lies in the
stratum. -/
theorem abelQuotientFppfClass_properties :
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelQuotient e k E).quotientπ.hom.op
        (abelQuotientFppfClass e k E) =
      (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E ∧
    (∀ l : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj
        (op (abelQuotient e k E).quotientOver.obj),
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map (abelQuotient e k E).quotientπ.hom.op l =
          (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E →
        l = abelQuotientFppfClass e k E) ∧
    abelQuotientFppfClass e k E ∈ (fineCondition i N e φ₀ ψ 0 (k + 1)).subfunctor.obj
      (op (abelQuotient e k E).quotientOver.obj) :=
  ⟨fppfPicardSheaf_map_abelQuotientFppfClass e k E,
    fun _ hl => eq_abelQuotientFppfClass_of_map_eq e k E hl,
    abelQuotientFppfClass_mem_subfunctor e k E⟩

section Representation

variable
  (hloc : ∀ ⦃T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))⦄
    (ξ : ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).obj
      (op T.obj)),
    ξ ∈ (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.obj (op T) →
      ∀ t : T.obj.left, ∃ (U : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))
        (f : U ⟶ T) (a : U ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E),
        Flat f.hom.left ∧ LocallyOfFinitePresentation f.hom.left ∧ t ∈ Set.range f.hom.left ∧
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
              a.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
            ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
              f.hom.op ξ)

/-- The representation is `f ↦ f^* λ`, `q` corresponds to `α_Z`, and the identity of `Q`
corresponds to `λ`. -/
theorem abelQuotientRepresentableByOfExistsLift_properties
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (f : T ⟶ (abelQuotient e k E).quotientOver) :
    ((abelQuotientRepresentableByOfExistsLift e k E hloc).homEquiv f).1 =
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f.hom.op (abelQuotientFppfClass e k E) ∧
      ((abelQuotientRepresentableByOfExistsLift e k E hloc).homEquiv
          (abelQuotient e k E).quotientπ).1 =
        (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E ∧
      ((abelQuotientRepresentableByOfExistsLift e k E hloc).homEquiv (𝟙 _)).1 =
        abelQuotientFppfClass e k E := by
  refine ⟨abelQuotientRepresentableByOfExistsLift_homEquiv_coe e k E hloc f,
    abelQuotientRepresentableByOfExistsLift_homEquiv_quotientπ e k E hloc, ?_⟩
  rw [abelQuotientRepresentableByOfExistsLift_homEquiv_coe, ObjectProperty.FullSubcategory.id_hom,
    op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The two pullbacks of a section of `Q` to `T` determine the morphism: the representation is
injective on morphisms (`Functor.RepresentableBy.homEquiv` is a bijection). -/
example {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (f₁ f₂ : T ⟶ (abelQuotient e k E).quotientOver)
    (h : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f₁.hom.op (abelQuotientFppfClass e k E) =
      (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f₂.hom.op (abelQuotientFppfClass e k E)) :
    f₁ = f₂ :=
  (abelQuotientRepresentableByOfExistsLift e k E hloc).homEquiv.injective (Subtype.ext h)

include hloc in
/-- The existence statement. -/
example : ∃ (Q : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))
      (q : (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E ⟶ Q)
      (l : (fppfPicardSheaf (i ≫ toSpec A ι)).obj.obj (op Q.obj))
      (rep :
        (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy
          Q),
      IsHQuasiProjective Q.obj.hom ∧ Flat q.hom.left ∧ Surjective q.hom.left ∧
        IsProper q.hom.left ∧
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map q.hom.op l =
          (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E ∧
        ∀ {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (f : T ⟶ Q),
          (rep.homEquiv f).1 = (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f.hom.op l :=
  exists_fineCondition_representableBy_of_exists_lift e k E hloc

end Representation

/-- The local lifting hypothesis in the literal form with the subfunctor written as
`restrictSubfunctor (locallyNoetherianOver _) C.subfunctor` is accepted as `hloc`, and the result
is a representation of the stratum by an H-quasi-projective scheme, the input form of a cover by
representable open subfunctors. -/
example
    (hloc : ∀ ⦃T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))⦄
      (ξ : ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).obj
        (op T.obj)),
      ξ ∈ (Scheme.LocalRepresentability.restrictSubfunctor (Scheme.locallyNoetherianOver _)
        (fineCondition i N e φ₀ ψ 0 (k + 1)).subfunctor).obj (op T) →
      ∀ t : T.obj.left, ∃ (U : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))
        (f : U ⟶ T) (a : U ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E),
        Flat f.hom.left ∧ LocallyOfFinitePresentation f.hom.left ∧ t ∈ Set.range f.hom.left ∧
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
              a.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
            ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
              f.hom.op ξ) :
    IsHQuasiProjective (abelQuotient e k E).quotientOver.obj.hom ∧
      Nonempty
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy
          (abelQuotient e k E).quotientOver) :=
  ⟨inferInstance, ⟨abelQuotientRepresentableByOfExistsLift e k E hloc⟩⟩

end AglibTest.StrataQuotient

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelRelation_w' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.Strata.abelRelation_w

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotient' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotient

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.comp_abelQuotientπ_eq_iff' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.Strata.comp_abelQuotientπ_eq_iff

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientFppfClass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientFppfClass

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.fppfPicardSheaf_map_abelQuotientFppfClass'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.RelativePicard.Strata.fppfPicardSheaf_map_abelQuotientFppfClass

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.eq_abelQuotientFppfClass_of_map_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.Strata.eq_abelQuotientFppfClass_of_map_eq

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientFppfClass_mem_subfunctor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientFppfClass_mem_subfunctor

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientRepresentableByOfExistsLift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientRepresentableByOfExistsLift

/-- info:
'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientRepresentableByOfExistsLift_homEquiv_coe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Strata.abelQuotientRepresentableByOfExistsLift_homEquiv_coe

/-- info:
'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientRepresentableByOfExistsLift_homEquiv_quotientπ'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Strata.abelQuotientRepresentableByOfExistsLift_homEquiv_quotientπ

/-- info:
'AlgebraicGeometry.Scheme.RelativePicard.Strata.exists_fineCondition_representableBy_of_exists_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.RelativePicard.Strata.exists_fineCondition_representableBy_of_exists_lift

/-- info: 'AglibTest.StrataQuotient.abelQuotient_properties' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.StrataQuotient.abelQuotient_properties

/-- info: 'AglibTest.StrataQuotient.abelQuotientFppfClass_properties' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.StrataQuotient.abelQuotientFppfClass_properties

/-- info: 'AglibTest.StrataQuotient.abelQuotientRepresentableByOfExistsLift_properties' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.StrataQuotient.abelQuotientRepresentableByOfExistsLift_properties

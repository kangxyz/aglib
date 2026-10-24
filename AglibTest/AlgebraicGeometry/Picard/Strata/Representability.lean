/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.Representability

/-!
# Consumer checks for the representability of the fine strata `Pic^{φ₀,ψ,k+1}_0`

The unconditional statements of `Picard/Strata/Representability` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30, and Lemma 4.9, pp. 30–31, fppf form on locally
Noetherian test schemes) are exercised: the representation of the stratum by the quotient
`Q = Z / R` through `f ↦ f^* λ`, the correspondence of `q` with `α_Z` and of the identity of `Q`
with `λ`, the input form of a cover by representable open subfunctors (`Q` H-quasi-projective
with a representation of `C.locallyNoetherianSubfunctor`), and the existence statement. With axiom
guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.RelativePicard Scheme.RelativePicard.Strata
open scoped Polynomial

universe u

namespace AglibTest.StrataRepresentability

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : ℚ[X]} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} [IsHQuasiProjective D.obj.hom]
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- The representation is `f ↦ f^* λ`, `q` corresponds to `α_Z`, and the identity of `Q`
corresponds to `λ`. -/
theorem abelQuotientRepresentableBy_properties
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (f : T ⟶ (abelQuotient e k E).quotientOver) :
    ((abelQuotientRepresentableBy e k E).homEquiv f).1 =
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f.hom.op (abelQuotientFppfClass e k E) ∧
      ((abelQuotientRepresentableBy e k E).homEquiv (abelQuotient e k E).quotientπ).1 =
        (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E ∧
      ((abelQuotientRepresentableBy e k E).homEquiv (𝟙 _)).1 = abelQuotientFppfClass e k E := by
  refine ⟨abelQuotientRepresentableBy_homEquiv_coe e k E f,
    abelQuotientRepresentableBy_homEquiv_quotientπ e k E, ?_⟩
  rw [abelQuotientRepresentableBy_homEquiv_coe, ObjectProperty.FullSubcategory.id_hom, op_id,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The input form of a cover of `Pic_{X/S,(fppf)}` by representable open subfunctors: the stratum
`C.locallyNoetherianSubfunctor` is represented by the H-quasi-projective scheme `Q`, and every
section of the stratum over a locally Noetherian `T` is `f^* λ` for a unique `f : T ⟶ Q`. -/
theorem fineCondition_representableBy_isHQuasiProjective :
    IsHQuasiProjective (abelQuotient e k E).quotientOver.obj.hom ∧
      Nonempty
        ((fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy
          (abelQuotient e k E).quotientOver) ∧
      ∀ {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
        (ξ : (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.obj
          (op T)),
        ∃! f : T ⟶ (abelQuotient e k E).quotientOver,
          (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map f.hom.op (abelQuotientFppfClass e k E) =
            ξ.1 :=
  ⟨inferInstance, ⟨abelQuotientRepresentableBy e k E⟩, fun ξ =>
    ⟨(abelQuotientRepresentableBy e k E).homEquiv.symm ξ,
      congrArg Subtype.val ((abelQuotientRepresentableBy e k E).homEquiv.apply_symm_apply ξ),
      fun _ hf => (abelQuotientRepresentableBy e k E).homEquiv.injective
        ((Subtype.ext hf).trans ((abelQuotientRepresentableBy e k E).homEquiv.apply_symm_apply
          ξ).symm)⟩⟩

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
  exists_fineCondition_representableBy e k E

end AglibTest.StrataRepresentability

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientRepresentableBy' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientRepresentableBy

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientRepresentableBy_homEquiv_coe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Strata.abelQuotientRepresentableBy_homEquiv_coe

/-- info:
'AlgebraicGeometry.Scheme.RelativePicard.Strata.abelQuotientRepresentableBy_homEquiv_quotientπ'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Strata.abelQuotientRepresentableBy_homEquiv_quotientπ

/-- info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.exists_fineCondition_representableBy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.Strata.exists_fineCondition_representableBy

/-- info: 'AglibTest.StrataRepresentability.abelQuotientRepresentableBy_properties' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.StrataRepresentability.abelQuotientRepresentableBy_properties

/-- info: 'AglibTest.StrataRepresentability.fineCondition_representableBy_isHQuasiProjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.StrataRepresentability.fineCondition_representableBy_isHQuasiProjective

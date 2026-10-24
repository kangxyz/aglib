/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Strata.LocalSections
public import Aglib.AlgebraicGeometry.Sites.FppfQuotient

/-!
# Consumer checks for the local sections of the Abel map on a fine stratum

A line bundle satisfying the fine condition `Pic^{φ₀,ψ,k+1}_0` at every point of a locally
Noetherian `V` lifts to `Z = Pic^{φ₀,ψ,k+1}_0 ×_P Div^{ψ − φ₀}_X` over a flat surjective `U ⟶ V`
locally of finite presentation, and the Abel map `Z ⟶ Pic^{φ₀,ψ,k+1}_0` is fppf-locally
surjective on locally Noetherian test schemes (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 4.8, p. 30). The second statement is passed, without
rewriting, as hypothesis (h₃) of `Scheme.representableByOfFppfQuotient`; with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace Scheme.Modules.Invertible Scheme.RelativePicard
open Scheme.RelativePicard.Strata

universe u

namespace AglibTest.StrataLocalSections

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)]
  {N : ℕ} (e : ι ≃ Fin (N + 1)) {φ₀ ψ : Polynomial ℚ} (k : ℕ)
  {D : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
  (E : (locallyNoetherianRelativeDivisorFunctor i rfl (ψ - φ₀)).RepresentableBy D)

/-- A line bundle on the fine stratum at `m = 0` lifts to `Z` over a flat surjective morphism
locally of finite presentation. -/
example {V : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (L : LineBundle (pullback (i ≫ toSpec A ι) V.obj.hom))
    (hL : ∀ v, (fineCondition i N e φ₀ ψ 0 (k + 1)).Holds V.obj (classOf _ L) v) :
    ∃ (U : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))) (g : U ⟶ V)
      (a : U ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E),
      Flat g.hom.left ∧ LocallyOfFinitePresentation g.hom.left ∧ Surjective g.hom.left ∧
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map a.hom.op
            ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
          (fppfPicardSheaf (i ≫ toSpec A ι)).obj.map g.hom.op
            ((quotientProjection _ ≫ toFppfPicardSheaf _).app (op V.obj) (classOf _ L)) :=
  exists_lift_abelPreimageOver_of_forall_fineCondition_holds e k E L hL

/-- **(h₃) passed as is**: with a flat surjective quotient `q : Z ⟶ Q` locally of finite
presentation satisfying (h₁), (h₂) and descent along `q`, the local-lift theorem is hypothesis
(h₃) of `Scheme.representableByOfFppfQuotient`, and `Q` represents `Pic^{φ₀,ψ,k+1}_0` on locally
Noetherian test schemes. -/
example {Q : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (q : (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E ⟶ Q)
    [Flat q.hom.left] [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left]
    (hG : ∀ ξ : ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
        CategoryTheory.forget AddCommGrpCat).obj (op Q.obj),
      ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
          q.hom.op ξ ∈
        (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.obj
          (op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E)) →
        ξ ∈ (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.obj (op Q))
    (h₁ : ∀ ⦃T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))⦄
        (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E),
        ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
            a.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
            b.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) →
        a ≫ q = b ≫ q)
    (h₂ : ∀ ⦃T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))⦄
        (a b : T ⟶ (fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageOver E), a ≫ q = b ≫ q →
        ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
            a.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E) =
          ((fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙ CategoryTheory.forget AddCommGrpCat).map
            b.hom.op ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)) :
    (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q :=
  Scheme.representableByOfFppfQuotient (isSheaf_fppfPicardSheaf_forget _)
    (fineCondition i N e φ₀ ψ 0 (k + 1)).locallyNoetherianSubfunctor q
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass E)
    ((fineCondition i N e φ₀ ψ 0 (k + 1)).abelPreimageFppfAbelClass_mem_subfunctor E) hG h₁ h₂
    (exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition e k E)

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.exists_lift_abelPreimageOver_of_forall_fineCondition_holds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_lift_abelPreimageOver_of_forall_fineCondition_holds

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.Strata.exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_lift_abelPreimageOver_of_mem_subfunctor_fineCondition

end AglibTest.StrataLocalSections

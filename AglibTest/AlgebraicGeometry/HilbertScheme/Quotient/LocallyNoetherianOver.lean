/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.LocallyNoetherianOver

/-!
# Consumer checks for flat proper quotients as locally Noetherian test schemes

For a flat proper quotient `𝔮` of a locally Noetherian scheme `Z` over a Noetherian `Spec A`
(Nitsure, arXiv:math/0504590v1, Theorem 6.8, p. 33, with "projective" weakened to "proper"), the
quotient is a locally Noetherian test scheme, H-quasi-projective over `Spec A`, and the quotient
morphism is a morphism of such test schemes whose underlying morphism is `q`: flat, surjective,
proper, locally of finite presentation, with kernel pair `R`. With axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AglibTest.FlatProperQuotientLocallyNoetherianOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {Z : Scheme.LocallyNoetherianOver (Spec (.of A))} {R : Scheme.{u}} {p₁ p₂ : R ⟶ Z.obj.left}

/-- The quotient as a locally Noetherian test scheme, and the quotient morphism as a morphism of
such test schemes, with the properties consumed by representability statements on locally
Noetherian test schemes. -/
theorem quotientOver_quotientπ (𝔮 : FlatProperQuotient Z.obj.hom p₁ p₂) :
    𝔮.quotientOver.obj.left = 𝔮.Q ∧ 𝔮.quotientOver.obj.hom = 𝔮.πQ ∧
      IsHQuasiProjective 𝔮.quotientOver.obj.hom ∧ 𝔮.quotientπ.hom.left = 𝔮.q ∧
      Flat 𝔮.quotientπ.hom.left ∧ Surjective 𝔮.quotientπ.hom.left ∧
      IsProper 𝔮.quotientπ.hom.left ∧ LocallyOfFinitePresentation 𝔮.quotientπ.hom.left ∧
      IsPullback p₁ p₂ 𝔮.quotientπ.hom.left 𝔮.quotientπ.hom.left :=
  ⟨𝔮.quotientOver_obj_left, 𝔮.quotientOver_obj_hom, inferInstance, 𝔮.quotientπ_hom_left,
    inferInstance, inferInstance, inferInstance, inferInstance, 𝔮.isPullback_quotientπ⟩

/-- The quotient morphism lies over `Spec A`, as a morphism of `Over (Spec A)`. -/
example (𝔮 : FlatProperQuotient Z.obj.hom p₁ p₂) :
    𝔮.quotientπ.hom.left ≫ 𝔮.quotientOver.obj.hom = Z.obj.hom :=
  Over.w 𝔮.quotientπ.hom

end AglibTest.FlatProperQuotientLocallyNoetherianOver

/-- info: 'AglibTest.FlatProperQuotientLocallyNoetherianOver.quotientOver_quotientπ' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FlatProperQuotientLocallyNoetherianOver.quotientOver_quotientπ

/-- info: 'AlgebraicGeometry.FlatProperQuotient.quotientOver' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.FlatProperQuotient.quotientOver

/-- info: 'AlgebraicGeometry.FlatProperQuotient.quotientπ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.FlatProperQuotient.quotientπ

/-- info: 'AlgebraicGeometry.FlatProperQuotient.isHQuasiProjective_quotientOver_hom' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.FlatProperQuotient.isHQuasiProjective_quotientOver_hom

/-- info: 'AlgebraicGeometry.FlatProperQuotient.locallyOfFinitePresentation_quotientπ_hom_left'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.FlatProperQuotient.locallyOfFinitePresentation_quotientπ_hom_left

/-- info: 'AlgebraicGeometry.FlatProperQuotient.isPullback_quotientπ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.FlatProperQuotient.isPullback_quotientπ

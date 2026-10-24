/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.FlatProper
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver

/-!
# Flat proper quotients as locally Noetherian test schemes

Let `A` be a Noetherian ring, `Z` a locally Noetherian scheme over `Spec A`, given as an object of
`Scheme.LocallyNoetherianOver (Spec A)`, and `𝔮` a flat proper quotient of `Z` by
`p₁, p₂ : R ⟶ Z` (`FlatProperQuotient`,
`Aglib.AlgebraicGeometry.HilbertScheme.Quotient.FlatProper`): an H-quasi-projective
`πQ : Q ⟶ Spec A` with a flat, surjective, proper `q : Z ⟶ Q` over `Spec A` such that
`R = Z ×_Q Z` through `(p₁, p₂)`. Since `Q` is locally Noetherian
(`FlatProperQuotient.isLocallyNoetherian`):

* `FlatProperQuotient.quotientOver 𝔮` is `Q` with its structure morphism `πQ`, as an object of
  `Scheme.LocallyNoetherianOver (Spec A)`; its structure morphism is H-quasi-projective
  (instance `FlatProperQuotient.isHQuasiProjective_quotientOver_hom`).
* `FlatProperQuotient.quotientπ 𝔮 : Z ⟶ 𝔮.quotientOver` is `q` as a morphism of locally Noetherian
  test schemes, a morphism over `Spec A` by `FlatProperQuotient.fac`. Its underlying morphism of
  schemes is `q` (`FlatProperQuotient.quotientπ_hom_left`); it is flat, surjective, proper and
  locally of finite presentation (instances), and the square `(p₁, p₂, q, q)` is cartesian
  (`FlatProperQuotient.isPullback_quotientπ`).

This is the form in which the quotient enters representability statements on locally Noetherian
test schemes, for example the fppf form of Kleiman's Lemma 4.9
(`Scheme.representableByOfFppfQuotient`, `Aglib.AlgebraicGeometry.Sites.FppfQuotient`), whose
quotient morphism is a morphism of `Scheme.LocallyNoetherianOver S` that is flat, surjective and
locally of finite presentation. The file repackages the fields of `FlatProperQuotient` (Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, Theorem 6.8, p. 33, with
"projective" weakened to "proper"); it proves no new property of the quotient.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FlatProperQuotient

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {Z : Scheme.LocallyNoetherianOver (Spec (.of A))} {R : Scheme.{u}} {p₁ p₂ : R ⟶ Z.obj.left}
  (𝔮 : FlatProperQuotient Z.obj.hom p₁ p₂)

/-- **The quotient as a locally Noetherian test scheme**: `Q` with its structure morphism
`πQ : Q ⟶ Spec A`, an object of `Scheme.LocallyNoetherianOver (Spec A)` because `Q` is locally
Noetherian over the Noetherian ring `A`. -/
def quotientOver : Scheme.LocallyNoetherianOver (Spec (.of A)) :=
  ⟨Over.mk 𝔮.πQ, 𝔮.isLocallyNoetherian⟩

@[simp]
theorem quotientOver_obj_left : 𝔮.quotientOver.obj.left = 𝔮.Q :=
  rfl

@[simp]
theorem quotientOver_obj_hom : 𝔮.quotientOver.obj.hom = 𝔮.πQ :=
  rfl

/-- The structure morphism of the quotient is H-quasi-projective. -/
instance isHQuasiProjective_quotientOver_hom : IsHQuasiProjective 𝔮.quotientOver.obj.hom :=
  𝔮.isHQuasiProjective

/-- **The quotient morphism as a morphism of locally Noetherian test schemes**: `q : Z ⟶ Q`, a
morphism over `Spec A` by `FlatProperQuotient.fac`. -/
def quotientπ : Z ⟶ 𝔮.quotientOver :=
  ObjectProperty.homMk (Over.homMk (V := Over.mk 𝔮.πQ) 𝔮.q 𝔮.fac)

@[simp]
theorem quotientπ_hom_left : 𝔮.quotientπ.hom.left = 𝔮.q :=
  rfl

/-- The quotient morphism is flat. -/
instance flat_quotientπ_hom_left : Flat 𝔮.quotientπ.hom.left :=
  𝔮.flat

/-- The quotient morphism is surjective. -/
instance surjective_quotientπ_hom_left : Surjective 𝔮.quotientπ.hom.left :=
  𝔮.surjective

/-- The quotient morphism is proper. -/
instance isProper_quotientπ_hom_left : IsProper 𝔮.quotientπ.hom.left :=
  𝔮.isProper

/-- The quotient morphism is locally of finite presentation (`A` is Noetherian). -/
instance locallyOfFinitePresentation_quotientπ_hom_left :
    LocallyOfFinitePresentation 𝔮.quotientπ.hom.left :=
  𝔮.locallyOfFinitePresentation

/-- **`R = Z ×_Q Z`** for the quotient morphism of locally Noetherian test schemes: the square
`(p₁, p₂, q, q)` is cartesian. -/
theorem isPullback_quotientπ : IsPullback p₁ p₂ 𝔮.quotientπ.hom.left 𝔮.quotientπ.hom.left :=
  𝔮.isPullback

end AlgebraicGeometry.FlatProperQuotient

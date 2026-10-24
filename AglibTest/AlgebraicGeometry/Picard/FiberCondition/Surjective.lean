/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FiberCondition.OpenSubfunctor
public import Aglib.AlgebraicGeometry.Picard.FiberCondition.Surjective
public import Aglib.AlgebraicGeometry.Sites.FppfQuotient

/-!
# Consumer checks for descent of `Pic^C` along surjections

The subsheaf `Pic^C` of a fiber condition descends along every morphism surjective on points; in
particular it satisfies the descent hypothesis of the fppf form of Kleiman's Lemma 4.9
(arXiv:math/0504020v1, p. 30) along a quotient map `q`, and the lemma then applies to
`G = Pic^C` on locally Noetherian test schemes with `F` the underlying presheaf of sets of
`Pic_{X/S,(fppf)}`, giving a representation of `C.locallyNoetherianSubfunctor`, the form consumed
by `Scheme.LocalRepresentability.SubfunctorCover`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Scheme.RelativePicard Scheme.RelativePicard.FiberCondition

universe u

namespace AglibTest.FiberConditionSurjective

variable {S X : Scheme.{u}} {p : X ⟶ S} (C : FiberCondition p)

/-- The descent hypothesis of `representableByOfFppfQuotient` for `G = Pic^C`. -/
example {Z Q : Scheme.LocallyNoetherianOver S} (q : Z ⟶ Q) [Surjective q.hom.left]
    (ξ : ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).obj (op Q.obj))
    (h : ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).map q.hom.op ξ ∈
      C.locallyNoetherianSubfunctor.obj (op Z)) :
    ξ ∈ C.locallyNoetherianSubfunctor.obj (op Q) :=
  C.mem_subfunctor_of_map_mem q.hom q.hom.left.surjective h

/-- The fppf form of Kleiman's Lemma 4.9 for `G = Pic^C`: from (h₁), (h₂), (h₃) for a section
`z ∈ Pic^C(Z)` and a flat surjective `q : Z ⟶ Q` locally of finite presentation, `Q` represents
`Pic^C` on locally Noetherian test schemes. -/
example {Z Q : Scheme.LocallyNoetherianOver S} (q : Z ⟶ Q) [Flat q.hom.left]
    [Surjective q.hom.left] [LocallyOfFinitePresentation q.hom.left]
    (z : (fppfPicardSheaf p).obj.obj (op Z.obj)) (hz : z ∈ C.locallyNoetherianSubfunctor.obj (op Z))
    (h₁ : ∀ ⦃T : Scheme.LocallyNoetherianOver S⦄ (a b : T ⟶ Z),
      (fppfPicardSheaf p).obj.map a.hom.op z = (fppfPicardSheaf p).obj.map b.hom.op z →
        a ≫ q = b ≫ q)
    (h₂ : ∀ ⦃T : Scheme.LocallyNoetherianOver S⦄ (a b : T ⟶ Z), a ≫ q = b ≫ q →
      (fppfPicardSheaf p).obj.map a.hom.op z = (fppfPicardSheaf p).obj.map b.hom.op z)
    (h₃ : ∀ ⦃T : Scheme.LocallyNoetherianOver S⦄ (ξ : (fppfPicardSheaf p).obj.obj (op T.obj)),
      ξ ∈ C.locallyNoetherianSubfunctor.obj (op T) → ∀ t : T.obj.left,
        ∃ (U : Scheme.LocallyNoetherianOver S) (k : U ⟶ T) (a : U ⟶ Z),
          Flat k.hom.left ∧ LocallyOfFinitePresentation k.hom.left ∧ t ∈ Set.range k.hom.left ∧
            (fppfPicardSheaf p).obj.map a.hom.op z = (fppfPicardSheaf p).obj.map k.hom.op ξ) :
    C.locallyNoetherianSubfunctor.toFunctor.RepresentableBy Q :=
  Scheme.representableByOfFppfQuotient (isSheaf_fppfPicardSheaf_forget p)
    C.locallyNoetherianSubfunctor q z hz
    (fun _ h => C.mem_subfunctor_of_map_mem q.hom q.hom.left.surjective h) h₁ h₂ h₃

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.mem_subfunctor_of_map_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mem_subfunctor_of_map_mem

end AglibTest.FiberConditionSurjective

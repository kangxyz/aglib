/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Sites.Descent.Composition
public import Aglib.CategoryTheory.Sites.Descent.OverSigma

/-! Focused consumer of the generic descent leaves `Composition`, `Bind` and `OverSigma`: the
monotonicity of (pre)stacks in the topology, effective descent along composites of covering
families and presieves for prestacks (`IsStackFor.bind`), and the sheaf conditions of
`Presieve.overSigma`, with axiom guards. -/

@[expose] public section

open CategoryTheory Opposite Bicategory

universe w v' v u' u

variable {C : Type u} [Category.{v} C]

example (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {J J' : GrothendieckTopology C} (h : J ≤ J')
    [F.IsStack J'] : F.IsStack J :=
  Pseudofunctor.IsStack.of_le F h

example (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} (R : Presieve S) (R' : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ S⦄, R f → Presieve Y)
    (hR : Sieve.generate R ∈ J S) (hR' : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ S⦄ (hf : R f),
      Sieve.generate (R' hf) ∈ J Y)
    (hRst : F.IsStackFor R) (hR'st : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ S⦄ (hf : R f), F.IsStackFor (R' hf)) :
    F.IsStackFor (R.bind R') :=
  hRst.bind hR R' hR'st hR'

example (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {J : GrothendieckTopology C} [F.IsPrestack J]
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) {κ : ι → Type w} {Y : ∀ i, κ i → C}
    (g : ∀ i j, Y i j ⟶ X i) [∀ i, (F.toDescentData (g i)).IsEquivalence]
    (hg : ∀ i, Sieve.ofArrows (Y i) (g i) ∈ J (X i)) (hf : Sieve.ofArrows X f ∈ J S)
    [(F.toDescentData f).IsEquivalence] :
    (F.toDescentData (fun ij : Σ i, κ i ↦ g ij.1 ij.2 ≫ f ij.1)).IsEquivalence :=
  Pseudofunctor.isEquivalence_toDescentData_comp (J := J) f g hg hf

example {S : C} (P : (Over S)ᵒᵖ ⥤ Type w) {R : Sieve S}
    (hR : Presieve.IsSheafFor (Presieve.overSigma P) R.arrows)
    (hY : Presieve.IsSeparatedFor (yoneda.obj S) R.arrows) :
    Presieve.IsSheafFor P ((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).arrows :=
  Presieve.isSheafFor_of_isSheafFor_overSigma P hR hY

/--
info: 'CategoryTheory.Pseudofunctor.IsPrestack.of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.IsPrestack.of_le

/--
info: 'CategoryTheory.Pseudofunctor.IsStack.of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.IsStack.of_le

/--
info: 'CategoryTheory.Presieve.isSheafFor_of_isSheafFor_overSigma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Presieve.isSheafFor_of_isSheafFor_overSigma

/--
info: 'CategoryTheory.Presieve.isSheafFor_overSigma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Presieve.isSheafFor_overSigma

/--
info: 'CategoryTheory.Pseudofunctor.eq_of_pullHom_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.eq_of_pullHom_eq

/--
info: 'CategoryTheory.Pseudofunctor.exists_pullHom_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.exists_pullHom_eq

/--
info: 'CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_comp

/--
info: 'CategoryTheory.Pseudofunctor.IsStackFor.bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Pseudofunctor.IsStackFor.bind

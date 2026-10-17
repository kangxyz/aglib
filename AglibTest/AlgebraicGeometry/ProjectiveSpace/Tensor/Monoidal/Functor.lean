/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Monoidal.Braided

/-! Focused consumer of the monoidal and braided twisting functor: instance search finds the
additive braided structure on `Discrete ℤ` and the monoidal and braided structures of
`twistingFunctor R ι`; its tensorator and unit comparison are the existing twist maps, and the
coherence equations of a braided monoidal functor hold for it. -/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry
  AlgebraicGeometry.ProjectiveSpace

universe u

variable (R : Type u) [CommRing R] (ι : Type u)

example : BraidedCategory (Discrete ℤ) := inferInstance

example : SymmetricCategory (Discrete ℤ) := inferInstance

example (a b : ℤ) : ((⟨a⟩ : Discrete ℤ) ⊗ ⟨b⟩).as = a + b := rfl

example (a b : ℤ) : (β_ (⟨a⟩ : Discrete ℤ) ⟨b⟩).hom = Discrete.eqToHom (add_comm a b) := rfl

example : (twistingFunctor R ι).Monoidal := inferInstance

example : (twistingFunctor R ι).Braided := inferInstance

example (n : ℤ) : (twistingFunctor R ι).obj ⟨n⟩ = twistingSheaf R ι n := rfl

example (a b : ℤ) :
    Functor.LaxMonoidal.μ (twistingFunctor R ι) ⟨a⟩ ⟨b⟩ = twistingTensorMap R ι a b := rfl

example : Functor.LaxMonoidal.ε (twistingFunctor R ι) = unitToTwistingZero R ι := rfl

example (m n : Discrete ℤ) :
    Functor.Monoidal.μIso (twistingFunctor R ι) m n = twistingTensorIso R ι m.as n.as := rfl

/-- The tensorator of the twisting functor is associative, as an instance of the general law. -/
example (X Y Z : Discrete ℤ) :
    Functor.LaxMonoidal.μ (twistingFunctor R ι) X Y ▷ (twistingFunctor R ι).obj Z ≫
        Functor.LaxMonoidal.μ (twistingFunctor R ι) (X ⊗ Y) Z ≫
          (twistingFunctor R ι).map (α_ X Y Z).hom =
      (α_ _ _ _).hom ≫
        (twistingFunctor R ι).obj X ◁ Functor.LaxMonoidal.μ (twistingFunctor R ι) Y Z ≫
          Functor.LaxMonoidal.μ (twistingFunctor R ι) X (Y ⊗ Z) :=
  Functor.LaxMonoidal.associativity _ X Y Z

/-- The tensorator of the twisting functor is compatible with the braidings. -/
example (X Y : Discrete ℤ) :
    Functor.LaxMonoidal.μ (twistingFunctor R ι) X Y ≫ (twistingFunctor R ι).map (β_ X Y).hom =
      (β_ _ _).hom ≫ Functor.LaxMonoidal.μ (twistingFunctor R ι) Y X :=
  Functor.LaxBraided.braided X Y

/--
info: 'CategoryTheory.Discrete.addBraidedCategory' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Discrete.addBraidedCategory

/--
info: 'CategoryTheory.Discrete.addSymmetricCategory' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Discrete.addSymmetricCategory

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingSection_eqToHom_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSection_eqToHom_val

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingSectionsEquiv_eqToHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSectionsEquiv_eqToHom

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingSectionMul_assoc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSectionMul_assoc

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingSectionMul_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSectionMul_comm

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMap_associativity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMap_associativity

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMap_leftUnitor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMap_leftUnitor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMap_rightUnitor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMap_rightUnitor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorMap_braiding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorMap_braiding

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingFunctorCoreMonoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingFunctorCoreMonoidal

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingFunctor_monoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingFunctor_monoidal

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingFunctor_braided' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingFunctor_braided

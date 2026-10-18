/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Homology.CochainComplex.ProjectiveCokernel

/-! Focused consumer of the projective cokernels of a bounded complex of projective modules that is
exact in positive degrees, with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- The complex-level statement: projective `H^0` for a bounded complex of projectives that is
exact in positive degrees. -/
example {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    [∀ j, Module.Projective A (K.X j)] (n : ℕ) [K.IsStrictlyGE 0] [K.IsStrictlyLE (n : ℤ)]
    (hvan : ∀ q : ℕ, q ≠ 0 → IsZero (K.homology (q : ℤ))) :
    Module.Projective A (K.homology 0) :=
  K.projective_homology_zero_of_vanishing n hvan

/-- Every cokernel of the differentials is projective, and scalar extension commutes with
homology in every nonnegative degree. -/
example {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    [∀ j, Module.Projective A (K.X j)] (n : ℕ) [K.IsStrictlyLE (n : ℤ)]
    (hvan : ∀ q : ℕ, q ≠ 0 → IsZero (K.homology (q : ℤ))) {B : Type u} [CommRing B]
    (σ : A →+* B) (q : ℕ) :
    Projective (cokernel (K.d (q : ℤ) ((q : ℤ) + 1))) ∧
      IsIso (HomologicalComplex.extendScalarsHomologyMap σ K (q : ℤ)) :=
  ⟨K.projective_cokernel_d_of_vanishing n hvan q,
    K.extendScalarsHomologyMap_isIso_of_vanishing n hvan σ q⟩

/--
info: 'CochainComplex.projective_cokernel_d_pred' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CochainComplex.projective_cokernel_d_pred

/--
info: 'CochainComplex.projective_cokernel_d_sub_of_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CochainComplex.projective_cokernel_d_sub_of_vanishing

/--
info: 'CochainComplex.projective_cokernel_d_of_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CochainComplex.projective_cokernel_d_of_vanishing

/--
info: 'CochainComplex.projective_homology_zero_of_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CochainComplex.projective_homology_zero_of_vanishing

/--
info: 'CochainComplex.extendScalarsHomologyMap_isIso_of_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CochainComplex.extendScalarsHomologyMap_isIso_of_vanishing

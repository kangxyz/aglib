/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Cohomology

/-!
# Compactly supported étale cohomology along an open immersion

The examples check that compactly supported cohomology is literally the original cohomology of
the extension by zero, exercise its functoriality and long exact sequence, and guard the axioms
of every public declaration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleCohomology

universe w u

namespace AglibTest.CompactSupportCohomology

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Compactly supported cohomology is the original cohomology of the extension by zero. -/
example (F : AbelianSheaf.{u, u + 1} U) (r : ℕ) :
    CompactSupport.H j F r = Sheaf.H.{w} ((etaleLowerShriek j).obj F) r :=
  rfl

/-- The functoriality is the original cohomology map of the extended morphism. -/
example {F G : AbelianSheaf.{u, u + 1} U} (φ : F ⟶ G) (r : ℕ) (x : CompactSupport.H j F r) :
    CompactSupport.H.map j φ r x = Sheaf.H.map ((etaleLowerShriek j).map φ) r x :=
  CompactSupport.H.map_apply j φ r x

/-- An isomorphism of coefficients induces a bijection. -/
example {F G : AbelianSheaf.{u, u + 1} U} (φ : F ≅ G) (r : ℕ) :
    Function.Bijective (CompactSupport.H.map j φ.hom r) :=
  CompactSupport.H.map_bijective_of_isIso j φ.hom r

/-- A short exact sequence on `U` gives exactness of compactly supported cohomology. -/
example {S : ShortComplex (AbelianSheaf.{u, u + 1} U)} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (CompactSupport.H.map j S.f n) (CompactSupport.H.map j S.g n) ∧
      Function.Exact (CompactSupport.H.map j S.g n) (CompactSupport.δ j hS n (n + 1) rfl) ∧
        Function.Exact (CompactSupport.δ j hS n (n + 1) rfl)
          (CompactSupport.H.map j S.f (n + 1)) :=
  ⟨CompactSupport.exact_map_f_map_g j hS n, CompactSupport.exact_map_g_δ j hS n (n + 1) rfl,
    CompactSupport.exact_δ_map_f j hS n (n + 1) rfl⟩

/-- The counit map is the original cohomology map of the counit. -/
example (G : AbelianSheaf.{u, u + 1} X) (r : ℕ)
    (x : CompactSupport.H j ((inverseImage j).obj G) r) :
    CompactSupport.counitMap j G r x =
      Sheaf.H.map ((etaleLowerShriekAdjunction j).counit.app G) r x :=
  CompactSupport.counitMap_apply j G r x

end AglibTest.CompactSupportCohomology

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map_id_apply' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map_id_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map_comp_apply' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map_comp_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map_bijective_of_isIso' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.H.map_bijective_of_isIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.functor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.functor

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_apply' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.counitMap_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.δ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.δ

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.longSequence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.longSequence

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.longSequence_exact' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.longSequence_exact

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_map_f_map_g' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_map_f_map_g

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_map_g_δ' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_map_g_δ

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_δ_map_f' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.exact_δ_map_f

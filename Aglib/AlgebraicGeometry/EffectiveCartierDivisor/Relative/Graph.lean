/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.GraphIdeal
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteFlat

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# A degree-one divisor is an actual graph once its projection is an isomorphism

An isomorphism q : D ≅ T constructs the section q⁻¹ i pr₁. The equality
q ≫ graph(section) = i is proved by the actual pullback projections. This
works over every scheme, including nonreduced and non-Noetherian bases.

The ideal-module comparison is the actual map of kernels induced by the
structural sheaf isomorphism for a source isomorphism. No graph identity,
line-bundle isomorphism or inverse Abel map is supplied as a premise.
The degree-one and projection-isomorphism hypotheses are discharged in
separate applications; there are no retained theorem families here.
-/
/-!
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
This module is a new reusable curve foundation for that application.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.Graph` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`09678d190ad960a7837255e8d90237d4b94f3efe9b1e51ac4af01cbea5d2557e`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Hom
universe u
variable {X Y Z : Scheme.{u}}
@[reassoc] theorem sourceIsoStructureIso_square (e : X ≅ Y) (i : Y ⟶ Z) :
    AlgebraicGeometry.Scheme.Hom.structureModuleMap i ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardStructureSourceIso e i).hom =
        AlgebraicGeometry.Scheme.Hom.structureModuleMap (e.hom ≫ i) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

/-- The ideal-module isomorphism induced by replacing the source of a morphism by an isomorphic
scheme. -/
def idealSourceIso (e : X ≅ Y) (i : Y ⟶ Z) :
    idealModule i ≅ idealModule (e.hom ≫ i) :=
  kernel.mapIso (AlgebraicGeometry.Scheme.Hom.structureModuleMap i)
      (AlgebraicGeometry.Scheme.Hom.structureModuleMap (e.hom ≫ i)) (Iso.refl _)
    (AlgebraicGeometry.Scheme.Modules.pushforwardStructureSourceIso e i) (by simpa using
        (sourceIsoStructureIso_square e i))

variable {S T D : Scheme.{u}} (p : X ⟶ S) (t : T ⟶ S) (i : D ⟶ pullback p t)
variable [IsIso (i ≫ pullback.snd p t)]
/-- The section recovered from `i` when its projection to the parameter scheme is an isomorphism. -/
def divisorSection : T ⟶ X := inv (i ≫ pullback.snd p t) ≫ i ≫ pullback.fst p t

@[reassoc (attr := simp)] theorem divisorSection_over : divisorSection p t i ≫ p = t := by
  simp only [divisorSection, Category.assoc, pullback.condition]
  rw [← Category.assoc i, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The isomorphism from the source of `i` to the parameter scheme given by its projection. -/
def divisorGraphIso : D ≅ T := asIso (i ≫ pullback.snd p t)

@[reassoc (attr := simp)] theorem divisorGraphIso_graph :
    (divisorGraphIso p t i).hom ≫ graph p t (divisorSection p t i) (divisorSection_over p t i)
        = i := by
  apply pullback.hom_ext
  · rw [Category.assoc, graph_fst]
    simp [divisorGraphIso, divisorSection, ← Category.assoc]
  · simp [divisorGraphIso]

/-- The ideal-module comparison between `i` and the graph of its recovered section,
assuming the projection of `i` is an isomorphism. -/
def divisorGraphIdealIso :
    idealModule (graph p t (divisorSection p t i) (divisorSection_over p t i)) ≅ idealModule i :=
  idealSourceIso (divisorGraphIso p t i) _ ≪≫
    eqToIso (congrArg idealModule (divisorGraphIso_graph p t i))
end AlgebraicGeometry.Scheme.Hom

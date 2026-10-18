/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.PrimitiveCharacters
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
This module retains the assigned pointed-character and geometric-comparison declarations.
The original source context below describes the full pre-split family;
its stated hypotheses and uninstantiated comparison boundaries remain in force.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/-!
# Primitive pointed characters and marked incoming isogenies

Source: `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, lines 341–445 of
`research/exposes/K2/018/expose.tex` at
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.

The direct continuous cocycle model `PointedH1` is used explicitly. Primitive
classes are first identified with surjective continuous equivariant characters,
using proved order preservation and finite cyclic algebra. General finite-etale
monodromy inputs then classify pointed geometrically connected coefficient
covers. The separately proved geometry comparison gives marked incoming cyclic
isogenies of actual group schemes over F, up to marked F-isomorphism.

The monodromy background quantifies over general finite etale coefficient
schemes and finite discrete modules; none of its fields mentions H¹, primitive
order, or isogenies. The geometric coefficient marking uses actual points over
an algebraically closed field and an explicit descent action. In particular,
cyclicity alone never identifies a coefficient scheme with the chi-square twist.
G and N are supplied continuous fundamental-group model data. Their actual
fundamental-group realization and the etale/cochain comparison are named
background boundaries, rather than an implicit replacement by discrete cohomology.
Each declaration's source pointer uses the module source basis above.
-/

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers
open GroupCohomology.PointedCohomology GroupCohomology.PrimitiveCharacters

namespace GroupCohomology.PrimitiveCharacters.Translation

universe u v
attribute [local instance] Over.cartesianMonoidalCategory

variable {G N : Type*} [Group G] [Group N] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace N]

variable {F K : Type u} [Field F] [Field K]
variable (s : Spec (CommRingCat.of K) ⟶ Base F)
variable (sigma : G →* Aut (Over.mk s))

/-- Explicit geometric coefficient realization for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
The points are actual scheme maps. Identifying the fixed sigma with the
arithmetic Galois descent action remains a general realization input. -/
structure CoefficientRealization (A : Grp (FScheme F)) (R : Type v)
    [AddCommGroup R] [DistribMulAction G R] where
  /-- Algebraically closed geometric field in the general coefficient realization
  for `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  closed : IsAlgClosed K
  /-- Supplied geometric descent action for
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  action : MulDistribMulAction G (Over.mk s ⟶ A.X)
  /-- General descent compatibility for
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  descent : ∀ g x, @SMul.smul G (Over.mk s ⟶ A.X) action.toSMul g x =
    (sigma (g⁻¹)).hom ≫ x
  /-- Actual geometric-point marking for
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  marking : (Over.mk s ⟶ A.X) ≃* Multiplicative R
  /-- Explicit coefficient-action compatibility for
  `K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
  equivariant : ∀ g x, marking (@SMul.smul G (Over.mk s ⟶ A.X) action.toSMul g x) =
    Multiplicative.ofAdd (g • (marking x).toAdd)

end GroupCohomology.PrimitiveCharacters.Translation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3d2bd6e35b98ffd673d8dc2030b76646602dcc1e81824bba4ab281331ca64875.
Definitions, hypotheses and universes are retained modulo native names. -/

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Field
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic

/-!
# Coherent genus of actual field curves

The underlying structure sheaf, actual Zariski Hⁿ, its structural scalar action,
and the scalar-compatible H⁰ comparison are constructed in
`Curves.Cohomology.StructureSheaf`. This facade retains the public genus,
finiteness and constants declarations.

Application: K2-018#prop:k2018-arithmetic-characters, expose.tex lines 341–445,
mathematical source e73d98b1b5c1e5abcdebf7d058e436d792b87982.
Frozen engineering basis 7f86e4a1763cc4ec35e9b0a8acd659750355a0de,
Lean4.34.1/mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothFieldNormality coherentH1 constants)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (ProperStructureCohomologyBaseChange fieldBaseChange structureCohomologyBaseChangeEquiv
    structureCohomologyIso)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/


@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
variable {F : Type u} [Field F]

/-- The actual coherent genus; finiteness is a separate theorem obligation. -/
def coherentGenus (F : Type u) [Field F] (X : FScheme F) : ℕ :=
  Module.finrank F (coherentH1 F X)

theorem coherentGenus_eq_finrank (X : FScheme F) :
    coherentGenus F X = Module.finrank F (coherentH1 F X) := rfl

/- General proper structure-sheaf cohomology finiteness in every degree.
This is the structure-sheaf specialization of Stacks 02O6 (30.19.2), with
properness over a field ensuring Noetherianity and coherence of O_X.
The exact statement and 2023 typographical correction were inspected
2026-10-09. The native `properStructureCohomologyFinite` in
`Aglib.AlgebraicGeometry.Cohomology.Proper.Field`, Aglib revision
197ca0728db3cdf1552a6bcefeeda901e3377862, now supplies this family on the
original constructed objects and structural scalar action. -/

/-- Actual finite-dimensional H¹ for a curve, supplied by native proper
structure-sheaf finiteness with its structural field action. -/
theorem coherentH1_finite (X : FScheme F) (h : Properties X) :
    Module.Finite F (coherentH1 F X) :=
  _root_.AlgebraicGeometry.Scheme.Cohomology.properStructureCohomologyFinite F X 1 h.proper

/- The general constants theorem in arbitrary dimension for proper
geometrically integral field schemes, stated for the actual canonical map.
Stacks 04L2 (33.26.2(4)), reducing to 33.9.3; statement, proof locator and
absence of correction comments inspected 2026-10-09. The native pointwise
constants theorem now supplies this bijection. -/

/-- The constants of an actual curve, with the isomorphism induced by its
structural map. It is not an arbitrarily chosen field identification. -/
def curveConstantsEquiv
    (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
    (X : FScheme F) (h : Properties X) : F ≃+* Γ(X.left, ⊤) :=
  RingEquiv.ofBijective (constants X)
    (@_root_.AlgebraicGeometry.Scheme.constants_bijective_of_proper_geometricallyIntegral
      F _ X h.proper (curveProperties_geometricallyIntegral hnormal hcomp h))

@[simp]
theorem curveConstantsEquiv_apply
    (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
    (X : FScheme F) (h : Properties X) (a : F) :
    curveConstantsEquiv hnormal hcomp X h a = constants X a := rfl

end AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
variable {F : Type u} [Field F] (K : Type u) [Field K] [Algebra F K]
/-- Genus invariance under field extension, for the actual coherent genus. -/
theorem coherentGenus_fieldBaseChange
    (hbase : ProperStructureCohomologyBaseChange.{u})
    (X : FScheme F) (hX : Properties X) :
    coherentGenus K (fieldBaseChange K X) = coherentGenus F X := by
  let : Module.Free F (coherentH1 F X) := Module.Free.of_divisionRing F (coherentH1 F X)
  unfold coherentGenus
  rw [← (structureCohomologyBaseChangeEquiv K hbase X hX.proper 1).finrank_eq]
  exact Module.finrank_baseChange (R := K) (S := F) (M' := coherentH1 F X)

/-- Actual F-scheme isomorphisms preserve coherent genus, with no properness,
normality or base-change premise needed for this invariance statement. -/
theorem coherentGenus_iso {X Y : FScheme F} (e : X ≅ Y) :
    coherentGenus F X = coherentGenus F Y := by
  unfold coherentGenus
  exact (structureCohomologyIso e 1).finrank_eq.symm
end AlgebraicGeometry.Scheme.OverField.Curve

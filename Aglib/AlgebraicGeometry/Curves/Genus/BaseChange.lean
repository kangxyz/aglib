/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Genus
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Coherent genus under every structural field map

Every actual map Spec K → Spec F is Spec of its actual ring map. Installing
that map as the scalar algebra reduces its pullback to the previously built
canonical field base change. This proves genus invariance for all K and all
structural maps s, rather than only one preselected extension presentation.
The only parameter is the unchanged proper structure-cohomology base-change
family (02KH); the H1 object and canonical tensor map remain unchanged.
Application K2-018#prop:k2018-arithmetic-characters, mathematical revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982; engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

open _root_.AlgebraicGeometry.Scheme.Cohomology (ProperStructureCohomologyBaseChange)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
variable {F : Type u} [Field F]
theorem coherentGenus_arbitraryBaseChange
    (hbase : ProperStructureCohomologyBaseChange.{u})
    (X : FScheme F) (hX : Properties X) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Base F) :
    coherentGenus K (Over.mk (pullback.snd X.hom s)) = coherentGenus F X := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  letI : Algebra F K := φ.hom.toAlgebra
  exact coherentGenus_fieldBaseChange K hbase X hX
end AlgebraicGeometry.Scheme.OverField.Curve

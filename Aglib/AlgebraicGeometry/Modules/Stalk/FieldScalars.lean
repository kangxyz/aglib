/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.StalkScalars
public import Aglib.AlgebraicGeometry.ResidueField.StalkScalars
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.RingTheory.Length.ResidueDimension

/-!
# Structural field scalars on module stalks

The field action is the existing native module-stalk action, induced by the
actual structural morphism and its germ. Finite local length at a closed point
of a scheme locally of finite type over the field gives finite field dimension.
Its dimension is the local length multiplied by the actual residue-field degree.
No integrality, Noetherianity, regularity or dimension assumption is used.

These general helpers are extracted from the frozen R5 curve source
`Curves/Picard/Degree/CommonFractionalIdeal.lean` at revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`. The curve degree wrapper remains in
its degree owner; the scalar object and germ formula delegate to the existing
`Scheme.Cohomology` providers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Opposite IsLocalRing

namespace AlgebraicGeometry.Scheme.Modules
universe u
variable (X : Scheme.{u}) {k : Type u} [Field k] (p : X ⟶ Spec (.of k))

/-- The native stalk-module action restricted along the actual structural field map. -/
abbrev stalkBaseModule (M : X.Modules) (x : X) : Module k (M.presheaf.stalk x) :=
  Scheme.Cohomology.nativeModuleStalkModule (Over.mk p) M x

/-- Structural field scalars act compatibly with the local-ring action. -/
theorem stalkBaseTower (M : X.Modules) (x : X) :
    letI := stalkConstantsAlgebra X p x
    letI := stalkBaseModule X p M x
    IsScalarTower k (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  let := stalkConstantsAlgebra X p x
  let := stalkBaseModule X p M x
  refine ⟨?_⟩
  intro a r m
  change (stalkConstants X p x a * r) • m = stalkConstants X p x a • (r • m)
  exact mul_smul _ _ _

/-- The native germ formula for the same structural field action. -/
theorem stalkBaseModule_germ_smul (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (a : k) (s : M.val.obj (op U)) :
    letI := stalkBaseModule X p M x
    a • M.presheaf.germ U x hx s = M.presheaf.germ U x hx
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) • s) :=
  Scheme.Cohomology.nativeModuleStalk_germ_smul (Over.mk p) M x U hx a s

variable [LocallyOfFiniteType p]

/-- Finite local length at a closed point gives finite dimension over the base field. -/
theorem stalkBase_finite (M : X.Modules) (x : X) (hx : IsClosed ({x} : Set X))
    (hM : IsFiniteLength (X.presheaf.stalk x) (M.presheaf.stalk x)) :
    letI := stalkBaseModule X p M x
    Module.Finite k (M.presheaf.stalk x) := by
  let := stalkConstantsAlgebra X p x
  let := stalkBaseModule X p M x
  let := stalkBaseTower X p M x
  let : Module.Finite k (ResidueField (X.presheaf.stalk x)) := residue_finite_from_stalk X p x hx
  exact Module.finite_over_field_of_finite_local_length k (X.presheaf.stalk x)
    (M.presheaf.stalk x) hM

/-- Field dimension is local length times the dimension of the actual residue field. -/
theorem stalkBase_finrank (M : X.Modules) (x : X) (hx : IsClosed ({x} : Set X))
    (hM : IsFiniteLength (X.presheaf.stalk x) (M.presheaf.stalk x)) :
    letI := stalkConstantsAlgebra X p x
    letI := residueAlgebraFromStalk X p x
    letI := stalkBaseModule X p M x
    (Module.finrank k (M.presheaf.stalk x) : ℤ) =
      ((Module.length (X.presheaf.stalk x) (M.presheaf.stalk x)).toNat : ℤ) *
        (Module.finrank k (X.residueField x) : ℤ) := by
  let := stalkConstantsAlgebra X p x
  let := stalkBaseModule X p M x
  let := stalkBaseTower X p M x
  let : Module.Finite k (ResidueField (X.presheaf.stalk x)) := residue_finite_from_stalk X p x hx
  rw [Module.finrank_eq_local_length_mul_residue_finrank k (X.presheaf.stalk x)
    (M.presheaf.stalk x) hM]
  exact Nat.cast_mul _ _

end AlgebraicGeometry.Scheme.Modules

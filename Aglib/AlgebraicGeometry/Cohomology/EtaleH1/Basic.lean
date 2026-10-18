/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Actual small-étale first cohomology

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen
interface basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The object below is exactly mathlib's Ext from the constant `ULift ℤ` sheaf,
not a group-cocycle or Čech replacement. This generic coefficient API applies
to every abelian sheaf. It makes no fundamental-group comparison claim.

Sheaf-value universe `v` and Ext universe `w` are explicit. At arbitrary
universes the library's `HasSheafify` and `HasExt` requirements remain explicit;
these are size/existence requirements, not comparison premises.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleH1

universe u v w

/-- Abelian sheaves on the actual small étale site of `X`. -/
abbrev AbelianSheaf (X : Scheme.{u}) :=
  Sheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{v}

/-- Concrete sheafification is available with values one universe above schemes.
This is proved by mathlib's left-exact plus-plus construction. -/
theorem hasSheafifyLarge (X : Scheme.{u}) :
    HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} := by
  infer_instance

/-- At the standard larger Ext universe, existence is a library theorem and
requires no enough-injectives or comparison premise. -/
theorem hasExtStandard (X : Scheme.{u})
    [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{v}] :
    HasExt.{max (u + 1) (v + 1)} (AbelianSheaf.{u, v} X) :=
  HasExt.standard _

variable (X : Scheme.{u})
variable [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{v}]
variable [HasExt.{w} (AbelianSheaf.{u, v} X)]

/-- Actual Ext-based small-étale H¹, the generic object needed by the finite
comparison and separately by the Gm/Picard application. -/
abbrev H1Etale (L : AbelianSheaf.{u, v} X) : Type w := Sheaf.H L 1

variable {X}

/-- Covariant coefficient change on actual small-étale H¹. -/
def coefficientMap {L M : AbelianSheaf.{u, v} X} (q : L ⟶ M) :
    H1Etale X L →+ H1Etale X M := Sheaf.H.map q 1

@[simp] theorem coefficientMap_id (L : AbelianSheaf.{u, v} X) :
    coefficientMap (𝟙 L) = AddMonoidHom.id (H1Etale X L) := by
  ext a
  exact Sheaf.H.map_id_apply a

@[simp] theorem coefficientMap_comp {L M N : AbelianSheaf.{u, v} X}
    (q : L ⟶ M) (r : M ⟶ N) :
    coefficientMap (q ≫ r) = (coefficientMap r).comp (coefficientMap q) := by
  ext a
  exact Sheaf.H.map_comp_apply q r a

@[simp] theorem coefficientMap_add {L M : AbelianSheaf.{u, v} X}
    (q r : L ⟶ M) :
    coefficientMap (q + r) = coefficientMap q + coefficientMap r := by
  ext a
  exact Sheaf.H.map_add_apply q r a

/-- A sheaf isomorphism induces an additive equivalence on actual H¹. -/
def coefficientIso {L M : AbelianSheaf.{u, v} X} (e : L ≅ M) :
    H1Etale X L ≃+ H1Etale X M where
  toFun := coefficientMap e.hom
  invFun := coefficientMap e.inv
  left_inv a := by
    change Sheaf.H.map e.inv 1 (Sheaf.H.map e.hom 1 a) = a
    rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv a := by
    change Sheaf.H.map e.hom 1 (Sheaf.H.map e.inv 1 a) = a
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  map_add' := (coefficientMap e.hom).map_add

@[simp] theorem coefficientIso_apply {L M : AbelianSheaf.{u, v} X}
    (e : L ≅ M) (a : H1Etale X L) :
    coefficientIso e a = coefficientMap e.hom a := rfl

/-- The degree-one cohomology functor; its maps are `coefficientMap`. -/
abbrev h1Functor : AbelianSheaf.{u, v} X ⥤ AddCommGrpCat.{w} :=
  Sheaf.functorH (Scheme.smallEtaleTopology X) 1

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 5d91a16a4878aaa77f75fe7bb9fb089f5b18b92868f194a89824027155337a57.
Definitions, hypotheses and universes are retained modulo native names. -/

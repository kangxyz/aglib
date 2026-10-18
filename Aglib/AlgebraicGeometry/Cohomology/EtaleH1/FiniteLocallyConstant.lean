/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Pullback

/-!
# Finite locally constant coefficients on the actual small étale site

Definition layer for `K2-018#eq:k2018-pointed-character`, frozen source
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

Local finiteness refers to the values of finite constant sheaves in étale
trivializations. No finiteness of sections over arbitrary test objects is
asserted. The positive annihilator and its invertibility on the scheme are
separate conditions. Representability and the fundamental-group comparison
are not assumed or claimed by these definitions.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u w
attribute [local instance] hasSheafifyLarge

/-- A finite local trivialization consists of an actual jointly surjective
étale family and sheaf isomorphisms to finite constant abelian sheaves. -/
structure FiniteLocalTrivialization {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) where
  /-- The index type of the jointly surjective étale trivializing family. -/
  index : Type u
  /-- The étale chart over `X` at each index. -/
  chart : index → X.Etale
  covers : ∀ x : X, ∃ i, ∃ y : (chart i).left, (chart i).hom y = x
  /-- The finite abelian group of constant values on each chart. -/
  value : index → AddCommGrpCat.{u + 1}
  finite_value : ∀ i, Finite (value i)
  /-- The isomorphism from the inverse image of `L` on each chart to the constant
  abelian sheaf with the specified value. -/
  trivialization : ∀ i, (inverseImage (chart i).hom).obj L ≅
    (constantSheaf (Scheme.smallEtaleTopology (chart i).left) AddCommGrpCat.{u + 1}).obj
      (value i)

/-- Finite local constancy, with finite local values rather than finite section sets. -/
def IsFiniteLocallyConstant {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) : Prop :=
  Nonempty (FiniteLocalTrivialization L)

/-- An isomorphism of coefficients transports the same local trivialization. -/
def FiniteLocalTrivialization.ofIso {X : Scheme.{u}}
    {L M : AbelianSheaf.{u, u + 1} X} (t : FiniteLocalTrivialization L) (e : M ≅ L) :
    FiniteLocalTrivialization M where
  index := t.index
  chart := t.chart
  covers := t.covers
  value := t.value
  finite_value := t.finite_value
  trivialization i := (inverseImage (t.chart i).hom).mapIso e ≪≫ t.trivialization i

/-- Finite local constancy is invariant under actual sheaf isomorphisms. -/
theorem isFiniteLocallyConstant_iff_of_iso {X : Scheme.{u}}
    {L M : AbelianSheaf.{u, u + 1} X} (e : L ≅ M) :
    IsFiniteLocallyConstant L ↔ IsFiniteLocallyConstant M :=
  ⟨fun ⟨t⟩ => ⟨t.ofIso e.symm⟩, fun ⟨t⟩ => ⟨t.ofIso e⟩⟩

/-- Annihilation is equality of actual sheaf morphisms. -/
def KilledBy {X : Scheme.{u}} (n : ℕ) (L : AbelianSheaf.{u, u + 1} X) : Prop :=
  n • (𝟙 L) = 0

/-- The integer is a unit as a global section of the scheme structure sheaf. -/
def LevelInvertible (X : Scheme.{u}) (n : ℕ) : Prop :=
  IsUnit (n : X.presheaf.obj (op ⊤))

/-- Precisely the finite-coefficient scope of the proposed comparison. This
record contains geometric coefficient conditions, never a comparison map. -/
structure FiniteCoefficient {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) where
  /-- The positive integer annihilating `L` and invertible as a global section on `X`. -/
  level : ℕ
  positive : 0 < level
  killed : KilledBy level L
  invertible : LevelInvertible X level
  locally_constant : IsFiniteLocallyConstant L

section Torsion
variable {X : Scheme.{u}}
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

@[simp] theorem coefficientMap_zero {L M : AbelianSheaf.{u, u + 1} X} :
    coefficientMap (0 : L ⟶ M) = 0 := by
  ext a
  simp [coefficientMap, Sheaf.H.map_apply]

@[simp] theorem coefficientMap_nsmul {L M : AbelianSheaf.{u, u + 1} X}
    (n : ℕ) (q : L ⟶ M) : coefficientMap (n • q) = n • coefficientMap q := by
  induction n with
  | zero => simp
  | succ n hn => simp [succ_nsmul, coefficientMap_add, hn]

/-- An annihilator of the coefficient sheaf annihilates its actual Ext H¹. -/
theorem nsmul_h1_eq_zero_of_killedBy {L : AbelianSheaf.{u, u + 1} X}
    {n : ℕ} (h : KilledBy n L) (a : H1Etale X L) : n • a = 0 := by
  have e := congrArg (fun q : L ⟶ L => coefficientMap q a) h
  simpa only [coefficientMap_nsmul, coefficientMap_id,
    AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, coefficientMap_zero,
    AddMonoidHom.zero_apply] using e

end Torsion
end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 0497acb6add32fce2a15b7497c3b8b1ac6c84fd997526f72742b7f962df6b55b.
Definitions, hypotheses and universes are retained modulo native names. -/

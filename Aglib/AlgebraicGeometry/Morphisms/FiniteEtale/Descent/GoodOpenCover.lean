/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineNeighborhoodRepresentation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.RelativeFiniteEtaleGluing

/-!
# GoodOpenCover

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace.Opens
namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation
universe u
variable {X : Scheme.{u}} {F : Scheme.EtaleCohomology.SetSheaf X} (t :
  Scheme.EtaleCohomology.FiniteSetLocalTrivialization F)

/-- Affine opens satisfying `IsGoodAffineOpen` for the sheaf `F`. -/
abbrev GoodOpen := { U : X.Opens // IsGoodAffineOpen F U }

include t in
theorem goodOpen_isBasis : IsBasis {U : X.Opens | IsGoodAffineOpen F U} := by
  rw [isBasis_iff_nbhd]
  intro V x hxV
  obtain ⟨U, hU, hxU⟩ := t.exists_goodAffineOpen x
  obtain ⟨W, hW, hxW, hWU⟩ := isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  exact ⟨W, IsGoodAffineOpen.restrict F hU (hWU.trans inf_le_left) hW, hxW, hWU.trans inf_le_right⟩

/-- The open cover by good affine opens, with coverage supplied by the local trivialization `t`. -/
def goodOpenCover : X.OpenCover where
  I₀ := GoodOpen (F := F)
  X U := U.1.toScheme
  f U := U.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨U, hU, hxU⟩ := t.exists_goodAffineOpen x
    exact ⟨⟨U, hU⟩, ⟨x, hxU⟩, rfl⟩

instance : Preorder (goodOpenCover t).I₀ := inferInstanceAs (Preorder (GoodOpen (F := F)))

instance : (goodOpenCover t).LocallyDirected :=
  .ofIsBasisOpensRange (by intros; simp [goodOpenCover]) (by
    convert goodOpen_isBasis t
    ext U
    simp [goodOpenCover])

@[simp] lemma goodOpenCover_trans {U V : GoodOpen (F := F)} (h : U ≤ V) :
    (goodOpenCover t).trans (homOfLE h) = X.homOfLE h := rfl

/-- A chosen finite-set open representation of `F` on the good affine open `U`. -/
def representative (U : GoodOpen (F := F)) : FiniteSetOpenRepresentation F U.1 :=
  Classical.choice U.2.2

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.GlobalFiniteRepresentation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 7cb4e725caae3c53cf9ed887e9bbd9f920b672c307b75dfc77b13fa0433cc075.
Definitions, hypotheses and universes are retained modulo native names. -/

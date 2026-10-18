/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.StageComparisonIso
public import Aglib.AlgebraicGeometry.FundamentalGroup.FiniteFieldCoverHom

/-!
# RefinedAction

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.ModelActions
universe u
variable {Ω : Type u} [Field Ω] {G R S : PointedScheme Ω}

theorem refinement_inv (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S)
    (e : f = r ≫ v) (A : Scheme.FiniteEtale S.right) :
    (refinementIso r v f e A).inv = ObjectProperty.homMk
      (FieldCoverDescent.overCompIso v.right r.right f.right
        (congrArg (fun t ↦ t.right) e).symm A.obj).hom := by
  subst f
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simp [refinementIso, comparisonIso, FieldCoverDescent.overCompIso]

theorem naturality_of_refinement (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S)
    (e : f = r ≫ v) (aR : FiberAutGroup R.hom) (aS : FiberAutGroup S.hom)
    (ha : pointedMap v aR = aS) (A B : Scheme.FiniteEtale S.right)
    (g : (baseChange v.right).obj A ⟶ (baseChange v.right).obj B)
    (γ : (baseChange f.right).obj A ⟶ (baseChange f.right).obj B)
    (hγ : refinement r v f e A ≫ (baseChange r.right).map g = γ ≫ refinement r v f e B)
    (z : Fiber G.hom ((baseChange f.right).obj A)) :
    (fiberToFinite G.hom).map γ (action f aS A z) =
      action f aS B ((fiberToFinite G.hom).map γ z) := by
  apply refinement_injective r v f e B
  have H (q : Fiber G.hom ((baseChange f.right).obj A)) :
      (fiberToFinite G.hom).map (refinement r v f e B) ((fiberToFinite G.hom).map γ q) =
        (fiberToFinite G.hom).map ((baseChange r.right).map g)
          ((fiberToFinite G.hom).map (refinement r v f e A) q) := by
    exact (ConcreteCategory.congr_hom (congrArg (fiberToFinite G.hom).map hγ) q).symm
  rw [H, refinement_action r v f e aR aS ha, action_naturality,
    ← H, refinement_action r v f e aR aS ha]

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.ModelActions

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 530740fe3b2c6c18259e2532e81d3ba98dfec40ad0c7427134152db58f1405b6.
Definitions, hypotheses and universes are retained modulo native names. -/

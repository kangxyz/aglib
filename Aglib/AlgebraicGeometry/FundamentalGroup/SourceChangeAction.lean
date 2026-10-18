/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.RefinedAction

/-!
# SourceChangeAction

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange baseChangeComp baseChangeId
  fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.ModelActions
universe u
variable {Ω : Type u} [Field Ω] {G R S : PointedScheme Ω}

/-- The equivalence from the fiber over `G` of the `f` -base change to the fiber over `R` of
the `v` -base change, using the supplied factorization `e : f = r ≫ v` and the pointed
fiber equivalence. -/
def sourceFiberEquiv (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S)
    (e : f = r ≫ v) (A : Scheme.FiniteEtale S.right) :
    Fiber G.hom ((baseChange f.right).obj A) ≃ Fiber R.hom ((baseChange v.right).obj A) :=
  (FintypeCat.equivEquivIso.symm ((fiberToFinite G.hom).mapIso (refinementIso r v f e A))).trans
    (pointedFiberEquiv r ((baseChange v.right).obj A)).symm

@[simp] theorem sourceFiberEquiv_apply (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S)
    (e : f = r ≫ v) (A : Scheme.FiniteEtale S.right)
      (z : Fiber G.hom ((baseChange f.right).obj A)) :
    sourceFiberEquiv r v f e A z =
      (pointedFiberEquiv r ((baseChange v.right).obj A)).symm
        ((fiberToFinite G.hom).map (refinement r v f e A) z) := by
  change (pointedFiberEquiv r _).symm ((fiberToFinite G.hom).map
    (refinementIso r v f e A).hom z) = _
  rw [refinementIso_hom]

theorem sourceFiberEquiv_action (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S)
    (e : f = r ≫ v) (a : FiberAutGroup S.hom) (A : Scheme.FiniteEtale S.right)
    (z : Fiber G.hom ((baseChange f.right).obj A)) :
    sourceFiberEquiv r v f e A (action f a A z) =
      action v a A (sourceFiberEquiv r v f e A z) := by
  subst f
  obtain ⟨q, rfl⟩ := (pointedFiberEquiv (r ≫ v) A).surjective z
  simp only [sourceFiberEquiv_apply, refinement, eqToHom_refl, Category.id_comp,
    action, Equiv.symm_apply_apply]
  have H (t : Fiber S.hom A) :
      (pointedFiberEquiv r ((baseChange v.right).obj A)).symm
        ((fiberToFinite G.hom).map (baseChangeComparison r.right v.right A)
          (pointedFiberEquiv (r ≫ v) A t)) = pointedFiberEquiv v A t :=
    (congrArg (pointedFiberEquiv r ((baseChange v.right).obj A)).symm
      (pointedFiberEquiv_comp r v A t)).symm.trans
        ((pointedFiberEquiv r ((baseChange v.right).obj A)).symm_apply_apply _)
  exact (H _).trans (congrArg (fun t ↦ pointedFiberEquiv v A (a.hom.app A t))
    ((congrArg (pointedFiberEquiv v A).symm (H q)).trans
      ((pointedFiberEquiv v A).symm_apply_apply q))).symm

theorem sourceFiberEquiv_naturality (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S)
    (e : f = r ≫ v) (A B : Scheme.FiniteEtale S.right)
    (g : (baseChange v.right).obj A ⟶ (baseChange v.right).obj B)
    (γ : (baseChange f.right).obj A ⟶ (baseChange f.right).obj B)
    (hγ : refinement r v f e A ≫ (baseChange r.right).map g = γ ≫ refinement r v f e B)
    (z : Fiber G.hom ((baseChange f.right).obj A)) :
    sourceFiberEquiv r v f e B ((fiberToFinite G.hom).map γ z) =
      (fiberToFinite R.hom).map g (sourceFiberEquiv r v f e A z) := by
  apply (pointedFiberEquiv r ((baseChange v.right).obj B)).injective
  simp only [sourceFiberEquiv_apply, Equiv.apply_symm_apply]
  rw [← pointEquiv_naturality, Equiv.apply_symm_apply]
  exact (ConcreteCategory.congr_hom (congrArg (fiberToFinite G.hom).map hγ) z).symm

theorem source_change_naturality (r : G ⟶ R) [IsIso r.right]
    (v : R ⟶ S) (f : G ⟶ S) (e : f = r ≫ v) (a : FiberAutGroup S.hom)
    (hnat : ∀ (A B : Scheme.FiniteEtale S.right)
      (g : (baseChange v.right).obj A ⟶ (baseChange v.right).obj B)
      (z : Fiber R.hom ((baseChange v.right).obj A)),
      (fiberToFinite R.hom).map g (action v a A z) =
        action v a B ((fiberToFinite R.hom).map g z))
    (A B : Scheme.FiniteEtale S.right)
    (γ : (baseChange f.right).obj A ⟶ (baseChange f.right).obj B)
    (z : Fiber G.hom ((baseChange f.right).obj A)) :
    (fiberToFinite G.hom).map γ (action f a A z) =
      action f a B ((fiberToFinite G.hom).map γ z) := by
  have : (baseChange r.right).Full := by
    let j := r.right
    let k := inv j
    have hFG : baseChange j ⋙ baseChange k ≅ 𝟭 (Scheme.FiniteEtale R.right) :=
      (baseChangeComp j k).symm ≪≫
        eqToIso (congrArg baseChange (IsIso.inv_hom_id j)) ≪≫ baseChangeId R.right
    have hGF : baseChange k ⋙ baseChange j ≅ 𝟭 (Scheme.FiniteEtale G.right) :=
      (baseChangeComp k j).symm ≪≫
        eqToIso (congrArg baseChange (IsIso.hom_inv_id j)) ≪≫ baseChangeId G.right
    have : (baseChange k).Faithful := Functor.Faithful.of_comp_iso hGF
    exact Functor.Full.of_comp_faithful_iso hFG
  let g := (baseChange r.right).preimage
    ((refinementIso r v f e A).inv ≫ γ ≫ (refinementIso r v f e B).hom)
  have hγ : refinement r v f e A ≫ (baseChange r.right).map g =
      γ ≫ refinement r v f e B := by
    rw [Functor.map_preimage, ← refinementIso_hom, ← refinementIso_hom]
    exact (refinementIso r v f e A).hom_inv_id_assoc _
  apply (sourceFiberEquiv r v f e B).injective
  rw [sourceFiberEquiv_naturality r v f e A B g γ hγ,
    sourceFiberEquiv_action, hnat, ← sourceFiberEquiv_naturality r v f e A B g γ hγ,
    sourceFiberEquiv_action]

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.ModelActions

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 69aaa707e6b4232b3c2781a7e76b97a9ac67824ca9060f9b8e671c7d9851746b.
Definitions, hypotheses and universes are retained modulo native names. -/

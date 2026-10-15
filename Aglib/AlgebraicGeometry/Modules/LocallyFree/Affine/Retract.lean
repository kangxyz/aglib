/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.CategoryTheory.Limits.NatTransCoproduct
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/VectorBundle/AffineRetract.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 85]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Actual finite-free retracts of affine vector bundles

Over an arbitrary commutative ring, finite projectivity of the original global sections yields
a split finite-free surjection. Applying tilde and its original counit gives literal sheaf
retraction maps. Additive functors and natural transformations preserve these retracts.
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ModuleCat.Algebra
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- An affine vector bundle is a retract of a finite free module sheaf. -/
theorem exists_retract_finiteFree (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [IsFiniteLocallyFree (Spec R) M] :
    ∃ (ι : Type u) (_ : Finite ι), Nonempty (Retract M
      (SheafOfModules.free (R := (Spec R).ringCatSheaf) ι)) := by
  classical
  let N := moduleSpecΓFunctor.obj M
  let : Module.Finite R N := finite_globalSections_of_finiteLocallyFree R M
  let : Module.Projective R N := projective_globalSections_of_finiteLocallyFree R M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  let P : ModuleCat R := ModuleCat.of R (Fin n → R)
  let g' : N ⟶ P := ModuleCat.ofHom (X := N) (Y := P) g
  let f' : P ⟶ N := ModuleCat.ofHom (X := P) (Y := N) f
  let b := Module.Free.chooseBasis R P
  let e : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (Module.Free.ChooseBasisIndex R P) ≅ tilde P :=
    (tildeFinsupp _).symm ≪≫ (tilde.functor R).mapIso b.repr.symm.toModuleIso
  let a : tilde N ≅ M := asIso M.fromTildeΓ
  refine ⟨Module.Free.ChooseBasisIndex R P, inferInstance, ⟨{
    i := a.inv ≫ (tilde.functor R).map g' ≫ e.inv
    r := e.hom ≫ (tilde.functor R).map f' ≫ a.hom
    retract := ?_ }⟩⟩
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  have h : g' ≫ f' = 𝟙 N := by
    ext x
    exact congrArg (fun k : N →ₗ[R] N => k x) hg
  rw [h, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
attribute [local instance] Abelian.hasFiniteBiproducts
/-- The original components on affine bundles inherit invertibility from the unit. -/
theorem isIso_app_affineBundle_of_unit_general (R : CommRingCat.{u})
    {D : Type w} [Category.{v} D] [Preadditive D]
    (F G : (Spec R).Modules ⥤ D) [F.Additive] [G.Additive] (α : F ⟶ G)
    [IsIso (α.app (SheafOfModules.unit (Spec R).ringCatSheaf))]
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] : IsIso (α.app M) := by
  obtain ⟨I, hI, ⟨r⟩⟩ := exists_retract_finiteFree R M
  let : Finite I := hI
  have : IsIso (α.app (SheafOfModules.free I)) :=
    NatTrans.isIso_app_coproduct F G α
      (fun (_ : I) => SheafOfModules.unit (Spec R).ringCatSheaf)
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    (α.retractArrowApp r) inferInstance
/-- An additive functor vanishing on the structure module vanishes on every affine bundle. -/
theorem isZero_obj_affineBundle_of_unit (R : CommRingCat.{u})
    {D : Type w} [Category.{v} D] [Preadditive D]
    (F : (Spec R).Modules ⥤ D) [F.Additive]
    (h : IsZero (F.obj (SheafOfModules.unit (Spec R).ringCatSheaf)))
    (M : (Spec R).Modules) [IsFiniteLocallyFree (Spec R) M] : IsZero (F.obj M) := by
  obtain ⟨I, hI, ⟨r⟩⟩ := exists_retract_finiteFree R M
  let : Finite I := hI
  have hf : IsZero (F.obj (SheafOfModules.free I)) := by
    rw [IsZero.iff_id_eq_zero]
    apply (isColimitOfPreserves F
      (SheafOfModules.isColimitFreeCofan (R := (Spec R).ringCatSheaf) I)).hom_ext
    intro i
    exact h.eq_of_src _ _
  rw [IsZero.iff_id_eq_zero, ← (r.map F).retract]
  rw [hf.eq_of_tgt (r.map F).i 0, zero_comp]
end AlgebraicGeometry.Scheme.Modules

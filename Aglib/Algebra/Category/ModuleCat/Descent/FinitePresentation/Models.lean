/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.BaseChange
public import Aglib.Algebra.Category.ModuleCat.FiniteMatrixBaseChange
public import Aglib.Algebra.Category.Ring.Descent.FinitePresentation.Models
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Finite-stage models of finitely presented modules

Finite presentation matrices over an actual filtered ring colimit lift to a
common stage above any prescribed stage. Their actual cokernels give finitely
presented module models. The comparison is the native extension-of-scalars
cokernel comparison and the specified colimit ring map; no injectivity or
Noetherianity hypothesis is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Limits TensorProduct
open scoped Matrix

namespace ModuleCat

/-- The actual cokernel of a finite-free linear map commutes with the
specified extension of scalars. The target map is its original matrix with
that same ring homomorphism applied to every coefficient. -/
def extendScalarsCokernelPiIso {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {m n : ℕ} (g : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (extendScalars φ).obj (ModuleCat.of R ((Fin n → R) ⧸ LinearMap.range g)) ≅
      ModuleCat.of S ((Fin n → S) ⧸
        LinearMap.range ((LinearMap.toMatrix' g).map φ).mulVecLin) := by
  let E := extendScalars φ
  have : E.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).isLeftAdjoint
  let f := ModuleCat.ofHom g
  let f' := ModuleCat.ofHom ((LinearMap.toMatrix' g).map φ).mulVecLin
  exact E.mapIso (cokernelIsoRangeQuotient f).symm ≪≫
    PreservesCokernel.iso E f ≪≫
    cokernel.mapIso (E.map f) f' (extendScalarsPiIso φ m) (extendScalarsPiIso φ n)
      (extendScalarsPiIso_map φ g) ≪≫
    cokernelIsoRangeQuotient f'

end ModuleCat

private theorem finitePresentation_quotient_range
    {R : Type u} [CommRing R] {m n : ℕ}
    (g : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Module.FinitePresentation R ((Fin n → R) ⧸ LinearMap.range g) := by
  apply Module.finitePresentation_of_surjective (LinearMap.range g).mkQ
    (LinearMap.range g).mkQ_surjective
  rw [Submodule.ker_mkQ]
  exact Submodule.fg_range g

namespace Module.FinitePresentation

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)

include hc in
/-- Every finitely presented module over a filtered ring colimit has an
actual finitely presented model above any prescribed stage. The displayed
linear equivalence uses the specified colimit cocone map. -/
theorem exists_model_above_of_isColimit (i₀ : I) (M : Type v)
    [AddCommGroup M] [Module c.pt M] [Module.FinitePresentation c.pt M] :
    ∃ (j : I) (_ : i₀ ⟶ j) (N : Type u) (_ : AddCommGroup N) (_ : Module (F.obj j) N),
      Module.FinitePresentation (F.obj j) N ∧
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj j] N ≃ₗ[c.pt] M) := by
  classical
  obtain ⟨n, m, p, g, hp, hgp⟩ := Module.FinitePresentation.exists_fin' c.pt M
  let A := LinearMap.toMatrix' g
  obtain ⟨i, hi⟩ := CommRingCat.exists_finite_subset_range_ι_app F c hc
    (Set.range fun z : Fin n × Fin m ↦ A z.1 z.2) (Set.finite_range _)
  choose b hb using fun z : Fin n × Fin m ↦ hi (Set.mem_range_self z)
  let j := IsFiltered.max i₀ i
  let q : i ⟶ j := IsFiltered.rightToMax i₀ i
  let B : Matrix (Fin n) (Fin m) (F.obj j) := fun r s ↦ F.map q (b (r, s))
  have hB : B.map (c.ι.app j).hom = A := by
    ext r s
    change (F.map q ≫ c.ι.app j) (b (r, s)) = A r s
    rw [c.w]
    exact hb (r, s)
  let gⱼ : (Fin m → F.obj j) →ₗ[F.obj j] (Fin n → F.obj j) := Matrix.toLin' B
  let N := (Fin n → F.obj j) ⧸ LinearMap.range gⱼ
  have hN : Module.FinitePresentation (F.obj j) N := finitePresentation_quotient_range gⱼ
  let : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  have hg : ((LinearMap.toMatrix' gⱼ).map (c.ι.app j).hom).mulVecLin = g := by
    change ((LinearMap.toMatrix' (Matrix.toLin' B)).map (c.ι.app j).hom).mulVecLin = g
    rw [LinearMap.toMatrix'_toLin', hB]
    apply LinearMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec g x
  let e := ModuleCat.extendScalarsCokernelPiIso (S := c.pt) (c.ι.app j).hom gⱼ
  let e' : ((Fin n → c.pt) ⧸
      LinearMap.range ((LinearMap.toMatrix' gⱼ).map (c.ι.app j).hom).mulVecLin) ≃ₗ[c.pt]
      ((Fin n → c.pt) ⧸ LinearMap.range g) :=
    Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range hg)
  refine ⟨j, IsFiltered.leftToMax i₀ i, N, inferInstance, inferInstance, hN, ?_⟩
  let eTensor : c.pt ⊗[F.obj j] N ≃ₗ[c.pt]
      (ModuleCat.extendScalars (c.ι.app j).hom).obj (ModuleCat.of (F.obj j) N) :=
    (ModuleCat.extendScalarsAlgebraIso (F.obj j) c.pt
      (ModuleCat.of (F.obj j) N)).symm.toLinearEquiv
  let eMatrix :
      (ModuleCat.extendScalars (c.ι.app j).hom).obj (ModuleCat.of (F.obj j) N) ≃ₗ[c.pt]
      ((Fin n → c.pt) ⧸
        LinearMap.range ((LinearMap.toMatrix' gⱼ).map (c.ι.app j).hom).mulVecLin) :=
    e.toLinearEquiv
  let ePresentation : ((Fin n → c.pt) ⧸ LinearMap.range g) ≃ₗ[c.pt] M :=
    hgp.linearEquivOfSurjective hp
  exact ⟨eTensor.trans (eMatrix.trans (e'.trans ePresentation))⟩

include hc in
/-- Every finitely presented module over an actual filtered ring colimit
is a scalar extension of a finitely presented module at one stage. -/
theorem exists_model_of_isColimit (M : Type v) [AddCommGroup M]
    [Module c.pt M] [Module.FinitePresentation c.pt M] :
    ∃ (j : I) (N : Type u) (_ : AddCommGroup N) (_ : Module (F.obj j) N),
      Module.FinitePresentation (F.obj j) N ∧
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj j] N ≃ₗ[c.pt] M) := by
  obtain ⟨j, q, N, hN, hmod, hfp, e⟩ :=
    exists_model_above_of_isColimit F c hc IsFiltered.nonempty.some M
  exact ⟨j, N, hN, hmod, hfp, e⟩

end Module.FinitePresentation

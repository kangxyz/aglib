/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Ext.Coefficients
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Localization of original top Koszul Ext in the coefficient

Native Yoneda postcomposition by an original module-localization map is a
localization on the top Ext of a finite weakly regular quotient. The proof
uses the same original Koszul class and coefficient quotient equivalence,
and Mathlib's localization of an actual quotient module. No coefficient
regularity, flatness, finiteness or Noetherian hypothesis is required.

The base ring and quotient source stay fixed in this statement. Change of
base ring, determinant changes of generators and geometric sheaf purity
remain separate consumers. The coefficient carriers share the ring universe;
the supported Ext size is independent. No localized scalar action is added
to the public interface or installed as a new instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace ChainComplex.Koszul
variable {R : Type u} [CommRing R] (T : Submonoid R)
  {N N' : ModuleCat.{u} R}
  (g : N ⟶ N') [IsLocalizedModule T g.hom]

private theorem quotientIdealMap_isLocalizedModule (I : Ideal R) :
    IsLocalizedModule T (((I • (⊤ : Submodule R N)).mapQ
      (I • (⊤ : Submodule R N')) g.hom
        (Submodule.smul_top_le_comap_smul_top I g.hom))) := by
  let : Module (Localization T) N' := IsLocalizedModule.module T g.hom
  let : IsScalarTower R (Localization T) N' :=
    IsLocalizedModule.isScalarTower_module T g.hom
  let P : Submodule R N := I • ⊤
  let P' : Submodule (Localization T) N' := P.localized' (Localization T) T g.hom
  have hP : P'.restrictScalars R = I • (⊤ : Submodule R N') := by
    dsimp only [P', P]
    rw [Submodule.restrictScalars_localized', Submodule.localized₀_smul,
      Submodule.localized₀_top]
  let e : (N' ⧸ P') ≃ₗ[R] N' ⧸ (I • (⊤ : Submodule R N')) :=
    (Submodule.Quotient.restrictScalarsEquiv R P').symm.trans
      (Submodule.quotEquivOfEq _ _ hP)
  let q := P.toLocalizedQuotient' (Localization T) T g.hom
  let : IsLocalizedModule T q := by dsimp only [q]; infer_instance
  have heq : (I • (⊤ : Submodule R N)).mapQ
        (I • (⊤ : Submodule R N')) g.hom
        (Submodule.smul_top_le_comap_smul_top I g.hom) = e.toLinearMap.comp q := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective P x
    change Submodule.Quotient.mk (g m) = e (q (Submodule.Quotient.mk m))
    simp [e, q]
  rw [heq]
  exact IsLocalizedModule.of_linearEquiv T q e

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- Native Yoneda postcomposition by an original coefficient localization map
localizes the top Ext of a weakly regular quotient. -/
theorem topExtPostcomp_isLocalizedModule (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    IsLocalizedModule T
      ((Ext.mk₀ g).postcompOfLinear R (ModuleCat.of R (R ⧸ Ideal.ofList s))
        (add_zero s.length)) := by
  let e := topExtLinearEquiv.{u,w} s hs N
  let e' := topExtLinearEquiv.{u,w} s hs N'
  let q := ((Ideal.ofList s) • (⊤ : Submodule R N)).mapQ
    ((Ideal.ofList s) • (⊤ : Submodule R N')) g.hom
      (Submodule.smul_top_le_comap_smul_top (Ideal.ofList s) g.hom)
  let : IsLocalizedModule T q := quotientIdealMap_isLocalizedModule T g (Ideal.ofList s)
  let : IsLocalizedModule T (q.comp e.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right T q e.symm
  have hloc : IsLocalizedModule T (e'.toLinearMap.comp (q.comp e.symm.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv T (q.comp e.symm.toLinearMap) e'
  have heq : (Ext.mk₀ g).postcompOfLinear R (ModuleCat.of R (R ⧸ Ideal.ofList s))
        (add_zero s.length) = e'.toLinearMap.comp (q.comp e.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := topExtClass_surjective s hs N x
    have he : e.symm (topExtClass s hs N m) = Submodule.Quotient.mk m := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      exact (topExtLinearEquiv_apply_mk s hs N m).symm
    change (topExtClass s hs N m).comp (Ext.mk₀ g) (add_zero s.length) =
      e' (q (e.symm (topExtClass s hs N m)))
    rw [he]
    have hq : q (Submodule.Quotient.mk m) = Submodule.Quotient.mk (g m) := rfl
    rw [hq, topExtClass_comp_mk₀]
    exact (topExtLinearEquiv_apply_mk s hs N' (g m)).symm
  rw [heq]
  exact hloc

end ChainComplex.Koszul

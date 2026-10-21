/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.PresentationExt
public import Aglib.Algebra.Category.ModuleCat.BaseChange

/-! # Compatibility of scalar-extended presentations on original unit tensors -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable {B R S : Type u} [CommRing B] [CommRing R] [CommRing S]
  (b : B →+* R) (φ : R →+* S)
  {L : ModuleCat.{max u v} B} {M N : ModuleCat.{max u v} R}
  {M' N' : ModuleCat.{max u v} S}

/-- The original scalar-extended presentation square. The named predicate keeps
its source presentation fixed at specialization boundaries. -/
def extendScalarsPresentationCompatible
    (_e : M ≅ (extendScalars b).obj L)
    (q : M ⟶ N) (q' : M' ⟶ N')
    (d : (extendScalars φ).obj N ⟶ N')
    (a : (extendScalars φ).obj M ⟶ M') : Prop :=
  (extendScalars φ).map q ≫ d = a ≫ q'

/-- Four original unit equations suffice for the entire presentation square.
No linearity of the auxiliary coordinate functions is required. -/
theorem extendScalarsPresentationCompatible_of_unit_equations
    (e : M ≅ (extendScalars b).obj L)
    (q : M ⟶ N) (q' : M' ⟶ N')
    (d : (extendScalars φ).obj N ⟶ N')
    (a : (extendScalars φ).obj M ⟶ M')
    (i : L → N) (j : L → N') (t : L → M')
    (hq : ∀ m, q (e.inv ((1 : R) ⊗ₜ[B,b] m)) = i m)
    (hd : ∀ m, d ((1 : S) ⊗ₜ[R,φ] i m) = j m)
    (ha : ∀ m, a ((1 : S) ⊗ₜ[R,φ] e.inv ((1 : R) ⊗ₜ[B,b] m)) = t m)
    (hq' : ∀ m, q' (t m) = j m) :
    extendScalarsPresentationCompatible b φ e q q' d a := by
  apply extendScalars_hom_ext_of_presentation b φ e
  intro m
  simp only [comp_apply, ExtendScalars.map_tmul]
  rw [hq, hd, ha, hq']

/-- Native algebra-tensor presentation compatibility with the same original maps. -/
def algebraTensorPresentationCompatible [Algebra B R]
    {L : ModuleCat.{u} B} {M N : ModuleCat.{u} R}
    {M' N' : ModuleCat.{u} S}
    (_e : M ≅ ModuleCat.of R (R ⊗[B] L))
    (q : M ⟶ N) (q' : M' ⟶ N')
    (d : (extendScalars φ).obj N ⟶ N')
    (a : (extendScalars φ).obj M ⟶ M') : Prop :=
  (extendScalars φ).map q ≫ d = a ≫ q'

/-- The native algebra-tensor form normalizes the scalar-extension coordinate
isomorphism only in the abstract supplier. -/
theorem algebraTensorPresentationCompatible_of_unit_equations [Algebra B R]
    {L : ModuleCat.{u} B} {M N : ModuleCat.{u} R}
    {M' N' : ModuleCat.{u} S}
    (e : M ≅ ModuleCat.of R (R ⊗[B] L))
    (q : M ⟶ N) (q' : M' ⟶ N')
    (d : (extendScalars φ).obj N ⟶ N')
    (a : (extendScalars φ).obj M ⟶ M')
    (i : L → N) (j : L → N') (t : L → M')
    (hq : ∀ m, q (e.inv ((1 : R) ⊗ₜ[B] m)) = i m)
    (hd : ∀ m, d ((1 : S) ⊗ₜ[R,φ] i m) = j m)
    (ha : ∀ m, a ((1 : S) ⊗ₜ[R,φ] e.inv ((1 : R) ⊗ₜ[B] m)) = t m)
    (hq' : ∀ m, q' (t m) = j m) :
    algebraTensorPresentationCompatible φ e q q' d a := by
  apply extendScalars_hom_ext_of_presentation (algebraMap B R) φ
    (e ≪≫ (extendScalarsAlgebraIso B R L).symm)
  intro m
  simp only [Iso.trans_inv, Iso.symm_inv, comp_apply,
    ExtendScalars.map_tmul]
  erw [extendScalarsAlgebraIso_tmul]
  rw [hq, hd, ha, hq']

end ModuleCat

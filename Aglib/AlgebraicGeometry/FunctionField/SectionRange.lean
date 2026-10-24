/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Regular sections inside the original function field

On a nonempty open of an integral scheme, a function-field element comes
from an original section if and only if it comes from every point stalk
on that open. The reverse implication glues actual representatives of
those germs. No normality, affineness or Noetherian hypothesis is used.

This extracts the sheaf-gluing argument underlying
`Properties.Normal.GlobalSections` without modifying that existing owner.
The current consumer is the original field-trace construction on arbitrary
opens of a normal integral scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- A rational function on a nonempty original open is an actual section
exactly when it is represented in every original point stalk there. -/
theorem mem_range_germToFunctionField_iff_stalk
    (U : X.Opens) [hU : Nonempty U] (f : X.functionField) :
    f ∈ Set.range (X.germToFunctionField U) ↔
      ∀ x : U, f ∈ Set.range (algebraMap (X.presheaf.stalk x.val) X.functionField) := by
  constructor
  · rintro ⟨s, rfl⟩ x
    exact ⟨X.presheaf.germ U x.val x.property s,
      algebraMap_germ_eq_germToFunctionField X x.property s⟩
  · intro h
    choose r hr using h
    choose V hx s hs using fun x => X.presheaf.exists_germ_eq (r x)
    let W (x : U) := V x ⊓ U
    let t (x : U) : Γ(X, W x) := X.presheaf.map ((V x).infLELeft U).op (s x)
    let (x : U) : Nonempty (W x) := ⟨⟨x.val, hx x, x.property⟩⟩
    let (x : U) : Nonempty (V x) := ⟨⟨x.val, hx x⟩⟩
    have he (x : U) : X.germToFunctionField (W x) (t x) = f := by
      rw [← algebraMap_germ_eq_germToFunctionField X
        (show x.val ∈ W x from ⟨hx x, x.property⟩)]
      change algebraMap (X.presheaf.stalk x.val) X.functionField
        (X.presheaf.germ (W x) x.val _
          (X.presheaf.map ((V x).infLELeft U).op (s x))) = f
      rw [X.presheaf.germ_res_apply, hs, hr]
    have heV (x : U) : X.germToFunctionField (V x) (s x) = f := by
      rw [← algebraMap_germ_eq_germToFunctionField X (hx x), hs, hr]
    have hc : TopCat.Presheaf.IsCompatible X.presheaf W t := by
      intro x y
      apply TopCat.Presheaf.section_ext X.sheaf
      intro z hz
      change X.presheaf.germ (W x ⊓ W y) z hz
        (X.presheaf.map ((W x).infLELeft (W y)).op (t x)) =
        X.presheaf.germ (W x ⊓ W y) z hz
          (X.presheaf.map ((W x).infLERight (W y)).op (t y))
      apply IsFractionRing.injective (X.presheaf.stalk z) X.functionField
      simp only [t, W, X.presheaf.germ_res_apply]
      rw [algebraMap_germ_eq_germToFunctionField X hz.1.1,
        algebraMap_germ_eq_germToFunctionField X hz.2.1, heV, heV]
    have hcover : U ≤ iSup W := by
      intro x hxU
      exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx _, hxU⟩
    obtain ⟨g, hg, _⟩ := X.sheaf.existsUnique_gluing' W U
      (fun _ => homOfLE inf_le_right) hcover t hc
    refine ⟨g, ?_⟩
    let x := hU.some
    let : Nonempty (W x) := ⟨⟨x.val, hx x, x.property⟩⟩
    let i : W x ⟶ U := homOfLE inf_le_right
    have hgx : X.presheaf.map i.op g = t x := hg x
    have hxg : genericPoint X ∈ W x :=
      ((genericPoint_spec X).mem_open_set_iff (W x).isOpen).mpr
        (by simpa using (inferInstance : Nonempty (W x)))
    have hres : X.germToFunctionField (W x) (X.presheaf.map i.op g) =
        X.germToFunctionField U g :=
      X.presheaf.germ_res_apply i (genericPoint X) hxg g
    change X.germToFunctionField U g = f
    exact hres.symm.trans ((congrArg (X.germToFunctionField (W x)) hgx).trans (he x))

/-- The section ring's original image is the intersection of the original
stalk images in the same function field. -/
theorem range_germToFunctionField_eq_iInter_stalks (U : X.Opens) [Nonempty U] :
    Set.range (X.germToFunctionField U) =
      ⋂ x : U, Set.range (algebraMap (X.presheaf.stalk x.val) X.functionField) := by
  ext f
  exact (mem_range_germToFunctionField_iff_stalk X U f).trans Set.mem_iInter.symm

end AlgebraicGeometry.Scheme

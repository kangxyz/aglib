/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Sections of normal integral schemes

`Aglib.AlgebraicGeometry.Properties.Normal.GlobalSections` proves integral closedness of
the actual section ring on any nonempty open of an integral scheme with normal stalks.
The proof uses the canonical maps to the actual function field and structure-sheaf gluing.
No affineness, Noetherianity or properness hypothesis is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual sections on a nonempty open are integrally closed in the function field if
the stalks at its points are integrally closed. This does not assert that the function field
is the fraction field of the section ring. -/
theorem isIntegrallyClosedIn_functionField_sections (U : X.Opens) [hU : Nonempty U]
    (hNormal : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val)) :
    IsIntegrallyClosedIn Γ(X, U) X.functionField := by
  refine isIntegrallyClosedIn_iff.mpr
    ⟨X.germToFunctionField_injective U, fun {f} hf => ?_⟩
  have hstalk (x : U) : ∃ r : X.presheaf.stalk x.val,
      algebraMap (X.presheaf.stalk x.val) X.functionField r = f := by
    let : IsIntegrallyClosed (X.presheaf.stalk x.val) := hNormal x
    let : Algebra Γ(X, U) (X.presheaf.stalk x.val) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf x
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hf.tower_top
  choose r hr using hstalk
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

/-- Any nonempty open of an integral scheme with integrally closed stalks has an
integrally closed section ring. Normality is needed only at the points of this open. -/
theorem isIntegrallyClosed_sections (U : X.Opens) [Nonempty U]
    (hNormal : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val)) :
    IsIntegrallyClosed Γ(X, U) := by
  let : FaithfulSMul Γ(X, U) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective Γ(X, U) X.functionField).mpr
      (X.germToFunctionField_injective U)
  let : IsIntegrallyClosedIn Γ(X, U) X.functionField :=
    X.isIntegrallyClosedIn_functionField_sections U hNormal
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn Γ(X, U) X.functionField

/-- Global sections of a normal integral scheme are integrally closed, on the actual
structure-sheaf section ring. -/
theorem NormalStalks.isIntegrallyClosed_globalSections (hNormal : NormalStalks X) :
    IsIntegrallyClosed Γ(X, ⊤) := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact X.isIntegrallyClosed_sections ⊤ fun x => (hNormal x.val).2

end AlgebraicGeometry.Scheme

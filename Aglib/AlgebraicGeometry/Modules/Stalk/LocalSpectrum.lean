/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Global sections and the closed stalk on a local spectrum

Every open neighbourhood of the closed point of a local spectrum is the whole
spectrum. Consequently the actual germ map is an equivalence for every module
sheaf, without quasicoherence or finiteness assumptions. The scalar action is
restricted along the inverse of the native closed-point stalk ring isomorphism.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable (R : CommRingCat.{u}) [IsLocalRing R]

/-- The original top germ at the closed point is bijective, even for a module
sheaf which is not quasicoherent. -/
theorem germ_closedPoint_bijective (M : (Spec R).Modules) :
    Function.Bijective (M.presheaf.germ ⊤ (closedPoint R) trivial) := by
  constructor
  · intro s t h
    obtain ⟨U, hx, i, j, hst⟩ :=
      M.presheaf.germ_eq (U := ⊤) (V := ⊤) (closedPoint R) trivial trivial s t h
    have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hx
    subst U
    have hi : i = 𝟙 _ := Subsingleton.elim _ _
    have hj : j = 𝟙 _ := Subsingleton.elim _ _
    simpa [hi, hj] using hst
  · intro t
    obtain ⟨U, hx, s, rfl⟩ := M.presheaf.exists_germ_eq t
    have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hx
    subst U
    exact ⟨s, rfl⟩

/-- The actual top germ, linear for the canonical local-ring identification. -/
def localSpectrumSectionsToStalk (M : (Spec R).Modules) :
    moduleSpecΓFunctor.obj M ⟶
      (ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom).obj
        ((moduleStalk (Spec R) (closedPoint R)).obj M) := ModuleCat.ofHom
  (X := moduleSpecΓFunctor.obj M)
  (Y := (ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom).obj
    ((moduleStalk (Spec R) (closedPoint R)).obj M))
  { toFun := fun s => M.presheaf.germ ⊤ (closedPoint R) trivial s
    map_add' := map_add (M.presheaf.germ ⊤ (closedPoint R) trivial).hom
    map_smul' := by
      intro a s
      change M.presheaf.germ ⊤ (closedPoint R) trivial
        ((Scheme.ΓSpecIso R).inv a • (show Γ(M, ⊤) from s)) = (stalkClosedPointIso R).inv a • _
      erw [_root_.PresheafOfModules.germ_smul M.val (closedPoint R) ⊤ trivial]
      congr 1
      change (Spec R).presheaf.germ ⊤ (closedPoint R) trivial
        ((Scheme.ΓSpecIso R).inv a) = (stalkClosedPointIso R).inv a
      have h := ConcreteCategory.congr_hom (ΓSpecIso_hom_stalkClosedPointIso_inv R)
        ((Scheme.ΓSpecIso R).inv a)
      simpa using h.symm }

/-- Sections are the closed stalk via the original germ, with its actual
structural scalar action. -/
def localSpectrumSectionsStalkIso (M : (Spec R).Modules) :
    moduleSpecΓFunctor.obj M ≅
      (ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom).obj
        ((moduleStalk (Spec R) (closedPoint R)).obj M) :=
  (LinearEquiv.ofBijective (localSpectrumSectionsToStalk R M).hom
    (germ_closedPoint_bijective R M)).toModuleIso

@[simp]
theorem localSpectrumSectionsStalkIso_hom_apply (M : (Spec R).Modules)
    (s : moduleSpecΓFunctor.obj M) :
    (localSpectrumSectionsStalkIso R M).hom s =
      M.presheaf.germ ⊤ (closedPoint R) trivial s := rfl

/-- Naturality uses the actual induced map on stalks. -/
theorem localSpectrumSectionsToStalk_naturality {M N : (Spec R).Modules} (f : M ⟶ N) :
    moduleSpecΓFunctor.map f ≫ localSpectrumSectionsToStalk R N =
      localSpectrumSectionsToStalk R M ≫
        (ModuleCat.restrictScalars (stalkClosedPointIso R).inv.hom).map
          ((moduleStalk (Spec R) (closedPoint R)).map f) := by
  ext s
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤
    (closedPoint R) trivial f.mapPresheaf s).symm

end AlgebraicGeometry.Scheme.Modules

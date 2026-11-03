/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Epimorphisms from the structure module on an integral scheme

An epimorphism from the actual structure module to an arbitrary module sheaf
with nonzero generic stalk is an isomorphism. No quasicoherence, finite type,
finite presentation or local freeness is needed. The proof retains the original
section and stalk maps: multiplication by the original global section is
injective on the generic stalk, and integral ring germs detect its kernel.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

/-- The germ of an original unit-module morphism is multiplication by the germ
of its original global section. -/
theorem germ_unitHom_app (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (x : X) (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    M.presheaf.germ U x hx (Scheme.Modules.Hom.app φ U r) =
      X.presheaf.germ U x hx r •
        M.presheaf.germ ⊤ x (by trivial) (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) := by
  have he := unitHomGlobalSectionsEquiv_symm_app X M
    (unitHomGlobalSectionsEquiv X M φ) U r
  rw [Equiv.symm_apply_apply, unitHomGlobalSectionsEquiv_apply] at he
  rw [he]
  have hs : M.presheaf.germ U x hx
      (r • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤)))) =
      X.presheaf.germ U x hx r • M.presheaf.germ U x hx
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤)))) :=
    PresheafOfModules.germ_smul M.val x U hx r _
  exact hs.trans (congrArg (fun z : M.presheaf.stalk x => X.presheaf.germ U x hx r • z)
    (M.presheaf.germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) x hx
      (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤)))))

/-- An epimorphic unit-module morphism has nonzero generator germ at every
point of the actual target support. -/
theorem germ_unitHom_one_ne_zero_of_epi
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) [Epi φ]
    (x : X) (hx : x ∈ support M) :
    M.presheaf.germ ⊤ x (by trivial) (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) ≠ 0 := by
  intro h
  have hs : Function.Surjective ((moduleStalk X x).map φ) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hz : ∀ m : M.presheaf.stalk x, m = 0 := by
    intro m
    obtain ⟨s, hs⟩ := hs m
    obtain ⟨U, hxU, r, rfl⟩ :=
      (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).exists_germ_eq s
    rw [← hs]
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (Scheme.Modules.Hom.mapPresheaf φ)
      ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).germ
        U x hxU r) = 0
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change M.presheaf.germ U x hxU (Scheme.Modules.Hom.app φ U r) = 0
    rw [germ_unitHom_app, h, smul_zero]
  exact hx ((AddCommGrpCat.isZero_iff_subsingleton).mpr
    ⟨fun a b => (hz a).trans (hz b).symm⟩)

/-- A unit-module morphism with nonzero generator germ at the generic point
of an integral scheme is a monomorphism. -/
theorem mono_unitHom_of_generic_germ_ne_zero [IsIntegral X]
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (hφ : M.presheaf.germ ⊤ (genericPoint X) (by trivial)
      (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) ≠ 0) : Mono φ := by
  apply moduleHom_mono_of_app_injective
  intro U
  rw [injective_iff_map_eq_zero]
  intro r hr
  change Γ(X, U) at r
  apply TopCat.Presheaf.section_ext X.sheaf U r 0
  intro x hx
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
  have hsmul : X.presheaf.germ U (genericPoint X) hη r •
      M.presheaf.germ ⊤ (genericPoint X) (by trivial)
        (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) = 0 := by
    rw [← germ_unitHom_app, hr, map_zero]
  have hzero : X.presheaf.germ U (genericPoint X) hη r = 0 :=
    (smul_eq_zero.mp hsmul).resolve_right hφ
  have hrzero : r = 0 := (germ_injective_of_isIntegral X (genericPoint X) hη)
    (hzero.trans (X.presheaf.germ U (genericPoint X) hη).hom.map_zero.symm)
  exact congrArg (X.presheaf.germ U x hx) hrzero

/-- On an integral scheme, an epimorphism from the actual structure module
to a sheaf with nonzero generic stalk is the original isomorphism. -/
theorem isIso_unitHom_of_epi_of_generic_mem_support [IsIntegral X]
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) [Epi φ]
    (hM : genericPoint X ∈ support M) : IsIso φ := by
  let : Mono φ := mono_unitHom_of_generic_germ_ne_zero φ
    (germ_unitHom_one_ne_zero_of_epi φ (genericPoint X) hM)
  exact isIso_of_mono_of_epi φ

end AlgebraicGeometry.Scheme.Modules

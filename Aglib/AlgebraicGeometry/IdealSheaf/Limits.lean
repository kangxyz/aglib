/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Diagrams

/-!
# Actual limits of closed subschemes from suprema of ideals

The closed subscheme of a supremum is the limit, in the over category, of the
original diagram of closed subschemes. The universal property is obtained from
the general native closed-subscheme diagram theorem. The comparison preserves
the actual ideal inclusions. For a connected diagram the same cone is limiting
in schemes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- Maps over the ambient scheme into the same closed subscheme are equal. -/
theorem hom_ext_subscheme {T : Over X} (I : X.IdealSheafData)
    (f g : T ⟶ Over.mk I.subschemeι) : f = g := by
  apply (Over.forget X).map_injective
  change f.left = g.left
  apply (cancel_mono I.subschemeι).mp
  exact (Over.w f).trans (Over.w g).symm

/-- The actual closed-subscheme cone with supremum ideal as its apex. -/
def subschemeSupCone (F : C ⥤ (X.IdealSheafData)ᵒᵖ) :
    Cone (F ⋙ subschemeFunctor X) where
  pt := Over.mk (⨆ c, (F.obj c).unop).subschemeι
  π :=
    { app c := Over.homMk (inclusion (le_iSup (fun c => (F.obj c).unop) c))
      naturality c d f := hom_ext_subscheme (F.obj d).unop _ _ }

/-- The ideal of the apex of the actual cone lies in the kernel of every test
cone's structural morphism. -/
theorem iSup_le_ker_of_subschemeCone (F : C ⥤ (X.IdealSheafData)ᵒᵖ)
    (s : Cone (F ⋙ subschemeFunctor X)) :
    (⨆ c, (F.obj c).unop) ≤ s.pt.hom.ker := by
  apply iSup_le
  intro c
  have h := Scheme.Hom.le_ker_comp (s.π.app c).left (F.obj c).unop.subschemeι
  have hw : (s.π.app c).left ≫ (F.obj c).unop.subschemeι = s.pt.hom :=
    Over.w (s.π.app c)
  rw [ker_subschemeι, hw] at h
  exact h

/-- The supremum cone is an actual limit in the over category, without
quasicompactness, finite generation, or connectedness assumptions. -/
def subschemeSupConeIsLimit (F : C ⥤ (X.IdealSheafData)ᵒᵖ) :
    IsLimit (subschemeSupCone F) := by
  let I := ⨆ c, (F.obj c).unop
  have hI : (⨆ c, (F.obj c).unop) = I.subschemeι.ker := by
    rw [ker_subschemeι]
  exact (ClosedSubscheme.isLimitIdealCone F I.subschemeι hI).ofIsoLimit
    (Cone.ext (Iso.refl _) (fun c => hom_ext_subscheme (F.obj c).unop _ _))

/-- The same actual supremum cone, with its structural maps forgotten. -/
def subschemeSupSchemeCone (F : C ⥤ (X.IdealSheafData)ᵒᵖ) :
    Cone (F ⋙ subschemeFunctor X ⋙ Over.forget X) :=
  (Over.forget X).mapCone (subschemeSupCone F)

/-- Connected diagrams of actual closed subschemes have the supremum closed
subscheme as a limit in schemes as well as in the over category. -/
def subschemeSupSchemeConeIsLimit [IsConnected C]
    (F : C ⥤ (X.IdealSheafData)ᵒᵖ) :
    IsLimit (subschemeSupSchemeCone F) :=
  isLimitOfPreserves (Over.forget X) (subschemeSupConeIsLimit F)

end AlgebraicGeometry.Scheme.IdealSheafData

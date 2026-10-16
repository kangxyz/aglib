/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Differentials.Relative
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Actual relative differentials for arbitrary scheme morphisms

Specialize the sole generic relative differential presheaf and its original
module sheafification to the original structure map `f.c`. The native
presheaf pullback instance on scheme opens is discharged internally.
The resulting actual structure-module sheaf represents relative derivations
against every coefficient module sheaf, with the original differential,
restriction and coefficient formulas. No base, finiteness, smoothness, or
quasicoherence assumption is made.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The sole native relative differential presheaf for the original scheme structure map. -/
abbrev relativeDifferentialPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials f.c

/-- The sole generic relative differential sheaf, on the original structure map `f.c`. -/
abbrev relativeDifferentialSheaf : X.Modules :=
  SheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials X.sheaf f.c

/-- Actual scheme-relative differentials represent the original relative derivations. -/
def relativeDifferentialSheafHomEquiv (M : X.Modules) :
    (relativeDifferentialSheaf f ⟶ M) ≃
      PresheafOfModulesOfCommRing.Derivation M.val f.c :=
  SheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentialsHomEquiv X.sheaf f.c M

/-- The actual universal relative derivation of the scheme structure sections. -/
abbrev relativeDifferentialDerivation : PresheafOfModulesOfCommRing.Derivation
    (relativeDifferentialSheaf f).val f.c :=
  SheafOfModulesOfCommRing.DifferentialsConstruction.derivation X.sheaf f.c

/-- The original differential is literally the module-sheafification unit on the native
relative cokernel differential. -/
theorem relativeDifferentialDerivation_d (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialDerivation f).d a =
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X)
        (relativeDifferentialPresheaf f).presheaf).app U
        ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation f.c).d a) := rfl

/-- The relative derivation annihilates the original pullback of every base section. -/
@[simp]
theorem relativeDifferentialDerivation_base (U : Y.Opens) (a : Γ(Y, U)) :
    (relativeDifferentialDerivation f).d (f.app U a) = 0 :=
  (relativeDifferentialDerivation f).d_app a

/-- The original section restrictions commute with the actual relative differential. -/
theorem relativeDifferentialDerivation_restrict {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (a : X.presheaf.obj U) :
    (relativeDifferentialDerivation f).d (X.presheaf.map i a) =
      (relativeDifferentialSheaf f).val.map i ((relativeDifferentialDerivation f).d a) :=
  (relativeDifferentialDerivation f).d_map i a

/-- The original descent map associated to a relative derivation with arbitrary coefficients. -/
abbrev relativeDifferentialDesc (M : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c) :
    relativeDifferentialSheaf f ⟶ M :=
  SheafOfModulesOfCommRing.DifferentialsConstruction.desc X.sheaf f.c M d

/-- The universal Hom equivalence evaluates on the same original differential. -/
theorem relativeDifferentialSheafHomEquiv_apply (M : X.Modules)
    (k : relativeDifferentialSheaf f ⟶ M) (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialSheafHomEquiv f M k).d a =
      k.val.app U ((relativeDifferentialDerivation f).d a) := rfl

/-- Actual descent preserves every original derivation value. -/
@[simp]
theorem relativeDifferentialDesc_d (M : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c)
    (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    (relativeDifferentialDesc f M d).val.app U ((relativeDifferentialDerivation f).d a) = d.d a :=
  SheafOfModulesOfCommRing.DifferentialsConstruction.desc_d X.sheaf f.c M d U a

/-- Actual maps out of the relative differential sheaf are determined by differential values. -/
@[ext]
theorem relativeDifferentialSheaf_hom_ext (M : X.Modules)
    {k l : relativeDifferentialSheaf f ⟶ M}
    (h : ∀ (U : X.Opensᵒᵖ) (a : X.presheaf.obj U),
      k.val.app U ((relativeDifferentialDerivation f).d a) =
        l.val.app U ((relativeDifferentialDerivation f).d a)) : k = l :=
  SheafOfModulesOfCommRing.DifferentialsConstruction.hom_ext X.sheaf f.c M h

/-- The same universal equivalence is natural for original scheme-module coefficient maps. -/
theorem relativeDifferentialSheafHomEquiv_comp (M N : X.Modules)
    (k : relativeDifferentialSheaf f ⟶ M) (l : M ⟶ N) :
    relativeDifferentialSheafHomEquiv f N (k ≫ l) =
      (relativeDifferentialSheafHomEquiv f M k).postcomp l.val :=
  SheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentialsHomEquiv_comp
    X.sheaf f.c M N k l

/-- Descent commutes with the original coefficient postcomposition. -/
theorem relativeDifferentialDesc_postcomp (M N : X.Modules)
    (d : PresheafOfModulesOfCommRing.Derivation M.val f.c) (k : M ⟶ N) :
    relativeDifferentialDesc f N (d.postcomp k.val) = relativeDifferentialDesc f M d ≫ k :=
  SheafOfModulesOfCommRing.DifferentialsConstruction.desc_postcomp X.sheaf f.c M N d k

end AlgebraicGeometry.Scheme.Modules.Differentials

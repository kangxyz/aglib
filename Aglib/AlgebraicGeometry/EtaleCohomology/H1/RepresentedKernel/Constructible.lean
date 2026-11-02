/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.Native
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.RepresentedFiniteUnramified

/-! # Constructibility of native finite unramified multiplication kernels

The same scheme kernel represents the literal additive torsion kernel.
Annihilation follows from its original kernel equation; it is not a certificate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

namespace AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.Native

universe u
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

/-- The literal additive scalar kernel is annihilated by that scalar. -/
theorem killedBy_scalarKernel {S : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} S) (n : ℕ) :
    KilledBy n (kernel (n • 𝟙 F)) := by
  apply (cancel_mono (kernel.ι (n • 𝟙 F))).mp
  simp

/-- The unchanged represented sheaf of the native multiplication kernel is bounded. -/
theorem killedBy_representedMultiplicationKernel {S : Scheme.{u}}
    (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ) :
    KilledBy n (representedSheaf (Group.Kernel.group ((𝟙 G : G ⟶ G) ^ n))) := by
  let e := multiplicationKernelIso G n
  have h := killedBy_scalarKernel (representedSheaf G) n
  apply (cancel_mono e.hom).mp
  calc
    (n • 𝟙 _) ≫ e.hom = e.hom ≫ (n • 𝟙 _) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    _ = 0 ≫ e.hom := by rw [h]; simp

/-- The restricted Yoneda description is the underlying original represented
coefficient, not a second choice of representing object. -/
def representedSheafRestrictedYonedaIso {S : Scheme.{u}}
    (G : Grp (Over S)) [IsCommMonObj G.X] :
    (Scheme.Etale.forget S).op ⋙ yoneda.obj (Over.mk G.X.hom) ⋙ uliftFunctor.{u + 1} ≅
      (representedSheaf G).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  Iso.refl _

/-- A finite formally unramified native multiplication kernel makes the literal
small-etale additive torsion kernel constructible. -/
theorem isConstructible_multiplicationKernel {S : Scheme.{u}} [IsLocallyNoetherian S]
    (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ) (hn : 0 < n)
    [IsFinite (Group.Kernel.group ((𝟙 G : G ⟶ G) ^ n)).X.hom]
    [FormallyUnramified (Group.Kernel.group ((𝟙 G : G ⟶ G) ^ n)).X.hom] :
    IsConstructible (kernel (n • 𝟙 (representedSheaf G))) := by
  let K := Group.Kernel.group ((𝟙 G : G ⟶ G) ^ n)
  have h : IsConstructible (representedSheaf K) :=
    Constructible.isConstructible_of_represented_finite_unramified_of_locallyNoetherian
      K.X.hom (representedSheaf K) (representedSheafRestrictedYonedaIso K)
      n hn (killedBy_representedMultiplicationKernel G n)
  exact (isConstructible_iff_of_iso (multiplicationKernelIso G n)).mp h

end AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.Native

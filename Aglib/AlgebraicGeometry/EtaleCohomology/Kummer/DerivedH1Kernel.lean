/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.MultiplicativeKernelInclusion
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MultiplicationFibre
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.Native
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ShortExact

/-! # The actual H1 row of the original derived Kummer triangle

One whole short-complex isomorphism retains both coefficient arrows. Its target
is the original normalized Picard kernel row, without asserting that [n] on the
full Picard sheaf is epimorphic.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients

universe u dX dS w s e
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))

/-- The original short-exact single triangle under the already installed derived direct image. -/
abbrev derivedKummerTriangle : Triangle (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S)) :=
  (derivedDirectImage p).mapTriangle.obj (shortExact X n hn hi).singleTrianglePlus

/-- No alternate fibre or shifted boundary is selected for the original Kummer triangle. -/
theorem derivedKummerTriangle_distinguished :
    derivedKummerTriangle p n hn hi ∈ distTriang _ :=
  (derivedDirectImage p).map_distinguished _ (shortExact X n hn hi).singleTrianglePlus_distinguished

/-- The original second arrow is literal positive multiplication in the selected derived model. -/
theorem derivedKummerTriangle_mor₂ :
    (derivedKummerTriangle p n hn hi).mor₂ =
      n • 𝟙 ((derivedKummerTriangle p n hn hi).obj₂) := by
  change (derivedDirectImage p).map
    ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).map (power X n)) =
    n • 𝟙 ((derivedDirectImage p).obj
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj (gm X)))
  simp only [power, CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

open Picard

/-- The SAME original H1 triangle row identifies simultaneously with the actual kernel and power. -/
def derivedKummerH1KernelIso :
    DerivedCategory.Plus.homologyOneShortComplex (derivedKummerTriangle p n hn hi)
      (derivedKummerTriangle_distinguished p n hn hi) ≅
    ShortComplex.mk (kernel.ι (n • 𝟙 (normalizedPicardEtaleSheaf p o ho)))
      (n • 𝟙 (normalizedPicardEtaleSheaf p o ho)) (kernel.condition _) := by
  let : ∀ Y : Scheme.{u}, HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) :=
    fun Y => HasExt.standard _
  change (sequence X n).map
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0 ⋙
        derivedDirectImage p ⋙
        DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1) ≅ _
  refine (sequence X n).mapNatIso (higherDirectImageIso p 1).symm ≪≫ ?_
  exact ShortComplex.isoMk
    (rootsHigherDirectImageNormalizedPicardTorsionIso.{u, w, s, e, u + 2} p n hn hi o ho)
    (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho)
    (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho)
    (gmHigherDirectImageNormalizedPicardIso_inclusion.{u, w, s, e} p n hn hi o ho).symm
    (gmHigherDirectImageNormalizedPicardIso_power.{u, w, s, e} p o ho n).symm

/-- The first component keeps the original single-homology inverse and roots map. -/
theorem derivedKummerH1KernelIso_hom_τ₁ :
    (derivedKummerH1KernelIso p n hn hi o ho).hom.τ₁ =
      (higherDirectImageIso p 1).inv.app (mu X n) ≫
        rootsHigherDirectImageToNormalizedPicardTorsion.{u, w, s, e} p n hn hi o ho := rfl

/-- The middle component keeps the original single-homology inverse and Picard isomorphism. -/
theorem derivedKummerH1KernelIso_hom_τ₂ :
    (derivedKummerH1KernelIso p n hn hi o ho).hom.τ₂ =
      (higherDirectImageIso p 1).inv.app (gm X) ≫
        (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom := rfl

/-- The original two Gm objects have the SAME H1 comparison. -/
theorem derivedKummerH1KernelIso_hom_τ₃ :
    (derivedKummerH1KernelIso p n hn hi o ho).hom.τ₃ =
      (higherDirectImageIso p 1).inv.app (gm X) ≫
        (gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).hom := rfl

/-- Whole H1 inclusion commutation on the original derived triangle. -/
theorem derivedKummerH1KernelIso_inclusion :
    (derivedKummerH1KernelIso p n hn hi o ho).hom.τ₁ ≫
        kernel.ι (n • 𝟙 (normalizedPicardEtaleSheaf p o ho)) =
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
          (derivedKummerTriangle p n hn hi).mor₁ ≫
        (derivedKummerH1KernelIso p n hn hi o ho).hom.τ₂ :=
  (derivedKummerH1KernelIso p n hn hi o ho).hom.comm₁₂

/-- Whole H1 multiplication commutation uses the same middle and third comparisons. -/
theorem derivedKummerH1KernelIso_power :
    (derivedKummerH1KernelIso p n hn hi o ho).hom.τ₂ ≫
        (n • 𝟙 (normalizedPicardEtaleSheaf p o ho)) =
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map
          (derivedKummerTriangle p n hn hi).mor₂ ≫
        (derivedKummerH1KernelIso p n hn hi o ho).hom.τ₃ :=
  (derivedKummerH1KernelIso p n hn hi o ho).hom.comm₂₃

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe d
attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]

/-- The existing native scheme-torsion comparison retains its original inclusion. -/
@[reassoc]
private theorem representedMultiplicationKernelIso_hom_ι (n : ℕ) :
    (RepresentedKernel.Native.multiplicationKernelIso G n).hom ≫
        kernel.ι (n • 𝟙 (representedSheaf G)) =
      representedSheafMap (Group.Kernel.inclusion ((𝟙 G : G ⟶ G) ^ n)) := by
  dsimp only [RepresentedKernel.Native.multiplicationKernelIso, Iso.trans_hom]
  rw [Category.assoc, kernelIsoOfEq_hom_comp_ι, RepresentedKernel.Native.kernelIso_hom_ι]

variable [HasDerivedCategory.{d} (AbelianSheaf.{u, u + 1} S)]
    {F B0 : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S)}
    (n : ℕ) (i : F ⟶ B0) (δ : B0 ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk i (n • 𝟙 B0) δ ∈ distTriang _)
    [Epi ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).map (n • 𝟙 B0))]
    (e : (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).obj B0 ≅
      representedSheaf G)

/-- The actual multiplication fibre has the represented sheaf of the ORIGINAL scheme kernel. -/
def representedMultiplicationFiberH1Iso :
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).obj F ≅
      representedSheaf (Group.Kernel.group ((𝟙 G : G ⟶ G) ^ n)) :=
  DerivedCategory.Plus.homologyOneMultiplicationKernelIso n i δ hT e ≪≫
    (RepresentedKernel.Native.multiplicationKernelIso G n).symm

/-- No original inclusion is lost when identifying the fibre with actual scheme torsion. -/
@[reassoc]
theorem representedMultiplicationFiberH1Iso_hom_inclusion :
    (representedMultiplicationFiberH1Iso G n i δ hT e).hom ≫
        representedSheafMap (Group.Kernel.inclusion ((𝟙 G : G ⟶ G) ^ n)) =
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1).map i ≫ e.hom := by
  have h : (RepresentedKernel.Native.multiplicationKernelIso G n).inv ≫
        representedSheafMap (Group.Kernel.inclusion ((𝟙 G : G ⟶ G) ^ n)) =
      kernel.ι (n • 𝟙 (representedSheaf G)) := by
    rw [← representedMultiplicationKernelIso_hom_ι G n, Iso.inv_hom_id_assoc]
  dsimp only [representedMultiplicationFiberH1Iso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, h, DerivedCategory.Plus.homologyOneMultiplicationKernelIso_hom_ι]

end AlgebraicGeometry.Scheme.EtaleCohomology

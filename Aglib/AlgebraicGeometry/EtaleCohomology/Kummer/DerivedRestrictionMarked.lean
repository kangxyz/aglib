/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.Marked
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! The original multiplication fibre and the marked represented kernel row. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open DerivedCategory RepresentedKernel

universe u d

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

variable {S : Scheme.{u}} {K G : Grp (Over S)} {q : G ⟶ G}
  [IsCommMonObj K.X] [IsCommMonObj G.X] (m : KernelMarking K G G q) (n : ℕ)
  (hpow : representedSheafMap q = n • 𝟙 (representedSheaf G))

/-- The given marked represented kernel identifies with the additive power kernel. -/
def markedPowerKernelIso :
    representedSheaf K ≅ kernel (n • 𝟙 (representedSheaf G)) :=
  (markedKernelSequenceIsKernel m).conePointUniqueUpToIso
    (kernelIsKernel (representedSheafMap q)) ≪≫ kernelIsoOfEq hpow

/-- The power kernel comparison preserves the original marked insertion. -/
@[reassoc]
theorem markedPowerKernelIso_hom_ι :
    (markedPowerKernelIso m n hpow).hom ≫ kernel.ι (n • 𝟙 (representedSheaf G)) =
      (markedKernelSequence m).f := by
  rw [markedPowerKernelIso, Iso.trans_hom, Category.assoc, kernelIsoOfEq_hom_comp_ι]
  exact IsLimit.conePointUniqueUpToIso_hom_comp (markedKernelSequenceIsKernel m)
    (kernelIsKernel (representedSheafMap q)) WalkingParallelPair.zero

/-- The inverse comparison takes the original marked insertion to the power kernel insertion. -/
@[reassoc]
theorem markedPowerKernelIso_inv_f :
    (markedPowerKernelIso m n hpow).inv ≫ (markedKernelSequence m).f =
      kernel.ι (n • 𝟙 (representedSheaf G)) := by
  rw [← markedPowerKernelIso_hom_ι m n hpow, Iso.inv_hom_id_assoc]

include hpow in
/-- The marked row is short exact when the actual additive power is epimorphic. -/
theorem markedPowerKernelSequence_shortExact [Epi (n • 𝟙 (representedSheaf G))] :
    (markedKernelSequence m).ShortExact := by
  let : Epi (representedSheafMap q) := (congrArg Epi hpow).mpr inferInstance
  exact markedKernelSequence_shortExact m

variable [HasDerivedCategory.{d} (AbelianSheaf.{u, u + 1} S)]
  {F B : Plus (AbelianSheaf.{u, u + 1} S)}

set_option hygiene false in
local notation "H₁" => Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 1

/-- The supplied multiplication-fibre isomorphism, expressed using the original marked kernel. -/
def markedMultiplicationFibreH1Iso (eF : (H₁).obj F ≅ kernel (n • 𝟙 (representedSheaf G))) :
    (H₁).obj F ≅ representedSheaf K :=
  eF ≪≫ (markedPowerKernelIso m n hpow).symm

/-- The supplied fibre equation gives the first square against the original marked row. -/
theorem markedMultiplicationFibreH1_first_square
    (i : F ⟶ B) (eB : (H₁).obj B ≅ representedSheaf G)
    (eF : (H₁).obj F ≅ kernel (n • 𝟙 (representedSheaf G)))
    (hF : eF.hom ≫ kernel.ι (n • 𝟙 (representedSheaf G)) = (H₁).map i ≫ eB.hom) :
    (H₁).map i ≫ eB.hom =
      (markedMultiplicationFibreH1Iso m n hpow eF).hom ≫ (markedKernelSequence m).f := by
  rw [← hF, markedMultiplicationFibreH1Iso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    markedPowerKernelIso_inv_f]

include hpow in
/-- The same middle and third comparison give the second square against the marked row. -/
theorem markedMultiplicationFibreH1_second_square (eB : (H₁).obj B ≅ representedSheaf G) :
    (H₁).map (n • 𝟙 B) ≫ eB.hom = eB.hom ≫ (markedKernelSequence m).g := by
  change (H₁).map (n • 𝟙 B) ≫ eB.hom = eB.hom ≫ representedSheafMap q
  rw [hpow, (H₁).map_nsmul, (H₁).map_id, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

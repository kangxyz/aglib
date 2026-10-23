/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.ProjectiveSections
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.Affine
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Product
public import Aglib.AlgebraicGeometry.IdealSheaf.Colon
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.SpecKernel
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Actual Cartier powers and their original scalar quotients

The tensor powers, closed ideal powers, scalar multiples and quotients are compared through their
original inclusions. The resulting short exact layers use the actual exceptional curve and its
native conormal O(1).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

universe u v w t

section OriginalEqualKernels

variable {D E X : Scheme.{u}} (j : D ⟶ X) (i : E ⟶ X)
  [IsClosedImmersion j] [IsClosedImmersion i]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equal original closed ideals identify their actual kernel modules through
an actual isomorphism of the original closed immersions. -/
def idealModuleIsoOfKernelEq (h : j.ker = i.ker) :
    Hom.idealModule j ≅ Hom.idealModule i := by
  let a := IsClosedImmersion.lift j i h.le
  have ha : a ≫ j = i := IsClosedImmersion.lift_fac j i h.le
  let _ : IsIso a := IsClosedImmersion.isIso_of_ker_eq i j a ha h.symm
  let hw : a ≫ j = i ≫ 𝟙 X := ha.trans (Category.comp_id i).symm
  let φ := Hom.idealPushforwardMap j i (𝟙 X) a hw
  let _ : IsIso φ := Hom.idealPushforwardMap_isIso_of_iso_square j i (𝟙 X) a hw
  exact asIso φ ≪≫ (Scheme.Modules.pushforwardId X).app (Hom.idealModule i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The equality comparison preserves the original inclusions into the same
structure module, rather than replacing either ideal by an abstract copy. -/
theorem idealModuleIsoOfKernelEq_hom_inclusion (h : j.ker = i.ker) :
    (idealModuleIsoOfKernelEq j i h).hom ≫ Hom.idealInclusion i =
      Hom.idealInclusion j := by
  let a := IsClosedImmersion.lift j i h.le
  have ha : a ≫ j = i := IsClosedImmersion.lift_fac j i h.le
  let hw : a ≫ j = i ≫ 𝟙 X := ha.trans (Category.comp_id i).symm
  let φ := Hom.idealPushforwardMap j i (𝟙 X) a hw
  change (φ ≫ (Scheme.Modules.pushforwardId X).hom.app (Hom.idealModule i)) ≫ _ = _
  calc
    _ = φ ≫ (Scheme.Modules.pushforward (𝟙 X)).map (Hom.idealInclusion i) ≫
        (Scheme.Modules.pushforwardId X).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
      have hn : (Scheme.Modules.pushforwardId X).hom.app (Hom.idealModule i) ≫
          Hom.idealInclusion i =
        (Scheme.Modules.pushforward (𝟙 X)).map (Hom.idealInclusion i) ≫
          (Scheme.Modules.pushforwardId X).hom.app (SheafOfModules.unit X.ringCatSheaf) :=
        ((Scheme.Modules.pushforwardId X).hom.naturality (Hom.idealInclusion i)).symm
      exact (Category.assoc _ _ _).trans (congrArg (fun q => φ ≫ q) hn)
    _ = Hom.idealInclusion j ≫ Hom.structureModuleMap (𝟙 X) ≫
        (Scheme.Modules.pushforwardId X).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
      rw [← Category.assoc, Hom.idealPushforwardMap_inclusion, Category.assoc]
    _ = _ := by
      have hunit : Hom.structureModuleMap (𝟙 X) ≫
          (Scheme.Modules.pushforwardId X).hom.app
            (SheafOfModules.unit X.ringCatSheaf) = 𝟙 _ := by
        ext U x
        rfl
      rw [hunit, Category.comp_id]

end OriginalEqualKernels

section ActualCartierPowers

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original top closed-ideal module is canonically the actual structure module. -/
def topIdealModuleIso : SheafOfModules.unit X.ringCatSheaf ≅
    Hom.idealModule (⊤ : X.IdealSheafData).subschemeι := by
  let c := (⊤ : X.IdealSheafData).subschemeι
  have hz : Hom.structureModuleMap c = 0 := by
    apply moduleHom_ext_affine
    intro U
    ext a
    change (c.app U.val).hom a = 0
    have hker : RingHom.ker (c.app U.val).hom = (⊤ : Ideal Γ(X, U.val)) :=
      (⊤ : X.IdealSheafData).ker_subschemeι_app U
    have ha : a ∈ RingHom.ker (c.app U.val).hom := by
      rw [hker]
      trivial
    exact ha
  let _ : IsIso (Hom.idealInclusion c) := kernel.ι_of_zero hz
  exact (asIso (Hom.idealInclusion c)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual one-step Cartier product comparison, with an arbitrary actual
previous power comparison. Separating the step keeps recursive proof checking small. -/
def cartierIdealPowerStepIso (n : ℕ) {P : X.Modules}
    (eP : P ≅ Hom.idealModule (i.ker ^ n).subschemeι) :
    tensorSheaf X (Hom.idealModule i) P ≅
      Hom.idealModule (i.ker ^ (n + 1)).subschemeι := by
  let j := (i.ker ^ n).subschemeι
  let e := (moduleTensorLeftFunctor X (Hom.idealModule i)).mapIso eP
  let c := Hom.idealProductIso i j hI
  have h : (i.ker * j.ker).subschemeι.ker = (i.ker ^ (n + 1)).subschemeι.ker := by
    dsimp only [j]
    simp only [Scheme.IdealSheafData.ker_subschemeι, pow_succ']
  exact e ≪≫ c ≪≫ idealModuleIsoOfKernelEq
    (i.ker * j.ker).subschemeι (i.ker ^ (n + 1)).subschemeι h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual Cartier tensor powers are the original ideal modules of the original
closed ideal powers, including the zeroth power. -/
def cartierIdealPowerIso : (n : ℕ) →
    (tensorPowerLineBundle X (cartierIdealLineBundle i hI) n).val ≅
      Hom.idealModule (i.ker ^ n).subschemeι
  | 0 => by
    let e₀ : (trivialLineBundle X).val ≅ SheafOfModules.unit X.ringCatSheaf :=
      coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
    exact e₀ ≪≫ topIdealModuleIso (X := X) ≪≫
      eqToIso (congrArg (fun J : X.IdealSheafData => Hom.idealModule J.subschemeι)
        (show (⊤ : X.IdealSheafData) = i.ker ^ 0 from (pow_zero i.ker).symm))
  | n + 1 => cartierIdealPowerStepIso i hI n (cartierIdealPowerIso n)

end ActualCartierPowers

section ActualExceptionalRestrictions

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of each original ideal power is the actual native O(n), through
the original Cartier tensor/product comparison. -/
def idealPowerRestrictionIso (n : ℕ) :
    (Scheme.Modules.pullback i).obj (Hom.idealModule (i.ker ^ n).subschemeι) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (n : ℤ) := by
  let e := tensorPowerRestrictionIso i (cartierIdealLineBundle i hI) 1 eI n
  refine (Scheme.Modules.pullback i).mapIso (cartierIdealPowerIso i hI n).symm ≪≫ e ≪≫ ?_
  exact eqToIso (congrArg (twistingSheaf k (ULift.{u} (Fin 2))) (mul_one (n : ℤ)))

end ActualExceptionalRestrictions

section ActualPowerLayer

open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact tensoring of the original Cartier ideal sequence gives the actual
successive ideal-power sequence, with its native O_E(n) quotient. -/
def idealPowerLayerSequence (n : ℕ) : ShortComplex X.Modules := by
  let J := cartierIdealLineBundle i hI
  let P := tensorPowerLineBundle X J n
  let T := (lineBundleDualTensorEquivalence X P).inverse
  let S := (Hom.idealSequence i).map T
  let e₁ : S.X₁ ≅ Hom.idealModule (i.ker ^ (n + 1)).subschemeι :=
    tensorSheafBraiding X P.val J.val ≪≫ cartierIdealPowerIso i hI (n + 1)
  let e₂ : S.X₂ ≅ Hom.idealModule (i.ker ^ n).subschemeι :=
    rightUnitor (C := X.Modules) P.val ≪≫ cartierIdealPowerIso i hI n
  let eR : (Scheme.Modules.pullback i).obj P.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (n : ℤ) :=
    (Scheme.Modules.pullback i).mapIso (cartierIdealPowerIso i hI n) ≪≫
      idealPowerRestrictionIso i hI eI n
  let e₃ : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
      (twistingSheaf k (ULift.{u} (Fin 2)) (n : ℤ)) :=
    closedImmersionProjectionFormulaIso i P.val
        (SheafOfModules.unit (ProjectiveSpace k (ULift.{u} (Fin 2))).ringCatSheaf) ≪≫
      (Scheme.Modules.pushforward i).mapIso
        (rightUnitor (C := (ProjectiveSpace k (ULift.{u} (Fin 2))).Modules)
          ((Scheme.Modules.pullback i).obj P.val)) ≪≫
      (Scheme.Modules.pushforward i).mapIso eR
  exact cartierSequenceOfIsos S e₁ e₂ e₃

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This original ideal-power sequence is short exact without any cohomology assumption. -/
theorem idealPowerLayerSequence_shortExact (n : ℕ) :
    (idealPowerLayerSequence i hI eI n).ShortExact := by
  have hBase := Hom.idealSequence_shortExact i
  let _ : Mono (Hom.idealSequence i).f := hBase.mono_f
  let _ : Epi (Hom.idealSequence i).g := hBase.epi_g
  let P := tensorPowerLineBundle X (cartierIdealLineBundle i hI) n
  let T := (lineBundleDualTensorEquivalence X P).inverse
  let _ : T.IsEquivalence := inferInstance
  dsimp only [idealPowerLayerSequence]
  apply cartierSequenceOfIsos_shortExact
  exact hBase.map T

end ActualPowerLayer

section OriginalQuotientLayer

variable {D : Type v} [Category.{u} D] [Abelian D]
  {K M N : D} (a : K ⟶ M) (b : M ⟶ N)

/-- The original cokernel map induced by the original second arrow. -/
def quotientLayerMap : cokernel a ⟶ cokernel (a ≫ b) :=
  cokernel.desc a (b ≫ cokernel.π (a ≫ b)) (by
    rw [← Category.assoc, cokernel.condition])

/-- The original reduction between the two original cokernels. -/
def quotientReductionMap : cokernel (a ≫ b) ⟶ cokernel b :=
  cokernel.desc (a ≫ b) (cokernel.π b) (by
    rw [Category.assoc, cokernel.condition, comp_zero])

private theorem quotientLayerMap_π : cokernel.π a ≫ quotientLayerMap a b =
    b ≫ cokernel.π (a ≫ b) := cokernel.π_desc _ _ _

private theorem quotientReductionMap_π : cokernel.π (a ≫ b) ≫ quotientReductionMap a b =
    cokernel.π b := cokernel.π_desc _ _ _

/-- The original successive-cokernel inclusion is killed by the original reduction. -/
theorem quotientLayerMap_reduction :
    quotientLayerMap a b ≫ quotientReductionMap a b = 0 := by
  apply (cancel_epi (cokernel.π a)).mp
  calc
    _ = b ≫ cokernel.π (a ≫ b) ≫ quotientReductionMap a b := by
      rw [← Category.assoc, quotientLayerMap_π, Category.assoc]
    _ = 0 := by rw [quotientReductionMap_π, cokernel.condition]
    _ = _ := (comp_zero : cokernel.π a ≫ (0 : cokernel a ⟶ cokernel b) = 0).symm

private theorem quotientLayerMap_mono [Mono b] : Mono (quotientLayerMap a b) := by
  let w : b ≫ cokernel.π (a ≫ b) = cokernel.π a ≫ quotientLayerMap a b :=
    (quotientLayerMap_π a b).symm
  let S := PushoutCocone.mk (cokernel.π (a ≫ b)) (quotientLayerMap a b) w
  have hS : IsColimit S := by
    refine PushoutCocone.IsColimit.mk w (fun s =>
      cokernel.desc (a ≫ b) s.inl (by
        rw [Category.assoc, s.condition, ← Category.assoc, cokernel.condition, zero_comp]))
      (fun s => cokernel.π_desc _ _ _) ?_ ?_
    · intro s
      apply (cancel_epi (cokernel.π a)).mp
      rw [← Category.assoc, quotientLayerMap_π, Category.assoc, cokernel.π_desc]
      exact s.condition
    · intro s m hm _
      apply (cancel_epi (cokernel.π (a ≫ b))).mp
      exact hm.trans (cokernel.π_desc _ _ _).symm
  exact Abelian.mono_inr_of_isColimit b (cokernel.π a) hS

private def quotientReductionDesc {T : D} (γ : cokernel (a ≫ b) ⟶ T)
    (hγ : quotientLayerMap a b ≫ γ = 0) : cokernel b ⟶ T :=
  cokernel.desc b (cokernel.π (a ≫ b) ≫ γ) (by
    rw [← Category.assoc, ← quotientLayerMap_π, Category.assoc, hγ, comp_zero])

private def quotientReductionMap_isCokernel :
    IsColimit (CokernelCofork.ofπ (quotientReductionMap a b)
      (quotientLayerMap_reduction a b)) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun γ hγ => quotientReductionDesc a b γ hγ) ?_ ?_
  · intro T γ hγ
    apply (cancel_epi (cokernel.π (a ≫ b))).mp
    rw [← Category.assoc, quotientReductionMap_π]
    exact cokernel.π_desc _ _ _
  · intro T γ hγ m hm
    apply (cancel_epi (cokernel.π b)).mp
    calc
      _ = (cokernel.π (a ≫ b) ≫ quotientReductionMap a b) ≫ m :=
        congrArg (fun q => q ≫ m) (quotientReductionMap_π a b).symm
      _ = cokernel.π (a ≫ b) ≫ γ := by rw [Category.assoc, hm]
      _ = _ := (cokernel.π_desc _ _ _).symm

/-- The actual successive-cokernel short complex of the original arrows. -/
def quotientLayerSequence : ShortComplex D :=
  ShortComplex.mk (quotientLayerMap a b) (quotientReductionMap a b)
    (quotientLayerMap_reduction a b)

private theorem quotientLayerSequence_shortExact [Mono b] :
    (quotientLayerSequence a b).ShortExact := by
  let _ : Mono (quotientLayerMap a b) := quotientLayerMap_mono a b
  let h := quotientReductionMap_isCokernel a b
  exact
    { exact := (quotientLayerSequence a b).exact_of_g_is_cokernel h
      mono_f := by
        change Mono (quotientLayerMap a b)
        exact quotientLayerMap_mono a b
      epi_g := epi_of_isColimit_cofork h }

end OriginalQuotientLayer

section OriginalPowerQuotients

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual successive ideal-power arrow and the original kernel inclusion
give the short exact sequence of their original cokernels. -/
theorem idealPowerQuotientLayer_shortExact (n : ℕ) :
    let a := (idealPowerLayerSequence i hI eI n).f
    let b := Hom.idealInclusion (i.ker ^ n).subschemeι
    let j : cokernel a ⟶ cokernel (a ≫ b) :=
      cokernel.desc a (b ≫ cokernel.π (a ≫ b))
        (by rw [← Category.assoc, cokernel.condition])
    let r : cokernel (a ≫ b) ⟶ cokernel b :=
      cokernel.desc (a ≫ b) (cokernel.π b)
        (by rw [Category.assoc, cokernel.condition, comp_zero])
    (ShortComplex.mk j r (by exact quotientLayerMap_reduction a b)).ShortExact := by
  let a := (idealPowerLayerSequence i hI eI n).f
  let b := Hom.idealInclusion (i.ker ^ n).subschemeι
  let _ : Mono b := inferInstance
  exact quotientLayerSequence_shortExact a b

end OriginalPowerQuotients

section ComposedInclusion

private theorem composedIso_inclusion {D : Type v} [Category.{u} D]
    {P Q S T U : D} (e : P ≅ Q) (c : Q ≅ S) (d : S ≅ T)
    (iS : S ⟶ U) (iT : T ⟶ U) (m : Q ⟶ U)
    (hd : d.hom ≫ iT = iS) (hc : c.hom ≫ iS = m) :
    (e ≪≫ c ≪≫ d).hom ≫ iT = e.hom ≫ m := by
  simp only [Iso.trans_hom, Category.assoc, hd, hc]

end ComposedInclusion

section OriginalPowerInclusions

open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.Modules.Invertible

variable {X C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original recursive tensor/product comparison retains the original
power-ideal inclusion, with its actual Cartier multiplication map. -/
theorem cartierIdealPowerStepIso_inclusion (n : ℕ) {P : X.Modules}
    (eP : P ≅ Hom.idealModule (i.ker ^ n).subschemeι) :
    (cartierIdealPowerStepIso i hI n eP).hom ≫
      Hom.idealInclusion (i.ker ^ (n + 1)).subschemeι =
    (moduleTensorLeftFunctor X (Hom.idealModule i)).map eP.hom ≫
      Hom.Cartier.idealMultiplication i (i.ker ^ n).subschemeι := by
  let j := (i.ker ^ n).subschemeι
  let e := (moduleTensorLeftFunctor X (Hom.idealModule i)).mapIso eP
  let c := Hom.idealProductIso i j hI
  have h : (i.ker * j.ker).subschemeι.ker = (i.ker ^ (n + 1)).subschemeι.ker := by
    dsimp only [j]
    simp only [Scheme.IdealSheafData.ker_subschemeι, pow_succ']
  let eJ := idealModuleIsoOfKernelEq
    (i.ker * j.ker).subschemeι (i.ker ^ (n + 1)).subschemeι h
  exact composedIso_inclusion e c eJ
    (Hom.idealInclusion (i.ker * j.ker).subschemeι)
    (Hom.idealInclusion (i.ker ^ (n + 1)).subschemeι)
    (Hom.Cartier.idealMultiplication i j)
    (idealModuleIsoOfKernelEq_hom_inclusion _ _ h)
    (Hom.idealProductIso_hom_inclusion i j hI)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original recursive tensor/product comparison retains the original
power-ideal inclusion, with its actual Cartier multiplication map. -/
theorem cartierIdealPowerIso_succ_inclusion (n : ℕ) :
    (cartierIdealPowerIso i hI (n + 1)).hom ≫
      Hom.idealInclusion (i.ker ^ (n + 1)).subschemeι =
    (moduleTensorLeftFunctor X (Hom.idealModule i)).map (cartierIdealPowerIso i hI n).hom ≫
      Hom.Cartier.idealMultiplication i (i.ker ^ n).subschemeι :=
  cartierIdealPowerStepIso_inclusion i hI n (cartierIdealPowerIso i hI n)

end OriginalPowerInclusions

section ActualPowerArrow

open CategoryTheory.MonoidalCategory AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

variable {k : Type u} [CommRing k] {X : Scheme.{u}}
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constructed power arrow is the inclusion of the ORIGINAL ideal powers,
identified by its literal original kernel-inclusion triangle. -/
theorem idealPowerLayerSequence_f_inclusion (n : ℕ) :
    (idealPowerLayerSequence i hI eI n).f ≫
      Hom.idealInclusion (i.ker ^ n).subschemeι =
        Hom.idealInclusion (i.ker ^ (n + 1)).subschemeι := by
  let I : X.Modules := Hom.idealModule i
  let P := tensorPowerLineBundle X (cartierIdealLineBundle i hI) n
  let j := (i.ker ^ n).subschemeι
  let e := cartierIdealPowerIso i hI n
  let B := tensorSheafBraiding X P.val I
  let E₁ := B ≪≫ cartierIdealPowerIso i hI (n + 1)
  let S := idealPowerLayerSequence i hI eI n
  apply (cancel_epi E₁.hom).mp
  have hf : E₁.hom ≫ S.f =
      tensorSheafMap X (𝟙 P.val) (Hom.idealInclusion i) ≫
        (rightUnitor (C := X.Modules) P.val).hom ≫ e.hom := by
    change E₁.hom ≫ (E₁.inv ≫
      tensorSheafMap X (𝟙 P.val) (Hom.idealInclusion i) ≫
        (rightUnitor (C := X.Modules) P.val).hom ≫ e.hom) = _
    simp only [Iso.hom_inv_id_assoc]
  have hR : E₁.hom ≫ Hom.idealInclusion (i.ker ^ (n + 1)).subschemeι =
      B.hom ≫ (moduleTensorLeftFunctor X I).map e.hom ≫ Hom.Cartier.idealMultiplication i j := by
    change (B.hom ≫ (cartierIdealPowerIso i hI (n + 1)).hom) ≫ _ = _
    exact (Category.assoc _ _ _).trans
      (congrArg (fun f => B.hom ≫ f) (cartierIdealPowerIso_succ_inclusion i hI n))
  have hmiddle :
      (tensorSheafMap X (𝟙 P.val) (Hom.idealInclusion i) ≫
        (rightUnitor (C := X.Modules) P.val).hom ≫ e.hom) ≫ Hom.idealInclusion j =
      B.hom ≫ (moduleTensorLeftFunctor X I).map e.hom ≫ Hom.Cartier.idealMultiplication i j := by
    apply moduleTensor_hom_ext
    intro U p m
    let a : Γ(X, U) := (Hom.idealInclusion i).val.app (op U) m
    have h₁ : (tensorSheafMap X (𝟙 P.val) (Hom.idealInclusion i)).val.app (op U)
        (moduleTensorSection X P.val I U p m) =
        moduleTensorSection X P.val (SheafOfModules.unit X.ringCatSheaf) U p a :=
      moduleTensorLeftFunctor_map_section P.val (Hom.idealInclusion i) U p m
    have h₂ : (rightUnitor (C := X.Modules) P.val).hom.val.app (op U)
        (moduleTensorSection X P.val (SheafOfModules.unit X.ringCatSheaf) U p a) = a • p :=
      tensorRightUnitIso_hom_section X P.val U p a
    have h₃ := (e.hom.val.app (op U)).hom.map_smul a p
    have h₄ := ((Hom.idealInclusion j).val.app (op U)).hom.map_smul a
      (e.hom.val.app (op U) p)
    have h₅ : B.hom.val.app (op U) (moduleTensorSection X P.val I U p m) =
        moduleTensorSection X I P.val U m p :=
      braiding_hom_moduleTensorSection P.val I U p m
    have h₆ : ((moduleTensorLeftFunctor X I).map e.hom).val.app (op U)
        (moduleTensorSection X I P.val U m p) =
        moduleTensorSection X I (Hom.idealModule j) U m (e.hom.val.app (op U) p) :=
      moduleTensorLeftFunctor_map_section I e.hom U m p
    change (Hom.idealInclusion j).val.app (op U)
      (e.hom.val.app (op U)
        ((rightUnitor (C := X.Modules) P.val).hom.val.app (op U)
          ((tensorSheafMap X (𝟙 P.val) (Hom.idealInclusion i)).val.app (op U)
            (moduleTensorSection X P.val I U p m)))) =
      (Hom.Cartier.idealMultiplication i j).val.app (op U)
        (((moduleTensorLeftFunctor X I).map e.hom).val.app (op U)
          (B.hom.val.app (op U) (moduleTensorSection X P.val I U p m)))
    rw [h₁, h₂, h₃, h₄, h₅, h₆, Hom.idealMultiplication_section]
    rfl
  calc
    _ = (E₁.hom ≫ S.f) ≫ Hom.idealInclusion j := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ Hom.idealInclusion j) hf
    _ = _ := hmiddle
    _ = _ := hR.symm

end ActualPowerArrow

section OriginalScalarKernel

open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (J : Ideal R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual scalar ideal multiple is the original kernel ideal of the actual
base thickening. Its comparison is forced by the original quotient unit. -/
def idealMultipleKernelIso :
    idealMultiple X (affineFormalFunctionsScalar f)
      (SheafOfModules.unit X.ringCatSheaf) J ≅
        Hom.idealModule (idealThickeningι f J) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let _ : O.IsQuasicoherent := quasicoherent_of_affineCharts O
    (fun R p _ => (affineLocallyFiniteType_unit X R p).1)
  let j := idealThickeningι f J
  let α := affineFormalFunctionsScalar f
  let eQ : idealQuotient X α O J ≅
      (Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit (idealThickeningSpace f J).ringCatSheaf) :=
    idealQuotientThickeningIso f O J ≪≫
      (Scheme.Modules.pushforward j).mapIso (pullbackUnitIso j)
  have he : idealQuotientπ X α O J ≫ eQ.hom = Hom.structureModuleMap j := by
    dsimp only [eQ, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, idealQuotientπ_thickeningIso_hom]
    exact pullbackUnitIso_homEquiv j
  have he' : Hom.structureModuleMap j ≫ eQ.inv = idealQuotientπ X α O J := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let _ : Mono (idealSequence X α O J).f := by
    change Mono (idealMultipleι X α O J)
    infer_instance
  let hK := IsKernel.ofCompIso (idealQuotientπ X α O J)
    (Hom.structureModuleMap j) eQ.symm he'
    (idealSequence_shortExact X α O J).exact.fIsKernel
  exact hK.conePointUniqueUpToIso (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar/kernel comparison keeps the literal original inclusions. -/
theorem idealMultipleKernelIso_hom_inclusion :
    (idealMultipleKernelIso f J).hom ≫ Hom.idealInclusion (idealThickeningι f J) =
      idealMultipleι X (affineFormalFunctionsScalar f)
        (SheafOfModules.unit X.ringCatSheaf) J := by
  dsimp only [idealMultipleKernelIso]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end OriginalScalarKernel

section OriginalSpectralPowers

variable {R k : Type u} [CommRing R] [CommRing k]

/-- The kernel of the original quotient-spectrum map is the original power
of the kernel of the original residue-spectrum map. -/
theorem spectralPowerKernel (I : Ideal R) (β : R →+* k)
    (hβ : RingHom.ker β = I) (n : ℕ) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))).ker =
      (Spec.map (CommRingCat.ofHom β)).ker ^ n := by
  apply Scheme.IdealSheafData.equivOfIsAffine.injective
  rw [map_pow]
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))).ker.ideal
      ⟨⊤, isAffineOpen_top _⟩ =
    ((Spec.map (CommRingCat.ofHom β)).ker.ideal ⟨⊤, isAffineOpen_top _⟩) ^ n
  rw [Scheme.IdealSheafData.specMap_kernel_top,
    Scheme.IdealSheafData.specMap_kernel_top, Ideal.mk_ker, hβ]
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have hmap (J : Ideal R) : J.comap e.toRingHom = J.map e.symm.toRingHom :=
    (Ideal.map_symm e).symm
  change (I ^ n).comap e.toRingHom = (I.comap e.toRingHom) ^ n
  rw [hmap, hmap, Ideal.map_pow]

/-- Every actual coefficient thickening has precisely the corresponding
power of the actual exceptional ideal, from the original degree-one equality. -/
theorem idealThickening_kernel_eq_power {X E : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (i : E ⟶ X)
    (I : Ideal R) (β : R →+* k) (hβ : RingHom.ker β = I)
    (hker : (Spec.map (CommRingCat.ofHom β)).ker.comap f = i.ker) (n : ℕ) :
    (idealThickeningι f (I ^ n)).ker = i.ker ^ n := by
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  change (pullback.fst f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (I ^ n))))).ker = _
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    spectralPowerKernel I β hβ n, Scheme.IdealSheafData.comap_pow, hker]

end OriginalSpectralPowers



section OriginalPowerScalarComparison

variable {R k : Type u} [CommRing R] [CommRing k] {X E : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (i : E ⟶ X)
  (I : Ideal R) (β : R →+* k) (hβ : RingHom.ker β = I)
  (hker : (Spec.map (CommRingCat.ofHom β)).ker.comap f = i.ker)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original scalar ideal powers identify with the original exceptional
ideal powers through the actual thickening-kernel comparison. -/
def idealPowerScalarIso (n : ℕ) :
    idealPower X (affineFormalFunctionsScalar f) (SheafOfModules.unit X.ringCatSheaf) I n ≅
      Hom.idealModule (i.ker ^ n).subschemeι :=
  idealMultipleKernelIso f (I ^ n) ≪≫
    idealModuleIsoOfKernelEq (idealThickeningι f (I ^ n)) (i.ker ^ n).subschemeι
      ((idealThickening_kernel_eq_power f i I β hβ hker n).trans
        (Scheme.IdealSheafData.ker_subschemeι _).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This comparison retains the actual formal-functions ideal inclusion. -/
theorem idealPowerScalarIso_hom_inclusion (n : ℕ) :
    (idealPowerScalarIso f i I β hβ hker n).hom ≫
        Hom.idealInclusion (i.ker ^ n).subschemeι =
      idealMultipleι X (affineFormalFunctionsScalar f)
        (SheafOfModules.unit X.ringCatSheaf) (I ^ n) := by
  dsimp only [idealPowerScalarIso, Iso.trans_hom]
  rw [Category.assoc, idealModuleIsoOfKernelEq_hom_inclusion,
    idealMultipleKernelIso_hom_inclusion]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original formal-functions coefficient quotient is the original
cokernel of the original exceptional-power inclusion. -/
def idealPowerScalarQuotientIso (n : ℕ) :
    idealPowerQuotient X (affineFormalFunctionsScalar f)
        (SheafOfModules.unit X.ringCatSheaf) I n ≅
      cokernel (Hom.idealInclusion (i.ker ^ n).subschemeι) :=
  cokernel.mapIso
    (idealMultipleι X (affineFormalFunctionsScalar f)
      (SheafOfModules.unit X.ringCatSheaf) (I ^ n))
    (Hom.idealInclusion (i.ker ^ n).subschemeι)
    (idealPowerScalarIso f i I β hβ hker n) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id] using
      (idealPowerScalarIso_hom_inclusion f i I β hβ hker n).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Its forward map carries the original quotient projection to the original
exceptional-power cokernel projection, with no assumed equality of tower maps. -/
theorem idealPowerScalarQuotientIso_π (n : ℕ) :
    idealQuotientπ X (affineFormalFunctionsScalar f)
        (SheafOfModules.unit X.ringCatSheaf) (I ^ n) ≫
        (idealPowerScalarQuotientIso f i I β hβ hker n).hom =
      cokernel.π (Hom.idealInclusion (i.ker ^ n).subschemeι) := by
  simp only [idealPowerScalarQuotientIso, cokernel.mapIso_hom,
    idealQuotientπ, cokernel.map, cokernel.π_desc, Iso.refl_hom, Category.id_comp]

end OriginalPowerScalarComparison

section OriginalFormalLayer

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.Invertible

variable {R k : Type u} [CommRing R] [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R))
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (Hom.idealModule i))
  (eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
    twistingSheaf k (ULift.{u} (Fin 2)) 1)
  (I : Ideal R) (β : R →+* k) (hβ : RingHom.ker β = I)
  (hker : (Spec.map (CommRingCat.ofHom β)).ker.comap f = i.ker)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original coefficient quotient tower has the actual successive O_E(n)
layer, constructed through the original kernel inclusions and cokernels. -/
def idealPowerFormalLayerSequence (n : ℕ) : ShortComplex X.Modules := by
  let S := idealPowerLayerSequence i hI eI n
  let hS := idealPowerLayerSequence_shortExact i hI eI n
  let _ : Epi S.g := hS.epi_g
  let a := S.f
  let b := Hom.idealInclusion (i.ker ^ n).subschemeι
  let e₁ : cokernel a ≅ S.X₃ :=
    (cokernelIsCokernel a).coconePointUniqueUpToIso hS.exact.gIsCokernel
  let e₂ : cokernel (a ≫ b) ≅ idealPowerQuotient X (affineFormalFunctionsScalar f)
      (SheafOfModules.unit X.ringCatSheaf) I (n + 1) :=
    cokernelIsoOfEq (idealPowerLayerSequence_f_inclusion i hI eI n) ≪≫
      (idealPowerScalarQuotientIso f i I β hβ hker (n + 1)).symm
  let e₃ := (idealPowerScalarQuotientIso f i I β hβ hker n).symm
  exact cartierSequenceOfIsos (quotientLayerSequence a b) e₁ e₂ e₃

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual formal-functions quotient layer is short exact, with no
assumed exactness or cohomological vanishing input. -/
theorem idealPowerFormalLayerSequence_shortExact (n : ℕ) :
    (idealPowerFormalLayerSequence f i hI eI I β hβ hker n).ShortExact := by
  dsimp only [idealPowerFormalLayerSequence]
  apply cartierSequenceOfIsos_shortExact
  exact quotientLayerSequence_shortExact _ _

end OriginalFormalLayer

end AlgebraicGeometry.Scheme.Surfaces.Contraction.FormalNeighborhood

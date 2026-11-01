/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureProperties
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ZModComparison
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.ShortExact

/-! # Finite abelian local-system closure on qcqs schemes

The actual finite local systems have positive scalar annihilators. A common
positive modulus lifts their original maps to genuine finite-ring modules.
Module weak-Serre closure and the original underlying comparisons give actual
finite abelian kernels, cokernels and extensions. No arbitrary-subobject
closure or finite-generation/finite-cardinality identification over an
infinite ring is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

private theorem finiteTypeLocallyConstant_lift {X : Scheme.{u}}
    (n : ℕ) (F : AbelianSheaf.{u, u + 1} X) (hk : n • 𝟙 F = 0)
    (hF : IsFiniteLocallyConstant F) :
    Modules.IsFiniteTypeLocallyConstant (TorsionZMod.sheaf X.smallEtaleTopology n F hk) :=
  Modules.isFiniteTypeLocallyConstant_of_zmodUnderlying n
    ((isFiniteLocallyConstant_iff_of_iso
      (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hk)).mpr hF)

private theorem common_annihilator {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : AbelianSheaf.{u, u + 1} X}
    (hF : IsFiniteLocallyConstant F) (hG : IsFiniteLocallyConstant G) :
    ∃ n : ℕ, 0 < n ∧ n • 𝟙 F = 0 ∧ n • 𝟙 G = 0 := by
  obtain ⟨a, ha, hFa⟩ := exists_positive_annihilator_of_finiteLocallyConstant F hF
  obtain ⟨b, hb, hGb⟩ := exists_positive_annihilator_of_finiteLocallyConstant G hG
  refine ⟨a * b, Nat.mul_pos ha hb, ?_, ?_⟩
  · rw [Nat.mul_comm, mul_smul, hFa, nsmul_zero]
  · rw [mul_smul, hGb, nsmul_zero]

/-- Kernels between actual finite abelian local systems on a qcqs scheme
remain finite local systems, via a common positive finite coefficient ring. -/
theorem isFiniteLocallyConstant_kernel_of_qcqs {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G)
    (hF : IsFiniteLocallyConstant F) (hG : IsFiniteLocallyConstant G) :
    IsFiniteLocallyConstant (kernel f) := by
  obtain ⟨n, hn, hkF, hkG⟩ := common_annihilator hF hG
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let U := Modules.moduleUnderlying (ZMod n) X
  let fn := TorsionZMod.sheafMap X.smallEtaleTopology n hkF hkG f
  let e : U.obj (kernel fn) ≅ kernel f :=
    PreservesKernel.iso U fn ≪≫ kernel.mapIso (U.map fn) f
      (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hkF)
      (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n G hkG)
      (TorsionZMod.sheafMap_underlying X.smallEtaleTopology n hkF hkG f)
  exact (isFiniteLocallyConstant_iff_of_iso e).mp
    (Modules.isFiniteLocallyConstant_underlying
      (Modules.isFiniteTypeLocallyConstant_kernel fn
        (finiteTypeLocallyConstant_lift n F hkF hF)
        (finiteTypeLocallyConstant_lift n G hkG hG)))

/-- Cokernels between actual finite abelian local systems on a qcqs scheme
remain finite local systems, without a chosen presentation of either input. -/
theorem isFiniteLocallyConstant_cokernel_of_qcqs {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G)
    (hF : IsFiniteLocallyConstant F) (hG : IsFiniteLocallyConstant G) :
    IsFiniteLocallyConstant (cokernel f) := by
  obtain ⟨n, hn, hkF, hkG⟩ := common_annihilator hF hG
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let U := Modules.moduleUnderlying (ZMod n) X
  let fn := TorsionZMod.sheafMap X.smallEtaleTopology n hkF hkG f
  let e : U.obj (cokernel fn) ≅ cokernel f :=
    PreservesCokernel.iso U fn ≪≫ cokernel.mapIso (U.map fn) f
      (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hkF)
      (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n G hkG)
      (TorsionZMod.sheafMap_underlying X.smallEtaleTopology n hkF hkG f)
  exact (isFiniteLocallyConstant_iff_of_iso e).mp
    (Modules.isFiniteLocallyConstant_underlying
      (Modules.isFiniteTypeLocallyConstant_cokernel fn
        (finiteTypeLocallyConstant_lift n F hkF hF)
        (finiteTypeLocallyConstant_lift n G hkG hG)))

/-- The original middle term of a short exact sequence with finite abelian
local-system endpoints is a finite local system on a qcqs scheme. -/
theorem isFiniteLocallyConstant_extension_of_qcqs {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (S : ShortComplex (AbelianSheaf.{u, u + 1} X)) (hS : S.ShortExact)
    (h₁ : IsFiniteLocallyConstant S.X₁) (h₃ : IsFiniteLocallyConstant S.X₃) :
    IsFiniteLocallyConstant S.X₂ := by
  obtain ⟨a, ha, hKa⟩ := exists_positive_annihilator_of_finiteLocallyConstant S.X₁ h₁
  obtain ⟨b, hb, hKb⟩ := exists_positive_annihilator_of_finiteLocallyConstant S.X₃ h₃
  let n := a * b
  have hn : 0 < n := Nat.mul_pos ha hb
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hk₁ : n • 𝟙 S.X₁ = 0 := by
    dsimp [n]
    rw [Nat.mul_comm, mul_smul, hKa, nsmul_zero]
  have hk₂ : n • 𝟙 S.X₂ = 0 := hS.nsmul_id_mul_eq_zero a b hKa hKb
  have hk₃ : n • 𝟙 S.X₃ = 0 := by
    dsimp [n]
    rw [mul_smul, hKb, nsmul_zero]
  let T := TorsionZMod.shortComplex X.smallEtaleTopology n S hk₁ hk₂ hk₃
  have hT : T.ShortExact :=
    TorsionZMod.shortComplex_shortExact X.smallEtaleTopology n S hk₁ hk₂ hk₃ hS
  have hM := Modules.isFiniteTypeLocallyConstant_extension T hT
    (finiteTypeLocallyConstant_lift n S.X₁ hk₁ h₁)
    (finiteTypeLocallyConstant_lift n S.X₃ hk₃ h₃)
  exact (isFiniteLocallyConstant_iff_of_iso
    (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n S.X₂ hk₂)).mp
      (Modules.isFiniteLocallyConstant_underlying hM)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

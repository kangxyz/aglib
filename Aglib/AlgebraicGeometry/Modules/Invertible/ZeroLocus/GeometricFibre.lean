/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms
public import Aglib.AlgebraicGeometry.Modules.Restriction.Monomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual geometric-fibre maps and chart regularity

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/Regular.lean`, SHA-256
  `f13d9e70c743fe8b9ef3ea654ed452b773b2112478a90bd156fdff564fcb134f`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open TensorProduct
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit
  X.ringCatSheaf))

/-- The actual pulled line-bundle map on the categorical field fibre, followed by the unit
comparison. -/
def fibreLineBundleMap (K : Type u) [Field K] (t : Spec (.of K) ⟶ S) :
    (show (Limits.pullback f t).Modules from
      (pullbackLineBundle (Limits.pullback.fst f t) L).val) ⟶
    (show (Limits.pullback f t).Modules from SheafOfModules.unit (Limits.pullback f t).ringCatSheaf)
      :=
  (Scheme.Modules.pullback (Limits.pullback.fst f t)).map φ ≫
    (pullbackUnitIso (Limits.pullback.fst f t)).hom

/-- Monicity of the specified actual line-bundle map on every algebraically closed field-valued
fibre. -/
def GeometricFibreRegular : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
    Mono (fibreLineBundleMap f L φ K t)

end AlgebraicGeometry.Scheme.Modules.Invertible
end

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The geometric-fibre hypothesis gives monicity on every open chart of the
actual categorical fibre, for the actual composed Limits.pullback map. -/
theorem geometricFibreRegular_mono_pullback_open {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X)
    (φ : (show X.Modules from L.val) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hφ : GeometricFibreRegular f L φ) (K : Type u) [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ S) {Y : Scheme.{u}}
    (j : Y ⟶ Limits.pullback f t) [IsOpenImmersion j] :
    Mono ((Scheme.Modules.pullback (j ≫ Limits.pullback.fst f t)).map φ) := by
  have hm : Mono (fibreLineBundleMap f L φ K t) := hφ K t
  change Mono ((Scheme.Modules.pullback (Limits.pullback.fst f t)).map φ ≫
    (pullbackUnitIso (Limits.pullback.fst f t)).hom) at hm
  have : Mono ((Scheme.Modules.pullback (Limits.pullback.fst f t)).map φ) :=
    mono_of_mono _ (pullbackUnitIso (Limits.pullback.fst f t)).hom
  have hmono : Mono ((Scheme.Modules.pullback (Limits.pullback.fst f t) ⋙
      Scheme.Modules.pullback j).map φ) := by
    change Mono ((Scheme.Modules.pullback j).map
      ((Scheme.Modules.pullback (Limits.pullback.fst f t)).map φ))
    exact pullback_mono_of_isOpenImmersion j _
  exact (((MorphismProperty.monomorphisms _).arrow_mk_iso_iff (Arrow.isoOfNatIso
    (Scheme.Modules.pullbackComp j (Limits.pullback.fst f t)) (Arrow.mk φ))).mp hmono)

/-- Geometric-fibre monicity restricts to the actual affine tensor-product
chart, compatibly with the original restriction and Limits.pullback functors. -/
theorem geometricFibreRegular_mono_affinePullback {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X)
    (φ : (show X.Modules from L.val) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hφ : GeometricFibreRegular f L φ)
    (V : S.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra Γ(S, V) K] :
    letI := (f.appLE V.val U.val hUV).hom.toAlgebra;
    Mono ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := Γ(S, V)) (A := K) (B := Γ(X, U))).toRingHom))).map
      ((Scheme.Modules.restrictFunctor U.property.fromSpec).map φ)) := by
  let := (f.appLE V.val U.val hUV).hom.toAlgebra
  let tf := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) K))
  let xf := Spec.map (f.appLE V.val U.val hUV)
  let t := tf ≫ V.property.fromSpec
  let α := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := Γ(S, V)) (A := K) (B := Γ(X, U))).toRingHom)
  let j₀ : Limits.pullback tf xf ⟶ Limits.pullback t f :=
    Limits.pullback.map tf xf t f (𝟙 _) U.property.fromSpec V.property.fromSpec
      (by simp [t]) (V.property.SpecMap_appLE_fromSpec f U.property hUV)
  let j : Spec (.of (K ⊗[Γ(S, V)] Γ(X, U))) ⟶ Limits.pullback f t :=
    (pullbackSpecIso Γ(S, V) K Γ(X, U)).inv ≫ j₀ ≫ (pullbackSymmetry t f).hom
  have : IsOpenImmersion j := by dsimp [j, j₀]; infer_instance
  have hj : j ≫ Limits.pullback.fst f t = α ≫ U.property.fromSpec := by
    have hproj :
        (pullbackSpecIso Γ(S, V) K Γ(X, U)).inv ≫
          Limits.pullback.snd tf xf ≫ U.property.fromSpec = α ≫ U.property.fromSpec :=
      pullbackSpecIso_inv_snd_assoc Γ(S, V) K Γ(X, U) U.property.fromSpec
    simpa [j, j₀, α, Category.assoc] using hproj
  have hm := geometricFibreRegular_mono_pullback_open f L φ hφ K t j
  rw [hj] at hm
  have hcomp : Mono ((Scheme.Modules.pullback U.property.fromSpec ⋙
      Scheme.Modules.pullback α).map φ) :=
    (((MorphismProperty.monomorphisms _).arrow_mk_iso_iff (Arrow.isoOfNatIso
      (Scheme.Modules.pullbackComp α U.property.fromSpec).symm (Arrow.mk φ))).mp hm)
  change Mono ((Scheme.Modules.restrictFunctor U.property.fromSpec ⋙
    Scheme.Modules.pullback α).map φ)
  exact (((MorphismProperty.monomorphisms _).arrow_mk_iso_iff (Arrow.isoOfNatIso
    (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.property.fromSpec)
      (Scheme.Modules.pullback α)).symm (Arrow.mk φ))).mp hcomp)

end AlgebraicGeometry.Scheme.Modules.Invertible
end

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

open scoped ChangeOfRings

/-- The actual geometric-fibre hypothesis makes every displayed line-bundle
chart equation regular in the actual affine tensor fibre. -/
theorem geometricFibreRegular_chart_regular {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X)
    (φ : (show X.Modules from L.val) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hφ : GeometricFibreRegular f L φ)
    (V : S.affineOpens) (U : X.affineOpens) (hUV : U.val ≤ f ⁻¹ᵁ V.val)
    (W : X.Opens) (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (hUW : U.val ≤ W) (K : Type u) [Field K] [IsAlgClosed K] [Algebra Γ(S, V) K] :
    letI := (f.appLE V.val U.val hUV).hom.toAlgebra;
    IsSMulRegular (K ⊗[Γ(S, V)] Γ(X, U))
      ((1 : K) ⊗ₜ[Γ(S, V)]
        X.presheaf.map (homOfLE hUW).op (φ.app W (chartGenerator X L.val W e))) := by
  let := (f.appLE V.val U.val hUV).hom.toAlgebra
  let T := K ⊗[Γ(S, V)] Γ(X, U)
  let : Algebra Γ(X, U) T := Algebra.TensorProduct.rightAlgebra
  let M : X.Modules := L.val
  let N : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let := lineBundle_isLocallyFree X L
  have : M.IsQuasicoherent := inferInstance
  have : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.ringCatSheaf))
      (show (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent from
        inferInstance)
  let ψ := (Scheme.Modules.restrictFunctor U.property.fromSpec).map φ
  have : Mono ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) T)))).map ψ) :=
    geometricFibreRegular_mono_affinePullback f L φ hφ V U hUV K
  have hf' := affineChart_pullback_tensor_injective U φ T
  exact _root_.Algebra.isSMulRegular_of_baseChange_injective_of_linearEquiv (R := Γ(X, U)) (T := T)
    (φ.val.app (op U.val)).hom
    (chartSectionEquiv X L.val W e U.val hUW) _
    (lineBundleMap_chart_general L φ W e U.val hUW) hf'

end AlgebraicGeometry.Scheme.Modules.Invertible
end

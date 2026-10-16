/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ZeroLocus
public import Aglib.AlgebraicGeometry.Modules.Invertible.Trivialization
public import Aglib.RingTheory.Flat.Quotient
public import Aglib.RingTheory.Regular.TensorProduct
public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Regularity and quotient flatness in actual line-bundle charts

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, SHA-256
  `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
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
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit
  X.ringCatSheaf))

/-- The local scalar formula does not require the scheme to be integral. -/
theorem lineBundleMap_chart_general (W : X.Opens)
    (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (V : X.Opens) (h : V ≤ W) (m : Γ((show X.Modules from L.val), V)) :
    φ.app V m = chartSectionEquiv X L.val W e V h m *
      X.presheaf.map (homOfLE h).op (φ.app W (chartGenerator X L.val W e)) := by
  have hm : m = chartSectionEquiv X L.val W e V h m •
      L.val.val.map (homOfLE h).op (chartGenerator X L.val W e) := by
    rw [chartGenerator_restrict]
    apply (chartSectionEquiv X L.val W e V h).injective
    rw [_root_.map_smul, LinearEquiv.apply_symm_apply]
    exact (mul_one _).symm
  conv_lhs => rw [hm]
  rw [Scheme.Modules.Hom.app_smul]
  congr 1
  exact PresheafOfModules.naturality_apply φ.val (homOfLE h).op _

/-- On an actual unit chart, the section-image ideal is the actual scalar's principal ideal. -/
theorem sectionImageIdeal_eq_span_chart (W : X.Opens)
    (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (V : X.Opens) (h : V ≤ W) :
    Hom.sectionImageIdeal φ V = Ideal.span
      {X.presheaf.map (homOfLE h).op (φ.app W (chartGenerator X L.val W e))} := by
  apply le_antisymm
  · rintro x ⟨m, rfl⟩
    rw [Ideal.mem_span_singleton']
    exact ⟨chartSectionEquiv X L.val W e V h m,
      (lineBundleMap_chart_general L φ W e V h m).symm⟩
  · apply Ideal.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    refine ⟨(chartSectionEquiv X L.val W e V h).symm 1, ?_⟩
    change φ.app V ((chartSectionEquiv X L.val W e V h).symm 1) = _
    simpa using lineBundleMap_chart_general L φ W e V h
      ((chartSectionEquiv X L.val W e V h).symm 1)

/-- Monicity of the section map in a unit chart is regularity of its specified scalar. -/
theorem app_injective_iff_chart_regular (W : X.Opens)
    (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (V : X.Opens) (h : V ≤ W) :
    Function.Injective (φ.app V) ↔ IsSMulRegular Γ(X, V)
      (X.presheaf.map (homOfLE h).op (φ.app W (chartGenerator X L.val W e))) := by
  let c := chartSectionEquiv X L.val W e V h
  constructor
  · intro hinj r s hrs
    apply c.symm.injective
    apply hinj
    rw [lineBundleMap_chart_general L φ W e V h,
      lineBundleMap_chart_general L φ W e V h]
    change c (c.symm r) * _ = c (c.symm s) * _
    simpa [mul_comm] using hrs
  · intro hreg m n hmn
    apply c.injective
    apply hreg
    change _ * c m = _ * c n
    rw [mul_comm _ (c m), mul_comm _ (c n)]
    exact (lineBundleMap_chart_general L φ W e V h m).symm.trans
      (hmn.trans (lineBundleMap_chart_general L φ W e V h n))

/-- Regularity of all affine chart scalars implies monicity of the original sheaf map. -/
theorem mono_of_affine_chart_regular
    (hreg : ∀ (W : X.Opens)
      (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
      (V : X.Opens), IsAffineOpen V → ∀ h : V ≤ W,
      IsSMulRegular Γ(X, V)
        (X.presheaf.map (homOfLE h).op (φ.app W (chartGenerator X L.val W e)))) :
    Mono φ := by
  have hinj (V : X.Opens) : Function.Injective (φ.app V) := by
    intro s t hst
    have hc : Presheaf.equalizerSieve (F := L.val.val.presheaf) s t ∈
        (Opens.grothendieckTopology X) V := by
      intro x hxV
      obtain ⟨W, hxW, ⟨e⟩⟩ :=
        (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ W ⊓ V from ⟨hxW, hxV⟩) (W ⊓ V).isOpen
      let j : U ⟶ V := homOfLE (hUle.trans inf_le_right)
      refine ⟨U, j, ?_, hxU⟩
      apply (app_injective_iff_chart_regular L φ W e U
        (hUle.trans inf_le_left)).mpr (hreg W e U hU _)
      exact (PresheafOfModules.naturality_apply φ.val j.op s).trans
        ((congrArg (X.presheaf.map j.op) hst).trans
          (PresheafOfModules.naturality_apply φ.val j.op t).symm)
    apply L.val.isSheaf.isSeparated V _ hc
    intro W j hj
    exact hj
  constructor
  intro P a b hab
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  apply hinj V
  exact congrArg (fun k : P ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ↦
    k.app V m) hab

/-- The kernel of the independently constructed zero-scheme map is the
principal ideal of the displayed chart scalar. -/
theorem zeroInclusion_kernel_eq_span_chart (W : X.Opens)
    (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (V : X.affineOpens) (h : V.val ≤ W) :
    RingHom.ker ((Hom.zeroInclusion φ).app V).hom = Ideal.span
      {X.presheaf.map (homOfLE h).op (φ.app W (chartGenerator X L.val W e))} := by
  let := lineBundle_isLocallyFree X L
  let : L.val.IsQuasicoherent := inferInstance
  exact (Hom.zeroInclusion_kernel φ (Hom.imageIdealLocalizes_of_isQuasicoherent φ) V).trans
    (sectionImageIdeal_eq_span_chart L φ W e V.val h)

/-- On affine charts, flatness of the principal quotient is flatness of the
actual section map of the zero-scheme composite. -/
theorem zeroInclusion_flat_section_comp_of_chart_quotient_flat
    {S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (W : X.Opens)
    (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (U : X.affineOpens) (hUW : U.val ≤ W) (hUV : U.val ≤ f ⁻¹ᵁ V)
    (hflat : let := (f.appLE V U.val hUV).hom.toAlgebra;
      Module.Flat Γ(S, V) (Γ(X, U) ⧸ Ideal.span
        {X.presheaf.map (homOfLE hUW).op (φ.app W (chartGenerator X L.val W e))})) :
    (((Hom.zeroInclusion φ).app U).hom.comp (f.appLE V U.val hUV).hom).Flat :=
  _root_.RingHom.flat_comp_of_flat_quotient (f.appLE V U.val hUV).hom
    ((Hom.zeroInclusion φ).app U).hom ((Hom.zeroInclusion φ).app_surjective U U.property) _
    (zeroInclusion_kernel_eq_span_chart L φ W e U hUW) hflat

end AlgebraicGeometry.Scheme.Modules.Invertible
end

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶
  (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- Flatness of all affine chart quotients gives flatness of the actual
zero-scheme composite over the base. -/
theorem flat_zeroInclusion_comp_of_affine_chart_quotient_flat
    (hflat : ∀ (V : S.Opens), IsAffineOpen V → ∀ (W : X.Opens)
      (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
      (U : X.affineOpens) (hUW : U.val ≤ W) (hUV : U.val ≤ f ⁻¹ᵁ V),
      letI := (f.appLE V U.val hUV).hom.toAlgebra;
      Module.Flat Γ(S, V) (Γ(X, U) ⧸ Ideal.span
        {X.presheaf.map (homOfLE hUW).op (φ.app W (chartGenerator X L.val W e))})) :
    Flat (Hom.zeroInclusion φ ≫ f) := by
  apply (IsZariskiLocalAtSource.iff_exists_resLE (P := @Flat)).mpr
  intro z
  let i := Hom.zeroInclusion φ
  obtain ⟨V, hV, hzV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f (i z) ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W, hzW, ⟨e⟩⟩ :=
    (isLocallyRankOne_iff_local_unit X L.val).mp L.property (i z)
  obtain ⟨U, hU, hzU, hUle⟩ := exists_isAffineOpen_mem_and_subset
    (show i z ∈ W ⊓ f ⁻¹ᵁ V from ⟨hzW, hzV⟩)
  have hUW : U ≤ W := hUle.trans inf_le_left
  have hUV : U ≤ f ⁻¹ᵁ V := hUle.trans inf_le_right
  have hZV : i ⁻¹ᵁ U ≤ (i ≫ f) ⁻¹ᵁ V := fun y hy ↦ hUV hy
  refine ⟨V, i ⁻¹ᵁ U, hzU, hZV, ?_⟩
  have : IsAffine V := hV
  have : IsAffine (i ⁻¹ᵁ U) := hU.preimage i
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  change (((i ≫ f).resLE V (i ⁻¹ᵁ U) hZV).app ⊤).hom.Flat
  rw [Scheme.Hom.resLE_app_top, CommRingCat.hom_comp, CommRingCat.hom_comp]
  have he : (i ≫ f).appLE V (i ⁻¹ᵁ U) hZV = f.appLE V U hUV ≫ i.app U := by
    rw [Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE i f V U (i ⁻¹ᵁ U) hUV le_rfl).symm
  have hmid : ((i ≫ f).appLE V (i ⁻¹ᵁ U) hZV).hom.Flat := by
    rw [he, CommRingCat.hom_comp]
    exact zeroInclusion_flat_section_comp_of_chart_quotient_flat L φ f V W e
      ⟨U, hU⟩ hUW hUV (hflat V hV W e ⟨U, hU⟩ hUW hUV)
  exact (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso V.topIso.hom)).comp
    (hmid.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (i ⁻¹ᵁ U).topIso.inv)))

end AlgebraicGeometry.Scheme.Modules.Invertible
end

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Relative affine charts suffice to prove monicity of the actual line-bundle
map; no single affine chart of the target has to contain an entire source chart. -/
theorem mono_of_relative_affine_chart_regular {X S : Scheme.{u}}
    (f : X ⟶ S) (L : LineBundle X)
    (φ : (show X.Modules from L.val) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hreg : ∀ (V : S.affineOpens) (W : X.Opens)
      (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
      (U : X.affineOpens) (hUW : U.val ≤ W) (_ : U.val ≤ f ⁻¹ᵁ V.val),
      IsSMulRegular Γ(X, U)
        (X.presheaf.map (homOfLE hUW).op (φ.app W (chartGenerator X L.val W e)))) :
    Mono φ := by
  apply moduleHom_mono_of_app_injective
  intro V s t hst
  have hc : Presheaf.equalizerSieve (F := L.val.val.presheaf) s t ∈
      (Opens.grothendieckTopology X) V := by
    intro x hxV
    obtain ⟨W, hxW, ⟨e⟩⟩ :=
      (isLocallyRankOne_iff_local_unit X L.val).mp L.property x
    obtain ⟨V₀, hV₀, hxV₀, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUle⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (W ⊓ V) ⊓ f ⁻¹ᵁ V₀ from ⟨⟨hxW, hxV⟩, hxV₀⟩)
    have hUW : U ≤ W := hUle.trans (inf_le_left.trans inf_le_left)
    have hUV : U ≤ V := hUle.trans (inf_le_left.trans inf_le_right)
    have hUV₀ : U ≤ f ⁻¹ᵁ V₀ := hUle.trans inf_le_right
    let j : U ⟶ V := homOfLE hUV
    refine ⟨U, j, ?_, hxU⟩
    apply (app_injective_iff_chart_regular L φ W e U hUW).mpr
      (hreg ⟨V₀, hV₀⟩ W e ⟨U, hU⟩ hUW hUV₀)
    exact (PresheafOfModules.naturality_apply φ.val j.op s).trans
      ((congrArg (X.presheaf.map j.op) hst).trans
        (PresheafOfModules.naturality_apply φ.val j.op t).symm)
  apply L.val.isSheaf.isSeparated V _ hc
  intro W j hj
  exact hj

end AlgebraicGeometry.Scheme.Modules.Invertible
end

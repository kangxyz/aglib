/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Thickening
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# A free generator of the square-zero ideal of a split thickening

For a split square-zero thickening `i : X ⟶ Y`, `p : Y ⟶ X`, `i ≫ p = 𝟙 X`, an
`IdealGenerator` is a global section `ε` of `Y` killed by `i^♯` such that, on every affine
open `W` of `X`, `a ↦ ε · p^♯ a` is injective on `Γ(X, W)` with image the kernel of the
closed-fibre map. The dual numbers `X[ε] = X ×_k Spec k[ε]` are the example
(Kleiman, arXiv:math/0504020v1, proof of Thm 5.11, where `ε𝒪_{X[ε]} ≅ 𝒪_X` is implicit in
the truncated exponential sequence, p. 43).

* `IdealGenerator.mulMap`: the map of abelian sheaves `𝒪_X ⟶ p_* 𝒪_Y`, `a ↦ ε · p^♯ a`.
* `IdealGenerator.kernelIso`: `𝒪_X ≅ I` onto the original additive kernel, checked
  through monomorphism and local surjectivity on affine opens.
* `IdealGenerator.unitsComplex_shortExact`: the sequence
  `0 → 𝒪_X → (p_* 𝒪_Y)^* → 𝒪_X^* → 1`, with first map `a ↦ 1 + ε a`, is short exact.
* `IdealGenerator.cohomologyEquiv`, `picardKerEquiv`, `picardEquiv`: `H^n(I) ≃+ H^n(X, 𝒪_X)`;
  under a unit-cohomology comparison, `ker(Pic(Y) → Pic(X)) ≃+ H^1(X, 𝒪_X)` and
  `Pic(Y) ≃+ Pic(X) × H^1(X, 𝒪_X)`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

namespace AlgebraicGeometry.Scheme.SplitThickening

universe u

variable {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X)

/-- The restriction of a global section of `Y` to `p ⁻¹ᵁ U`. -/
abbrev restrictTop (ε : Γ(Y, ⊤)) (U : X.Opens) : Γ(Y, p ⁻¹ᵁ U) :=
  (Y.presheaf.map (homOfLE le_top).op).hom ε

theorem restrictTop_restrict (ε : Γ(Y, ⊤)) {U V : X.Opens} (k : op (p ⁻¹ᵁ U) ⟶ op (p ⁻¹ᵁ V)) :
    (Y.presheaf.map k).hom (restrictTop p ε U) = restrictTop p ε V := by
  have e : Y.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op ≫ Y.presheaf.map k =
      Y.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    exact congrArg Y.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  exact congrArg (fun φ => φ.hom ε) e

theorem reduction_restrictTop (ε : Γ(Y, ⊤)) (hε : (i.app ⊤).hom ε = 0) (U : X.Opens) :
    ((reduction i p h).hom.app (op U)).hom (restrictTop p ε U) = 0 := by
  have e := congrArg (fun φ => φ.hom ε) (i.naturality (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  change (X.presheaf.map _).hom ((i.app (p ⁻¹ᵁ U)).hom (restrictTop p ε U)) = 0
  rw [restrictTop, e, hε, map_zero, map_zero]

theorem reduction_projection (U : X.Opensᵒᵖ) (a : Γ(X, U.unop)) :
    ((reduction i p h).hom.app U).hom ((p.app U.unop).hom a) = a :=
  congrArg (fun φ : X.sheaf ⟶ X.sheaf => (φ.hom.app U).hom a) (projectionMap_reduction i p h)

/-- A global section `ε` of `Y`, killed by `i^♯`, that freely generates the kernel of the
closed-fibre map over `𝒪_X` on every affine open of `X`. -/
structure IdealGenerator where
  /-- The generator. -/
  ε : Γ(Y, ⊤)
  eps_mul_self : ε * ε = 0
  app_top_eps : (i.app ⊤).hom ε = 0
  injective : ∀ W : X.Opens, IsAffineOpen W →
    Function.Injective fun a : Γ(X, W) => restrictTop p ε W * (p.app W).hom a
  exists_eq : ∀ W : X.Opens, IsAffineOpen W → ∀ b : Γ(Y, p ⁻¹ᵁ W),
    ((reduction i p h).hom.app (op W)).hom b = 0 →
      ∃ a : Γ(X, W), restrictTop p ε W * (p.app W).hom a = b

namespace IdealGenerator

variable {i p h} (G : IdealGenerator i p h)

/-- The value of multiplication by the generator on sections over `U`. -/
def mulApp (U : X.Opens) : Γ(X, U) →+ Γ(Y, p ⁻¹ᵁ U) where
  toFun a := restrictTop p G.ε U * (p.app U).hom a
  map_zero' := by rw [map_zero, mul_zero]
  map_add' a b := by rw [map_add, mul_add]

theorem mulApp_restrict {U V : X.Opens} (g : V ≤ U) (a : Γ(X, U)) :
    (Y.presheaf.map (homOfLE ((Opens.map p.base).monotone g)).op).hom (G.mulApp U a) =
      G.mulApp V ((X.presheaf.map (homOfLE g).op).hom a) := by
  change (Y.presheaf.map _).hom (restrictTop p G.ε U * (p.app U).hom a) =
    restrictTop p G.ε V * (p.app V).hom ((X.presheaf.map (homOfLE g).op).hom a)
  rw [map_mul, restrictTop_restrict]
  congr 1
  have e := congrArg (fun φ => φ.hom a) (p.naturality (homOfLE g).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e.symm

/-- Multiplication by the generator, `a ↦ ε · p^♯ a`, as a map of abelian sheaves
`𝒪_X ⟶ p_* 𝒪_Y`. -/
def mulMap : Scheme.structureAddSheaf X ⟶ Sheaf.additive.{u, u, u} (ringSheaf p) :=
  ObjectProperty.homMk
  { app := fun U => AddCommGrpCat.ofHom (G.mulApp U.unop)
    naturality := by
      intro U V g
      ext a
      exact (G.mulApp_restrict (leOfHom g.unop) a).symm }

theorem mulMap_app_apply (U : X.Opensᵒᵖ) (a : Γ(X, U.unop)) :
    G.mulMap.hom.app U a = restrictTop p G.ε U.unop * (p.app U.unop).hom a := rfl

/-- Restrictions of kernel sections to affine opens are multiples of the generator. -/
theorem exists_restrict_eq {U : X.Opens} (t : Γ(Y, p ⁻¹ᵁ U))
    (ht : ((reduction i p h).hom.app (op U)).hom t = 0) (W : X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ U) : ∃ a : Γ(X, W),
      (Y.presheaf.map (homOfLE ((Opens.map p.base).monotone hle)).op).hom t =
        restrictTop p G.ε W * (p.app W).hom a := by
  obtain ⟨a, ha⟩ := G.exists_eq W hW
    ((Y.presheaf.map (homOfLE ((Opens.map p.base).monotone hle)).op).hom t) (by
      have e := congrArg (fun φ => φ.hom t) ((reduction i p h).hom.naturality (homOfLE hle).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
      exact e.trans (by rw [ht, map_zero]))
  exact ⟨a, ha.symm⟩

include G in
/-- The section kernels of the closed-fibre map are square-zero, because `ε ^ 2 = 0`. -/
theorem reduction_ker_sq (U : X.Opensᵒᵖ) :
    RingHom.ker ((reduction i p h).hom.app U).hom ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  apply Ideal.mem_bot.mpr
  apply eq_zero_of_local (x * y)
  intro z hz
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show p z ∈ U.unop from hz) U.unop.2
  have hle : W ≤ U.unop := hWU
  refine ⟨p ⁻¹ᵁ W, (Opens.map p.base).monotone hle, hzW, ?_⟩
  obtain ⟨a, ha⟩ := G.exists_restrict_eq x (RingHom.mem_ker.mp hx) W hW hle
  obtain ⟨b, hb⟩ := G.exists_restrict_eq y (RingHom.mem_ker.mp hy) W hW hle
  have hε : restrictTop p G.ε W * restrictTop p G.ε W = 0 := by
    rw [← map_mul, G.eps_mul_self, map_zero]
  rw [map_mul, ha, hb]
  calc restrictTop p G.ε W * (p.app W).hom a * (restrictTop p G.ε W * (p.app W).hom b) =
        (restrictTop p G.ε W * restrictTop p G.ε W) * ((p.app W).hom a * (p.app W).hom b) := by
          ring
    _ = 0 := by rw [hε, zero_mul]

theorem mulApp_injective (U : X.Opens) : Function.Injective (G.mulApp U) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_forall_affine a
  intro W hW hWU
  apply G.injective W hW
  change G.mulApp W _ = restrictTop p G.ε W * (p.app W).hom 0
  rw [← G.mulApp_restrict hWU, ha, map_zero, map_zero, mul_zero]

theorem mulMap_comp_additiveMap :
    G.mulMap ≫ Sheaf.additiveMap.{u, u, u} (reduction i p h) = 0 := by
  ext U a
  change ((reduction i p h).hom.app U).hom (restrictTop p G.ε U.unop * (p.app U.unop).hom a) = 0
  rw [map_mul, reduction_restrictTop i p h G.ε G.app_top_eps, zero_mul]

/-- The comparison `𝒪_X ⟶ I` into the original additive kernel. -/
def kernelMap : Scheme.structureAddSheaf X ⟶ idealSheaf i p h :=
  kernel.lift _ G.mulMap G.mulMap_comp_additiveMap

@[reassoc (attr := simp)]
theorem kernelMap_ι : G.kernelMap ≫ kernel.ι (Sheaf.additiveMap.{u, u, u} (reduction i p h)) =
    G.mulMap :=
  kernel.lift_ι _ _ _

instance mono_mulMap : Mono G.mulMap := by
  apply (sheafToPresheaf _ _).mono_of_mono_map
  have : ∀ U : X.Opensᵒᵖ, Mono (G.mulMap.hom.app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).mpr (G.mulApp_injective U.unop)
  exact NatTrans.mono_of_mono_app G.mulMap.hom

instance mono_kernelMap : Mono G.kernelMap :=
  mono_of_mono_fac G.kernelMap_ι

theorem ι_app_injective (U : X.Opensᵒᵖ) :
    Function.Injective
      ((kernel.ι (Sheaf.additiveMap.{u, u, u} (reduction i p h))).hom.app U) := by
  have : Mono (kernel.ι (Sheaf.additiveMap.{u, u, u} (reduction i p h))).hom :=
    (sheafToPresheaf _ _).map_mono _
  exact (AddCommGrpCat.mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp this U)

instance isLocallySurjective_kernelMap :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) G.kernelMap.hom where
  imageSieve_mem {U} x := by
    intro z hz
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hz U.2
    have hle : W ≤ U := hWU
    refine ⟨W, homOfLE hle, ?_, hzW⟩
    let ι := kernel.ι (Sheaf.additiveMap.{u, u, u} (reduction i p h))
    let x' := (idealSheaf i p h).obj.map (homOfLE hle).op x
    have hb : ((reduction i p h).hom.app (op W)).hom (ι.hom.app (op W) x') = 0 := by
      have e := congrArg (fun φ : idealSheaf i p h ⟶ Sheaf.additive.{u, u, u} X.sheaf =>
        φ.hom.app (op W) x') (kernel.condition (Sheaf.additiveMap.{u, u, u} (reduction i p h)))
      exact e
    obtain ⟨a, ha⟩ := G.exists_eq W hW _ hb
    refine ⟨a, ι_app_injective (i := i) (p := p) (h := h) (op W) ?_⟩
    have e := congrArg (fun φ : Scheme.structureAddSheaf X ⟶ Sheaf.additive.{u, u, u}
      (ringSheaf p) => φ.hom.app (op W) a) G.kernelMap_ι
    exact e.trans ha

instance epi_kernelMap : Epi G.kernelMap :=
  Sheaf.epi_of_isLocallySurjective _

instance isIso_kernelMap : IsIso G.kernelMap :=
  isIso_of_mono_of_epi _

/-- The original additive kernel of the closed-fibre map is `𝒪_X`, through `a ↦ ε a`. -/
def kernelIso : Scheme.structureAddSheaf X ≅ idealSheaf i p h :=
  asIso G.kernelMap

/-- `H^n(I) ≃+ H^n(X, 𝒪_X)` through the generator. -/
def cohomologyEquiv (n : ℕ) :
    Sheaf.H (idealSheaf i p h) n ≃+ Sheaf.H (Scheme.structureAddSheaf X) n where
  toFun := Sheaf.H.map G.kernelIso.inv n
  invFun := Sheaf.H.map G.kernelIso.hom n
  left_inv x := by
    rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
  right_inv x := by
    rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
  map_add' x y := map_add _ x y

@[simp]
theorem cohomologyEquiv_symm_apply (n : ℕ) (x : Sheaf.H (Scheme.structureAddSheaf X) n) :
    (G.cohomologyEquiv n).symm x = Sheaf.H.map G.kernelMap n x := rfl

/-- The first map of the unit sequence, `a ↦ 1 + ε · p^♯ a`. -/
def oneAddMap : Scheme.structureAddSheaf X ⟶ (ringSheaf p).units :=
  G.kernelMap ≫ oneAddUnits i p h G.reduction_ker_sq

theorem oneAddMap_app_apply (U : X.Opensᵒᵖ) (a : Γ(X, U.unop)) :
    ((G.oneAddMap.hom.app U a).toMul : (Γ(Y, p ⁻¹ᵁ U.unop))ˣ).val =
      1 + restrictTop p G.ε U.unop * (p.app U.unop).hom a := by
  have e := congrArg (fun φ : Scheme.structureAddSheaf X ⟶ Sheaf.additive.{u, u, u}
    (ringSheaf p) => φ.hom.app U a) G.kernelMap_ι
  have e' : ((Sheaf.additiveKernelSectionHom.{u, u, u} (reduction i p h) U
      (G.kernelMap.hom.app U a)).val : Γ(Y, p ⁻¹ᵁ U.unop)) =
        restrictTop p G.ε U.unop * (p.app U.unop).hom a := e
  exact (Sheaf.coe_oneAddUnits.{u, u, u} (reduction i p h) G.reduction_ker_sq U _).trans
    (congrArg (fun r : Γ(Y, p ⁻¹ᵁ U.unop) => 1 + r) e')

/-- The sequence `0 → 𝒪_X → (p_* 𝒪_Y)^* → 𝒪_X^* → 1` with first map `a ↦ 1 + ε a`. -/
abbrev unitsComplex : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk G.oneAddMap (Sheaf.unitsMap (reduction i p h)) (by
    rw [oneAddMap, Category.assoc]
    change G.kernelMap ≫ (SplitThickening.unitsComplex i p h G.reduction_ker_sq).f ≫
      (SplitThickening.unitsComplex i p h G.reduction_ker_sq).g = 0
    rw [ShortComplex.zero, comp_zero])

/-- Comparison with the original square-zero unit sequence. -/
def unitsComplexIso : G.unitsComplex ≅ SplitThickening.unitsComplex i p h G.reduction_ker_sq :=
  ShortComplex.isoMk G.kernelIso (Iso.refl _) (Iso.refl _) (by
    change G.kernelMap ≫ oneAddUnits i p h G.reduction_ker_sq = G.oneAddMap ≫ 𝟙 _
    rw [Category.comp_id]
    rfl) (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

theorem unitsComplex_shortExact : G.unitsComplex.ShortExact :=
  ShortComplex.shortExact_of_iso G.unitsComplexIso.symm
    (SplitThickening.unitsComplex_shortExact i p h G.reduction_ker_sq)

/-- The sequence `0 → 𝒪_X → (p_* 𝒪_Y)^* → 𝒪_X^* → 1` is split by `p^♯`. -/
def unitsSplitting : G.unitsComplex.Splitting :=
  (SplitThickening.unitsSplitting i p h G.reduction_ker_sq).ofIso G.unitsComplexIso.symm

/-- Under a unit-cohomology comparison, `ker(i^* : Pic(Y) → Pic(X)) ≃+ H^1(X, 𝒪_X)`. -/
def picardKerEquiv (C : UnitsCohomologyComparison i p h) :
    (pullbackHom i).ker ≃+ Sheaf.H (Scheme.structureAddSheaf X) 1 :=
  (SplitThickening.picardKerEquiv i p h G.reduction_ker_sq C).trans (G.cohomologyEquiv 1)

/-- Under a unit-cohomology comparison, `Pic(Y) ≃+ Pic(X) × H^1(X, 𝒪_X)` through the
retraction; the first component is `i^*`. -/
def picardEquiv (C : UnitsCohomologyComparison i p h) :
    PicardGroup Y ≃+ PicardGroup X × Sheaf.H (Scheme.structureAddSheaf X) 1 :=
  (SplitThickening.picardEquiv i p h G.reduction_ker_sq C).trans
    (AddEquiv.prodCongr (AddEquiv.refl _) (G.cohomologyEquiv 1))

end IdealGenerator

end AlgebraicGeometry.Scheme.SplitThickening

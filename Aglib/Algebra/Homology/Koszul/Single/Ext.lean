/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Single
public import Aglib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The original one-element Koszul Ext class

The actual multiplication resolution of a regular scalar gives the native
linear degree-one Ext class of each coefficient element. The defining
cocycle is the original map from the free rank-one resolution term. This
retains its native scalar action, without replacing Ext by a quotient type.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ZeroObject

universe u w

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a) (N : ModuleCat.{u} R)

/-- The original degree-one Koszul cocycle associated with a coefficient element. -/
def singleExtOneClass :
    N →ₗ[R] Ext (ModuleCat.of R (SingleQuotient R a)) N 1 := by
  let P := singleProjectiveResolution R a ha
  let c (x : N) : P.complex.X 1 ⟶ N :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)
  have hc (x : N) : P.complex.d 2 1 ≫ c x = 0 := by
    change (singleComplex R a).d (0 + 2) (0 + 1) ≫ c x = 0
    rw [singleComplex_d_add_two]
    exact zero_comp
  refine {
    toFun := fun x => P.extMk (c x) 2 rfl (hc x)
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    rw [P.add_extMk]
    congr 1
    ext
    simp [c, LinearMap.toSpanSingleton_apply, smul_add]
  · intro r x
    rw [Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
    congr 1
    ext
    simp [c, LinearMap.toSpanSingleton_apply, smul_comm]

/-- The linear class map is the literal original cocycle in the actual
one-element projective resolution. -/
theorem singleExtOneClass_apply (x : N) :
    singleExtOneClass a ha N x =
      (singleProjectiveResolution R a ha).extMk
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)) 2 rfl (by
          change (singleComplex R a).d (0 + 2) (0 + 1) ≫ _ = 0
          rw [singleComplex_d_add_two]
          exact zero_comp) := rfl

/-- Every native degree-one Ext class is represented by an actual coefficient
in the rank-one Koszul term. -/
theorem singleExtOneClass_surjective : Function.Surjective (singleExtOneClass a ha N) := by
  let P := singleProjectiveResolution R a ha
  intro e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e 2 rfl
  let f₀ : ModuleCat.of R R ⟶ N := f
  have hF : ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f₀.hom (1 : R))) = f₀ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r • f₀.hom 1 = f₀.hom r
    simpa only [smul_eq_mul, mul_one] using (f₀.hom.map_smul r (1 : R)).symm
  refine ⟨f₀.hom (1 : R), ?_⟩
  rw [singleExtOneClass_apply]
  change P.extMk (ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f₀.hom (1 : R))))
      2 rfl _ = P.extMk f 2 rfl hf
  congr 1

/-- The original class vanishes exactly on scalar multiples, as detected by
the original boundary in degree zero of the same resolution. -/
theorem singleExtOneClass_eq_zero_iff (x : N) :
    singleExtOneClass a ha N x = 0 ↔
      x ∈ LinearMap.range (LinearMap.lsmul R N a) := by
  let P := singleProjectiveResolution R a ha
  rw [singleExtOneClass_apply]
  rw [P.extMk_eq_zero_iff _ 2 rfl _ 0 rfl]
  constructor
  · rintro ⟨g, hg⟩
    let g₀ : ModuleCat.of R R ⟶ N := g
    refine ⟨g₀.hom (1 : R), ?_⟩
    change a • g₀.hom (1 : R) = x
    change (singleComplex R a).d 1 0 ≫ g₀ = _ at hg
    rw [singleComplex_d_one_zero] at hg
    change ModuleCat.ofHom (LinearMap.lsmul R R a) ≫ g₀ =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R N x) at hg
    have he := ConcreteCategory.congr_hom hg (1 : R)
    change g₀.hom (a • (1 : R)) = (1 : R) • x at he
    simpa only [g₀.hom.map_smul, one_smul] using he
  · rintro ⟨y, hy⟩
    change a • y = x at hy
    refine ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton R N y), ?_⟩
    change (singleComplex R a).d 1 0 ≫ _ = _
    rw [singleComplex_d_one_zero]
    change ModuleCat.ofHom (LinearMap.lsmul R R a) ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R N y) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (a * r) • y = r • x
    rw [mul_smul, ← hy]
    exact smul_comm a r y

/-- The literal kernel of the original class map is the scalar-multiplication
image on the original coefficient module. -/
theorem singleExtOneClass_ker :
    LinearMap.ker (singleExtOneClass a ha N) =
      LinearMap.range (LinearMap.lsmul R N a) := by
  ext x
  exact singleExtOneClass_eq_zero_iff a ha N x

/-- The actual coefficient quotient computes the native degree-one Ext group
through the original Koszul class, with its original R-scalar action. -/
def singleExtOneLinearEquiv :
    SingleQuotient N a ≃ₗ[R] Ext (ModuleCat.of R (SingleQuotient R a)) N 1 :=
  (Submodule.quotEquivOfEq _ _ (singleExtOneClass_ker a ha N).symm).trans
    ((singleExtOneClass a ha N).quotKerEquivOfSurjective
      (singleExtOneClass_surjective a ha N))

/-- A quotient representative is sent to its original Koszul Ext class. -/
@[simp]
theorem singleExtOneLinearEquiv_apply_mk (x : N) :
    singleExtOneLinearEquiv a ha N (Submodule.Quotient.mk x) =
      singleExtOneClass a ha N x := by
  simp only [singleExtOneLinearEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Changing coefficients retains the original cocycle and native Yoneda
postcomposition, on the same projective resolution. -/
@[simp]
theorem singleExtOneClass_comp_mk₀ {N' : ModuleCat.{u} R} (g : N ⟶ N') (x : N) :
    (singleExtOneClass a ha N x).comp (Ext.mk₀ g) (add_zero 1) =
      singleExtOneClass a ha N' (g x) := by
  rw [singleExtOneClass_apply, singleExtOneClass_apply,
    ProjectiveResolution.extMk_comp_mk₀]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change g.hom (r • x) = r • g.hom x
  exact g.hom.map_smul r x

/-- Regularity on the coefficient kills degree-zero Ext from the scalar
quotient. Source regularity is not needed for this degree-zero assertion. -/
theorem singleExtZero_eq_zero_of_regular (hN : IsSMulRegular N a)
    (e : Ext (ModuleCat.of R (SingleQuotient R a)) N 0) : e = 0 := by
  let g : ModuleCat.of R (SingleQuotient R a) ⟶ N := (Ext.linearEquiv₀ (R := R)) e
  let p : ModuleCat.of R R ⟶ ModuleCat.of R (SingleQuotient R a) :=
    singleAugmentationMap R a
  let l : ModuleCat.of R R ⟶ N := p ≫ g
  have hpa : p.hom a = 0 := by
    change (LinearMap.range (LinearMap.lsmul R R a)).mkQ a = 0
    exact (Submodule.Quotient.mk_eq_zero (p := _)).mpr ⟨1, by simp⟩
  have hla : l.hom a = 0 := by
    change g.hom (p.hom a) = 0
    rw [hpa, g.hom.map_zero]
  have hla' : a • l.hom (1 : R) = 0 := by
    have h := (l.hom.map_smul a (1 : R)).symm
    simpa only [smul_eq_mul, mul_one, hla] using h
  have hl₁ : l.hom (1 : R) = 0 := hN (hla'.trans (smul_zero a).symm)
  have hl : l = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change l.hom r = 0
    simpa only [smul_eq_mul, mul_one, hl₁, smul_zero] using l.hom.map_smul r (1 : R)
  have hg : g = 0 := by
    apply (cancel_epi p).mp
    simpa only [comp_zero] using hl
  apply (Ext.linearEquiv₀ (R := R)).injective
  simpa only [map_zero] using hg

omit [HasExt.{w} (ModuleCat.{u} R)] in
include ha in
/-- The actual multiplication resolution bounds the native projective
dimension of its original module quotient by one. -/
theorem singleQuotient_hasProjectiveDimensionLE :
    HasProjectiveDimensionLE (ModuleCat.of R (SingleQuotient R a)) 1 := by
  apply (singleProjectiveResolution R a ha).hasProjectiveDimensionLE_of_isZero_X 1
  intro i hi
  obtain (_ | _ | i) := i
  · omega
  · omega
  · change IsZero (0 : ModuleCat R)
    exact isZero_zero _

include ha in
/-- Every native Ext class above degree one vanishes for the original scalar
quotient, without regularity or finiteness assumptions on the coefficient. -/
theorem singleExt_eq_zero_above_one (n : ℕ) (hn : 1 < n)
    (e : Ext (ModuleCat.of R (SingleQuotient R a)) N n) : e = 0 := by
  let := singleQuotient_hasProjectiveDimensionLE a ha
  exact e.eq_zero_of_hasProjectiveDimensionLT 2 (by omega)

include ha in
/-- If the scalar is regular on both source ring and coefficient, the
original Ext groups are concentrated in degree one. -/
theorem singleExt_eq_zero_of_ne_one (hN : IsSMulRegular N a) (n : ℕ) (hn : n ≠ 1)
    (e : Ext (ModuleCat.of R (SingleQuotient R a)) N n) : e = 0 := by
  cases n with
  | zero => exact singleExtZero_eq_zero_of_regular a N hN e
  | succ n => exact singleExt_eq_zero_above_one a ha N (n + 1) (by omega) e

end ChainComplex.Koszul

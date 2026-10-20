/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Trivial.Sections
public import Aglib.AlgebraicGeometry.Curves.Picard.RationalTrivialization
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/

open _root_.AlgebraicGeometry.Scheme.Modules (locallyBijective_of_local_isIso)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne LineBundle PicardGroup classOf classOf_dual classOf_tensor class_eq_iff
    dualLineBundle tensorLineBundle trivialLineBundle)

/-!
# Constructive divisor/Picard equivalence and actual line-bundle degree

C2, K2-018 `lem:k2018-geometric-exact-order`, frozen basis `7f86e4a`.
On an integral Noetherian scheme of dimension at most one with actual closed
DVR stalks, every actual locally rank-one module sheaf is isomorphic to the
fractional-ideal sheaf O(D). The map is the previously constructed rational
embedding; local rank-one charts identify it with multiplication by their
nonzero rational generators. Its divisor coefficient is minus the generator
order, so the convention is ord(s) + D >= 0.

Conversely, an actual isomorphism O(D) with the structure module gives a
nonzero global generator z with ord(z) + D = 0. Thus D = div(z inverse).
This proves injectivity, rather than assuming the divisor/Picard comparison.
The full additive equivalence uses the proved tensor multiplication iso.

Residue-weighted degree transfers through this actual inverse. The only
additional degree input is the explicit principal product formula from
Degree.lean, whose universal proper-curve formulation is Stacks Tag 02RU.
Tensor, dual, isomorphism invariance, O(D) degree compatibility, and positive
level torsion degree zero are proved. A finite-morphism pullback-degree law
is a separate construction and is not asserted here. Meromorphic-section
source correspondence: Stacks Tags 02SG and 02SH.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme.Modules.Invertible.RationalTrivialization
open AlgebraicGeometry.Scheme.Modules.Trivial
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorInverse
open DivisorClass RationalTrivialization
universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable (M : SheafOfModules.{u} X.ringCatSheaf) (hM : IsLocallyRankOne X M)
variable (U₀ : X.Opens) [Nonempty U₀]
variable (e : M.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))

theorem coordinate_fractional (V : X.Opens) [Nonempty V] (s : M.val.obj (op V)) :
    IsFractionalSection X (divisor X M U₀ e hM) V (coordinate X M U₀ e V s) := by
  by_cases hs : coordinate X M U₀ e V s = 0
  · exact Or.inl hs
  right
  intro x hx
  let c := localChart X M hM x.val
  let W := c.1 ⊓ V
  let : Nonempty c.1 := ⟨⟨x.val, c.2.property⟩⟩
  let : Nonempty W := ⟨⟨x.val, c.2.property, hx⟩⟩
  let t := M.val.map (homOfLE inf_le_right : W ⟶ V).op s
  let a := chartSectionEquiv X M c.1 c.2.val W inf_le_left t
  have he : coordinate X M U₀ e V s =
      X.germToFunctionField W a * coordinate X M U₀ e c.1 (chartGenerator X M c.1 c.2.val) := by
    rw [← coordinate_naturality X M U₀ e (homOfLE inf_le_right : W ⟶ V)]
    exact coordinate_chart X M U₀ e c.1 c.2.val W inf_le_left t
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, map_zero, zero_mul] at he
    exact hs he
  rw [divisor_apply, divisorCoefficient_chart X M U₀ e hM c.1 c.2.val x c.2.property, he]
  have hh := Scheme.ord_le_smul (show x.val ∈ W from ⟨c.2.property, hx⟩) ha
    (coordinate X M U₀ e c.1 (chartGenerator X M c.1 c.2.val))
  change X.ord _ x.val ≤ X.ord (X.germToFunctionField W a * _) x.val at hh
  linarith

def toDivisorSection (V : X.Opens) :
    M.val.obj (op V) →ₗ[Γ(X, V)] (divisorSheaf X (divisor X M U₀ e hM)).val.obj (op V) :=
  (embeddingSection X M U₀ e V).codRestrict _ (by
    intro s
    classical
    by_cases hV : Nonempty V
    · let := hV
      change _ ∈ (fractionalPresheaf X (divisor X M U₀ e hM)).obj (op V)
      simp only [fractionalPresheaf, dite_eq_left hV, Submodule.mem_comap]
      change IsFractionalSection X _ V (rationalValue X V (embeddingSection X M U₀ e V s))
      rw [embeddingSection_value]
      exact coordinate_fractional X M hM U₀ e V s
    · change _ ∈ (fractionalPresheaf X (divisor X M U₀ e hM)).obj (op V)
      simp only [fractionalPresheaf, dite_eq_right hV, Submodule.mem_top])

def toDivisorSheaf : M ⟶ divisorSheaf X (divisor X M U₀ e hM) where
  val := PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (fun V => ConcreteCategory.ofHom (C := ModuleCat Γ(X, V.unop))
      (toDivisorSection X M hM U₀ e V.unop)) (by
      intro U V i
      ext s
      apply Subtype.ext
      exact PresheafOfModules.naturality_apply (embedding X M U₀ e).val i s)

def generatorUnit (W : X.Opens) [Nonempty W]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) : X.functionFieldˣ :=
  Units.mk0 _ (coordinate_generator_ne_zero X M U₀ e hM W d)

theorem generatorUnit_order (W : X.Opens) [Nonempty W]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (x : ClosedPoint X) (hx : x.val ∈ W) :
    X.ord (generatorUnit X M hM U₀ e W d : X.functionField) x.val +
      divisor X M U₀ e hM x = 0 := by
  rw [divisor_apply, divisorCoefficient_chart X M U₀ e hM W d x hx]
  exact add_neg_cancel _

def toDivisorLocalIso (hdim : topologicalKrullDim X ≤ 1) (W : X.Opens) [Nonempty W]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    M.over W ≅ (divisorSheaf X (divisor X M U₀ e hM)).over W :=
  d ≪≫ divisorSheafLocalIso X hdim (divisor X M U₀ e hM) W
    (generatorUnit X M hM U₀ e W d) (generatorUnit_order X M hM U₀ e W d)

theorem toDivisorLocalIso_hom (hdim : topologicalKrullDim X ≤ 1)
    (W : X.Opens) [Nonempty W]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    (toDivisorLocalIso X M hM U₀ e hdim W d).hom.val =
      (_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf W).map (toDivisorSheaf
        X M hM U₀ e).val := by
  ext V s
  apply Subtype.ext
  by_cases hV : Nonempty V.unop.left
  · let := hV
    apply (rationalValueEquiv X V.unop.left).injective
    change rationalValue X V.unop.left
      (sectionTrivialization X hdim _ V.unop.left _ _ (d.hom.val.app V s)).val =
      rationalValue X V.unop.left (embeddingSection X M U₀ e V.unop.left s)
    rw [sectionTrivialization_value, embeddingSection_value,
      coordinate_chart X M U₀ e W d V.unop.left V.unop.hom.le s]
    exact mul_comm _ _
  · have h0 := eq_bot_of_not_nonempty X V.unop.left hV
    have : Subsingleton ((rationalFunctions X).val.obj (op V.unop.left)) := by
      rw [h0]
      exact rational_empty_subsingleton X
    exact this.elim _ _

theorem toDivisorSheaf_isIso (hdim : topologicalKrullDim X ≤ 1) :
    IsIso (toDivisorSheaf X M hM U₀ e) := by
  have hh := locallyBijective_of_local_isIso X (toDivisorSheaf X M hM U₀ e).val (by
    intro x
    let c := localChart X M hM x
    let : Nonempty c.1 := ⟨⟨x, c.2.property⟩⟩
    refine ⟨c.1, c.2.property, ?_⟩
    rw [← toDivisorLocalIso_hom X M hM U₀ e hdim c.1 c.2.val]
    exact Functor.map_isIso (SheafOfModules.forget _) (toDivisorLocalIso X M hM U₀ e hdim c.1
      c.2.val).hom)
  let := hh.1
  let := hh.2
  let : IsIso ((SheafOfModules.forget X.ringCatSheaf).map (toDivisorSheaf X M hM U₀ e)) :=
    _root_.PresheafOfModules.isIso_of_locallyBijective (toDivisorSheaf X M hM U₀ e).val M.isSheaf
    (divisorSheaf X (divisor X M U₀ e hM)).isSheaf
  exact isIso_of_reflects_iso (toDivisorSheaf X M hM U₀ e) (SheafOfModules.forget _)

/-- The actual rational embedding identifies the invertible sheaf with O(D). -/
def toDivisorIso (hdim : topologicalKrullDim X ≤ 1) :
    M ≅ divisorSheaf X (divisor X M U₀ e hM) :=
  letI := toDivisorSheaf_isIso X M hM U₀ e hdim
  asIso (toDivisorSheaf X M hM U₀ e)

include hM in
theorem exists_divisor_iso (hdim : topologicalKrullDim X ≤ 1) :
    ∃ D : Divisor X, Nonempty (M ≅ divisorSheaf X D) := by
  let c := localChart X M hM (genericPoint X)
  let : Nonempty c.1 := ⟨⟨genericPoint X, c.2.property⟩⟩
  exact ⟨divisor X M c.1 c.2.val hM, ⟨toDivisorIso X M hM c.1 c.2.val hdim⟩⟩
theorem trivial_divisor_principal (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X)
    (a : divisorSheaf X D ≅ SheafOfModules.unit X.ringCatSheaf) :
    ∃ f : X.functionFieldˣ, principal X (Additive.ofMul f) = D := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let N := divisorSheaf X D
  let s := globalGenerator X N a
  let z := rationalValue X ⊤ s.val
  have hz : z ≠ 0 := by
    intro hz
    have hv : s.val = 0 := (rationalValueEquiv X ⊤).injective
      (hz.trans (rationalValue X ⊤).map_zero.symm)
    have hs : s = 0 := Subtype.ext hv
    have hh := congrArg (isoSectionEquiv X N a ⊤) hs
    simp [s, globalGenerator] at hh
  have ho (x : ClosedPoint X) : X.ord z x.val + D x = 0 := by
    have hge := (explicitSheafSectionsEquiv X D ⊤ s).property.resolve_left hz x (by trivial)
    change 0 ≤ X.ord z x.val + D x at hge
    obtain ⟨W, hxW, g, hg⟩ := exists_local_principal_function X D x.val
    let : Nonempty W := ⟨⟨x.val, hxW⟩⟩
    let t := sectionTrivialization X hdim D W g hg 1
    let b := isoSectionEquiv X N a W t
    have ht : rationalValue X W t.val = (g : X.functionField) := by
      rw [sectionTrivialization_value, map_one, mul_one]
    have he : (g : X.functionField) = X.germToFunctionField W b * z := by
      rw [← ht]
      have hh := congrArg (fun t : N.val.obj (op W) => rationalValue X W t.val)
        (section_as_smul_generator X N a W t)
      change rationalValue X W t.val = rationalValue X W
        (b • (rationalFunctions X).val.map (homOfLE le_top : W ⟶ ⊤).op s.val) at hh
      rw [_root_.map_smul, rationalValue_restrict] at hh
      exact hh
    have hb : b ≠ 0 := by
      intro hb
      rw [hb, map_zero, zero_mul] at he
      exact g.ne_zero he
    have hle := Scheme.ord_le_smul hxW hb z
    change X.ord z x.val ≤ X.ord (X.germToFunctionField W b * z) x.val at hle
    rw [← he] at hle
    linarith [hg x hxW]
  let z' : X.functionFieldˣ := Units.mk0 z hz
  refine ⟨z'⁻¹, ?_⟩
  ext x
  change X.ord ((z'⁻¹ : X.functionFieldˣ) : X.functionField) x.val = D x
  rw [order_inv]
  change -X.ord z x.val = D x
  linarith [ho x]

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorInverse

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
open DivisorInverse
universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable (hdim : topologicalKrullDim X ≤ 1)

theorem divisorClassToPicard_surjective : Function.Surjective (divisorClassToPicard X hdim) := by
  intro a
  induction a using Quotient.inductionOn with
  | h L =>
    obtain ⟨D, ⟨e⟩⟩ := exists_divisor_iso X L.val L.property hdim
    exact ⟨QuotientAddGroup.mk D, Quotient.sound ⟨e.symm⟩⟩

theorem divisorClassToPicard_injective : Function.Injective (divisorClassToPicard X hdim) := by
  have hker : ∀ a, divisorClassToPicard X hdim a = 0 → a = 0 := by
    intro a
    induction a using Quotient.inductionOn with
    | h D =>
      intro hz
      have hc : classOf X (divisorLineBundle X hdim D) = classOf X (trivialLineBundle X) := hz
      obtain ⟨e⟩ := (class_eq_iff X (divisorLineBundle X hdim D) (trivialLineBundle X)).mp hc
      obtain ⟨f, hf⟩ := trivial_divisor_principal X hdim D
        (e ≪≫ CategoryTheory.Limits.coproductUniqueIso
          (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
      exact (QuotientAddGroup.eq_zero_iff D).mpr ⟨Additive.ofMul f, hf⟩
  intro a b hab
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hab, sub_self]

/-- Full divisor-class/Picard equivalence, using actual invertible sheaves and tensor addition. -/
def divisorPicardEquiv : (Divisor X ⧸ (principal X).range) ≃+ PicardGroup X :=
  AddEquiv.ofBijective (divisorClassToPicard X hdim)
    ⟨divisorClassToPicard_injective X hdim, divisorClassToPicard_surjective X hdim⟩

@[simp] theorem divisorPicardEquiv_mk (D : Divisor X) :
    divisorPicardEquiv X hdim (QuotientAddGroup.mk D) = classOf X (divisorLineBundle X hdim D) :=
      rfl

@[simp] theorem divisorPicardEquiv_symm_divisor (D : Divisor X) :
    (divisorPicardEquiv X hdim).symm (classOf X (divisorLineBundle X hdim D)) =
      QuotientAddGroup.mk D :=
  (divisorPicardEquiv X hdim).symm_apply_apply (QuotientAddGroup.mk D)

/-- The original set-valued divisor-class map is the underlying proved additive equivalence. -/
theorem divisorPicardEquiv_eq_old_map (a : Divisor X ⧸ (principal X).range) :
    divisorPicardEquiv X hdim a = divisorClassToLineBundleClass X hdim a :=
  divisorClassToPicard_eq_old_map X hdim a
end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree
open DivisorClass
universe u
variable {k : Type u} [Field k] (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
variable (p : X ⟶ Spec (.of k)) (hdim : topologicalKrullDim X ≤ 1)
variable (hprod : PrincipalProductFormula X p)

/-- Degree of actual invertible-sheaf classes, transported through the proved inverse. -/
def picardDegree : PicardGroup X →+ ℤ :=
  (divisorClassDegree X p hprod).comp (divisorPicardEquiv X hdim).symm.toAddMonoidHom

/-- Degree of an actual line bundle, invariant under actual module-sheaf isomorphism. -/
def lineBundleDegree (L : LineBundle X) : ℤ := picardDegree X p hdim hprod (classOf X L)

@[simp] theorem picardDegree_divisor (D : Divisor X) :
    picardDegree X p hdim hprod (classOf X (divisorLineBundle X hdim D)) = degDiv X p D := by
  change divisorClassDegree X p hprod ((divisorPicardEquiv X hdim).symm _) = _
  rw [divisorPicardEquiv_symm_divisor, divisorClassDegree_mk]

@[simp] theorem lineBundleDegree_divisor (D : Divisor X) :
    lineBundleDegree X p hdim hprod (divisorLineBundle X hdim D) = degDiv X p D :=
  picardDegree_divisor X p hdim hprod D

theorem lineBundleDegree_iso {L N : LineBundle X} (e : L.val ≅ N.val) :
    lineBundleDegree X p hdim hprod L = lineBundleDegree X p hdim hprod N := by
  unfold lineBundleDegree
  congr 1
  exact Quotient.sound ⟨e⟩

@[simp] theorem lineBundleDegree_tensor (L N : LineBundle X) :
    lineBundleDegree X p hdim hprod (tensorLineBundle X L N) =
      lineBundleDegree X p hdim hprod L + lineBundleDegree X p hdim hprod N := by
  simp [lineBundleDegree, classOf_tensor]

@[simp] theorem lineBundleDegree_dual (L : LineBundle X) :
    lineBundleDegree X p hdim hprod (dualLineBundle X L) = -lineBundleDegree X p hdim hprod L := by
  simp [lineBundleDegree, classOf_dual]

@[simp] theorem lineBundleDegree_trivial :
    lineBundleDegree X p hdim hprod (trivialLineBundle X) = 0 := by
  simp [lineBundleDegree]

/-- The degree-zero subgroup of the actual ordinary Picard group. -/
def picardZero : AddSubgroup (PicardGroup X) := (picardDegree X p hdim hprod).ker

theorem picard_torsion_degree_zero (n : ℕ) (hn : 0 < n) (L : PicardGroup X) (hL : n • L = 0) :
    picardDegree X p hdim hprod L = 0 := by
  have h := congrArg (picardDegree X p hdim hprod) hL
  rw [map_nsmul, map_zero] at h
  exact (nsmul_right_injective (ne_of_gt hn)) h
end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree

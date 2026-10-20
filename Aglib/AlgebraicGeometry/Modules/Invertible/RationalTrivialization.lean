/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Points.Closed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Aglib.AlgebraicGeometry.Modules.RationalFunctions
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Trivialization

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.RationalTrivialization` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0fb897eddf1088b67bef21f948d5462be3e5e718961c6e3ac4e23dfd48df71d5`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne isLocallyRankOne_iff_local_unit)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Rational trivialization of an actual invertible sheaf

C2, K2-018 `lem:k2018-geometric-exact-order`, frozen source basis `7f86e4a`.
For an integral scheme, restrictions of a locally rank-one module sheaf to
nonempty subopens are injective. A chosen nonempty trivializing chart gives
an injective function-field coordinate, with the actual restriction and
scalar laws. The actual morphism into the generic direct-image rational
sheaf has zero empty-open sections, rather than a constant-field value there.

On a Noetherian integral scheme, the negative orders of the local generator
coordinates give a genuine finitely supported closed-point divisor. Changing
the local chart preserves its coefficient: both change-of-basis directions
are regular. Support lies in the codimension-one part of the complement of
the generic chart, which is finite by Noetherianity. The degree-one case is
consumed by the subsequent O(D) inverse construction. No divisor/Picard
identification or rational-trivialization existence is assumed. The DVR
hypotheses used by the fractional-section infrastructure remain explicit.
Sources: Stacks Tags 02SG and 02SH (meromorphic sections and their divisors).
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible.RationalTrivialization
universe u
variable (X : Scheme.{u}) [IsIntegral X]

theorem generic_mem_open (U : X.Opens) [hU : Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

theorem nonempty_inf (U V : X.Opens) [Nonempty U] [Nonempty V] : Nonempty ((U ⊓ V) : X.Opens) :=
  ⟨⟨genericPoint X, generic_mem_open X U, generic_mem_open X V⟩⟩

theorem germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V] (i : U ⟶ V) (a : Γ(X, V)) :
    X.germToFunctionField U (X.presheaf.map i.op a) = X.germToFunctionField V a :=
  X.presheaf.germ_res_apply i (genericPoint X) (generic_mem_open X U) a

variable (M : SheafOfModules.{u} X.ringCatSheaf)
theorem restrict_injective (hM : IsLocallyRankOne X M) {U V : X.Opens} [Nonempty U]
    (i : U ⟶ V) : Function.Injective (M.val.map i.op) := by
  intro s t hst
  let := show Nonempty V from ⟨⟨(Classical.choice ‹Nonempty U›).val,
    i.le (Classical.choice ‹Nonempty U›).property⟩⟩
  have hc : Presheaf.equalizerSieve (F := M.val.presheaf) s t ∈
      (Opens.grothendieckTopology X) V := by
    intro x hxV
    obtain ⟨W, hxW, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X M).mp hM x
    let A := W ⊓ V
    let B := W ⊓ U
    let : Nonempty W := ⟨⟨x, hxW⟩⟩
    let : Nonempty A := ⟨⟨x, hxW, hxV⟩⟩
    let : Nonempty B := nonempty_inf X W U
    let p : A ⟶ V := homOfLE inf_le_right
    let q : B ⟶ U := homOfLE inf_le_right
    let j : B ⟶ A := homOfLE (inf_le_inf le_rfl i.le)
    let A' : Over W := Over.mk (homOfLE (show A ≤ W from inf_le_left))
    let B' : Over W := Over.mk (homOfLE (show B ≤ W from inf_le_left))
    let j' : B' ⟶ A' := Over.homMk j
    refine ⟨A, p, ?_, hxW, hxV⟩
    apply (chartSectionEquiv X M W e A inf_le_left).injective
    apply X.germToFunctionField_injective A
    have hes := PresheafOfModules.naturality_apply e.hom.val j'.op (M.val.map p.op s)
    have het := PresheafOfModules.naturality_apply e.hom.val j'.op (M.val.map p.op t)
    have hpath (z : M.val.obj (op V)) : M.val.map j.op (M.val.map p.op z) =
        M.val.map q.op (M.val.map i.op z) := by
      rw [← M.val.map_comp_apply, ← M.val.map_comp_apply]
      congr 1
    have heq : X.presheaf.map j.op (e.hom.val.app (op A') (M.val.map p.op s)) =
        X.presheaf.map j.op (e.hom.val.app (op A') (M.val.map p.op t)) := by
      change e.hom.val.app (op B') (M.val.map j.op (M.val.map p.op s)) =
        X.presheaf.map j.op (e.hom.val.app (op A') (M.val.map p.op s)) at hes
      change e.hom.val.app (op B') (M.val.map j.op (M.val.map p.op t)) =
        X.presheaf.map j.op (e.hom.val.app (op A') (M.val.map p.op t)) at het
      rw [← hes, ← het, hpath, hpath, hst]
    have hfield := congrArg (fun a : Γ(X, B) => X.germToFunctionField B a) heq
    rw [germ_restrict, germ_restrict] at hfield
    exact hfield
  apply M.isSheaf.isSeparated V _ hc
  intro W j hj
  exact hj

variable (U₀ : X.Opens) [Nonempty U₀]
variable (e : M.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))

/-- Evaluate a section as a rational function by restricting it to the intersection with
the chosen trivializing open and applying the given trivialization. -/
def coordinate (V : X.Opens) [Nonempty V] (s : M.val.obj (op V)) : X.functionField :=
  let := nonempty_inf X V U₀
  X.germToFunctionField (V ⊓ U₀)
    (e.hom.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U₀ ⟶ U₀)))
      (M.val.map (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op s))

theorem coordinate_add (V : X.Opens) [Nonempty V] (s t : M.val.obj (op V)) :
    coordinate X M U₀ e V (s + t) = coordinate X M U₀ e V s + coordinate X M U₀ e V t := by
  let := nonempty_inf X V U₀
  exact ((X.germToFunctionField (V ⊓ U₀)).hom.toAddMonoidHom.comp
    ((e.hom.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U₀ ⟶ U₀)))).hom.toAddMonoidHom.comp
      (M.val.map (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op).hom.toAddMonoidHom)).map_add s t

theorem coordinate_smul (V : X.Opens) [Nonempty V] (a : Γ(X, V)) (s : M.val.obj (op V)) :
    coordinate X M U₀ e V (a • s) = X.germToFunctionField V a * coordinate X M U₀ e V s := by
  let := nonempty_inf X V U₀
  dsimp only [coordinate]
  rw [M.val.map_smul, (e.hom.val.app _).hom.map_smul]
  change X.germToFunctionField (V ⊓ U₀) ((X.presheaf.map (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op
      a) * _) = _
  rw [map_mul, germ_restrict]

theorem coordinate_naturality {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) (s : M.val.obj (op V)) :
    coordinate X M U₀ e U (M.val.map i.op s) = coordinate X M U₀ e V s := by
  let := nonempty_inf X U U₀
  let := nonempty_inf X V U₀
  let j : U ⊓ U₀ ⟶ V ⊓ U₀ := homOfLE (inf_le_inf i.le le_rfl)
  let j' : Over.mk (homOfLE inf_le_right : U ⊓ U₀ ⟶ U₀) ⟶
      Over.mk (homOfLE inf_le_right : V ⊓ U₀ ⟶ U₀) := Over.homMk j
  have he := PresheafOfModules.naturality_apply e.hom.val j'.op
    (M.val.map (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op s)
  change e.hom.val.app (op (Over.mk (homOfLE inf_le_right : U ⊓ U₀ ⟶ U₀)))
      (M.val.map j.op (M.val.map (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op s)) =
    X.presheaf.map j.op
      (e.hom.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U₀ ⟶ U₀)))
        (M.val.map (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op s)) at he
  have hc : M.val.map j.op (M.val.map (homOfLE inf_le_left : V ⊓ U₀ ⟶ V).op s) =
      M.val.map (homOfLE inf_le_left : U ⊓ U₀ ⟶ U).op (M.val.map i.op s) := by
    rw [← M.val.map_comp_apply, ← M.val.map_comp_apply]
    congr 1
  dsimp only [coordinate]
  rw [← hc, he, germ_restrict]

/-- The section-coordinate map to the function field as a linear map over sections of
the nonempty open. -/
def coordinateLinear (V : X.Opens) [Nonempty V] : M.val.obj (op V) →ₗ[Γ(X, V)] X.functionField where
  toFun := coordinate X M U₀ e V
  map_add' := coordinate_add X M U₀ e V
  map_smul' a s := coordinate_smul X M U₀ e V a s
theorem coordinate_injective (hM : IsLocallyRankOne X M)
    (V : X.Opens) [Nonempty V] : Function.Injective (coordinate X M U₀ e V) := by
  let := nonempty_inf X V U₀
  intro s t h
  apply restrict_injective X M hM (homOfLE inf_le_left : V ⊓ U₀ ⟶ V)
  apply (chartSectionEquiv X M U₀ e (V ⊓ U₀) inf_le_right).injective
  exact X.germToFunctionField_injective (V ⊓ U₀) h

theorem coordinate_chart (W : X.Opens) [Nonempty W]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (V : X.Opens) [Nonempty V] (h : V ≤ W) (s : M.val.obj (op V)) :
    coordinate X M U₀ e V s =
      X.germToFunctionField V (chartSectionEquiv X M W d V h s) *
        coordinate X M U₀ e W (chartGenerator X M W d) := by
  let a := chartSectionEquiv X M W d V h s
  have hs : s = a • M.val.map (homOfLE h).op (chartGenerator X M W d) := by
    rw [chartGenerator_restrict]
    apply (chartSectionEquiv X M W d V h).injective
    rw [(chartSectionEquiv X M W d V h).map_smul, LinearEquiv.apply_symm_apply]
    exact (mul_one a).symm
  conv_lhs => rw [hs]
  rw [coordinate_smul, coordinate_naturality]

theorem coordinate_generator_ne_zero (hM : IsLocallyRankOne X M)
    (W : X.Opens) [Nonempty W]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    coordinate X M U₀ e W (chartGenerator X M W d) ≠ 0 := by
  intro h
  have hz : chartGenerator X M W d = 0 := (coordinate_injective X M U₀ e hM W)
    (h.trans (coordinateLinear X M U₀ e W).map_zero.symm)
  have ho := congrArg (chartSectionEquiv X M W d W le_rfl) hz
  simp [chartGenerator] at ho

open AlgebraicGeometry.Scheme.Modules.RationalFunctions
variable [AlgebraicGeometry.IsNoetherian X]
variable [hDVR : ∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
theorem eq_bot_of_not_nonempty (V : X.Opens) (h : ¬ Nonempty V) : V = ⊥ := by
  ext x
  constructor
  · intro hx
    exact (h ⟨⟨x, hx⟩⟩).elim
  · simp

omit [AlgebraicGeometry.IsNoetherian X]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
theorem rational_empty_subsingleton : Subsingleton ((rationalFunctions X).val.obj (op ⊥)) := by
  change Subsingleton Γ(Spec X.functionField, ((X.fromSpecStalk (genericPoint X))) ⁻¹ᵁ ⊥)
  rw [Scheme.Hom.preimage_bot]
  infer_instance

/-- Embed sections into rational-function sections using their chosen rational coordinates;
on an empty open use the zero map. -/
def embeddingSection (V : X.Opens) : M.val.obj (op V) →ₗ[Γ(X, V)] (rationalFunctions X).val.obj
    (op V) := by
  classical
  exact if h : Nonempty V then
    letI := h
    (rationalValueEquiv X V).symm.toLinearMap.comp (coordinateLinear X M U₀ e V)
  else 0

omit hDVR in
-- Retain the original DVR condition at every closed-point stalk in the rational embedding API.
@[nolint unusedArguments]
theorem embeddingSection_value
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (V : X.Opens) [hV : Nonempty V] (s : M.val.obj (op V)) :
    rationalValue X V (embeddingSection X M U₀ e V s) = coordinate X M U₀ e V s := by
  simp only [embeddingSection, dite_eq_left hV, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (rationalValueEquiv X V).apply_symm_apply _

/-- The module-sheaf morphism to rational functions assembled from the compatible
section-coordinate maps. -/
def embedding : M ⟶ rationalFunctions X where
  val := PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (fun V => ConcreteCategory.ofHom (C := ModuleCat Γ(X, V.unop))
      (embeddingSection X M U₀ e V.unop)) (by
      intro U V i
      ext s
      change embeddingSection X M U₀ e V.unop (M.val.map i s) =
        (rationalFunctions X).val.map i (embeddingSection X M U₀ e U.unop s)
      by_cases hV : Nonempty V.unop
      · let := hV
        let : Nonempty U.unop := ⟨⟨hV.some.val, i.unop.le hV.some.property⟩⟩
        apply (rationalValueEquiv X V.unop).injective
        change rationalValue X V.unop _ = rationalValue X V.unop _
        have hr := rationalValue_restrict X i.unop (embeddingSection X M U₀ e U.unop s)
        rw [Quiver.Hom.op_unop] at hr
        rw [embeddingSection_value, hr, embeddingSection_value]
        exact coordinate_naturality X M U₀ e i.unop s
      · have h0 := eq_bot_of_not_nonempty X V.unop hV
        have : Subsingleton ((rationalFunctions X).val.obj V) := by
          rw [← Opposite.op_unop V, h0]
          exact rational_empty_subsingleton X
        exact this.elim _ _)

theorem embedding_injective (hM : IsLocallyRankOne X M) (V : X.Opens) :
    Function.Injective ((embedding X M U₀ e).val.app (op V)) := by
  intro s t h
  by_cases hV : Nonempty V
  · let := hV
    apply coordinate_injective X M U₀ e hM V
    have hv := congrArg (rationalValue X V) h
    change rationalValue X V (embeddingSection X M U₀ e V s) =
      rationalValue X V (embeddingSection X M U₀ e V t) at hv
    simpa only [embeddingSection_value] using hv
  · apply M.isSheaf.isSeparated V ⊥
    · intro x hx
      exact (hV ⟨⟨x, hx⟩⟩).elim
    · intro W i hi
      exact False.elim hi

end AlgebraicGeometry.Scheme.Modules.Invertible.RationalTrivialization

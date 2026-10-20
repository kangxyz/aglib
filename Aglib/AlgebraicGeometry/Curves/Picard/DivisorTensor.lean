/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorClass
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
  (PicardGroup classOf sheafificationMapIsoOfLocallyBijective tensorPowerLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules
  (sheafifyForgetIso tensorPresheafOverIso tensorSheaf tensorSheafIso)

/-!
# Actual divisor-sheaf tensor multiplication

C2, K2-018 `lem:k2018-geometric-exact-order`, frozen source basis `7f86e4a`.
Multiplication in the actual generic direct-image sheaf defines a bilinear
map of fractional-ideal sheaves. Uniformizer trivializations show that this
map is locally scalar multiplication, hence locally bijective on the tensor
presheaf and an isomorphism after sheafification. This proves
O(D) tensor O(E) = O(D+E), including the empty-open cases, and the tensor-power
formula. The actual O(D) map therefore descends additively from the actual
divisor quotient into the actual Picard group. Surjectivity and injectivity
of this map are not asserted here; the generic-vector inverse remains separate.
No extra standard-theorem premise is used.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

/-- The commutative ring structure on rational-function sections, inherited from the
generic-point spectrum. -/
local instance rationalSectionCommRing (U : X.Opensᵒᵖ) :
    CommRing ((rationalFunctions X).val.obj U) :=
  inferInstanceAs (CommRing Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ
    U.unop))

/-- The product of sections of the divisor sheaves for `D` and `E`, regarded as a section for `D
+ E`. -/
def divisorMultiplySections (D E : Divisor X) (U : X.Opens)
    (s : (divisorSheaf X D).val.obj (op U)) (t : (divisorSheaf X E).val.obj (op U)) :
    (divisorSheaf X (D + E)).val.obj (op U) :=
  ⟨(show Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) from s.val) *
    (show Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) from t.val), by
    classical
    by_cases hU : Nonempty U
    · let := hU
      change _ ∈ (fractionalPresheaf X (D + E)).obj (op U)
      simp only [fractionalPresheaf, dite_eq_left hU, Submodule.mem_comap]
      change IsFractionalSection X (D + E) U ((rationalSectionIso X U).hom (s.val * t.val))
      rw [map_mul]
      exact isFractionalSection_mul X
        (explicitSheafSectionsEquiv X D U s).property (explicitSheafSectionsEquiv X E U t).property
    · change _ ∈ (fractionalPresheaf X (D + E)).obj (op U)
      simp only [fractionalPresheaf, dite_eq_right hU, Submodule.mem_top]⟩

theorem divisorMultiplySections_value (D E : Divisor X) (U : X.Opens) [Nonempty U]
    (s : (divisorSheaf X D).val.obj (op U)) (t : (divisorSheaf X E).val.obj (op U)) :
    rationalValue X U (divisorMultiplySections X D E U s t).val =
      rationalValue X U s.val * rationalValue X U t.val :=
  (rationalSectionIso X U).hom.hom.map_mul _ _

/-- The tensor-presheaf morphism induced by multiplication of divisor-sheaf sections. -/
def divisorMultiplicationPresheaf (D E : Divisor X) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      (divisorSheaf X D).val (divisorSheaf X E).val ⟶ (divisorSheaf X (D + E)).val :=
  PresheafOfModulesOfCommRing.homMk (fun U =>
    ModuleCat.MonoidalCategory.tensorLift (divisorMultiplySections X D E U.unop)
      (by intro s s' t; apply Subtype.ext; exact add_mul _ _ _)
      (by
        intro a s t
        apply Subtype.ext
        let a' : (rationalFunctions X).val.obj U := (X.fromSpecStalk (genericPoint X)).app
          U.unop a
        change (a' * s.val) * t.val = a' * (s.val * t.val)
        exact mul_assoc _ _ _)
      (by intro s t t'; apply Subtype.ext; exact mul_add _ _ _)
      (by
        intro a s t
        apply Subtype.ext
        let a' : (rationalFunctions X).val.obj U := (X.fromSpecStalk (genericPoint X)).app
          U.unop a
        change s.val * (a' * t.val) = a' * (s.val * t.val)
        exact mul_left_comm _ _ _))
    (by
      intro U V i
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro s t
      apply Subtype.ext
      exact ((Spec X.functionField).presheaf.map
        ((Opens.map (X.fromSpecStalk (genericPoint X)).base).map i.unop).op).hom.map_mul s.val
          t.val |>.symm)

/-- The morphism from the tensor product of divisor sheaves to the divisor sheaf of `D + E`,
obtained by sheafification. -/
def divisorMultiplicationSheaf (D E : Divisor X) :
    tensorSheaf X (divisorSheaf X D) (divisorSheaf X E) ⟶ divisorSheaf X (D + E) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    (divisorMultiplicationPresheaf X D E)

omit [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
theorem product_local_order (D E : Divisor X) (U : X.Opens) (g h : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0)
    (hh : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (h : X.functionField) x.val + E x = 0) :
    ∀ x : ClosedPoint X, x.val ∈ U → X.ord ((g * h : X.functionFieldˣ) : X.functionField) x.val +
      (D + E) x = 0 := by
  intro x hx
  rw [Units.val_mul, Scheme.ord_mul g.ne_zero h.ne_zero, Finsupp.add_apply]
  linarith [hg x hx, hh x hx]

/-- The local tensor-product isomorphism supplied by rational trivializing units for `D` and
`E`, in dimension at most one. -/
def divisorTensorLocalIso (hdim : topologicalKrullDim X ≤ 1)
    (D E : Divisor X) (U : X.Opens) (g h : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0)
    (hh : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (h : X.functionField) x.val + E x = 0) :
    (_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
        (divisorSheaf X D).val (divisorSheaf X E).val) ≅
      ((divisorSheaf X (D + E)).over U).val :=
  tensorPresheafOverIso X (divisorSheaf X D) (divisorSheaf X E) U ≪≫
    CategoryTheory.MonoidalCategory.tensorIso
      (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
      ((SheafOfModules.forget _).mapIso (divisorSheafLocalIso X hdim D U g hg).symm)
      ((SheafOfModules.forget _).mapIso (divisorSheafLocalIso X hdim E U h hh).symm) ≪≫
    CategoryTheory.MonoidalCategory.leftUnitor
      (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val ≪≫
    (SheafOfModules.forget _).mapIso
      (divisorSheafLocalIso X hdim (D + E) U (g * h) (product_local_order X D E U g h hg hh))

theorem divisorTensorLocalIso_hom (hdim : topologicalKrullDim X ≤ 1)
    (D E : Divisor X) (U : X.Opens) (g h : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0)
    (hh : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (h : X.functionField) x.val + E x = 0) :
    (divisorTensorLocalIso X hdim D E U g h hg hh).hom =
      (_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).map
        (divisorMultiplicationPresheaf X D E) := by
  ext V : 1
  let : CommRing ((X.ringCatSheaf.over U).obj.obj V) := inferInstanceAs (CommRing Γ(X, V.unop.left))
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  classical
  by_cases hV : Nonempty V.unop.left
  · let := hV
    apply Subtype.ext
    apply (rationalValueEquiv X V.unop.left).injective
    let hg' := fun x hx => hg x (V.unop.hom.le hx)
    let hh' := fun x hx => hh x (V.unop.hom.le hx)
    let a := (sectionTrivialization X hdim D V.unop.left g hg').symm s
    let b := (sectionTrivialization X hdim E V.unop.left h hh').symm t
    have ha : rationalValue X V.unop.left s.val =
        (g : X.functionField) * X.germToFunctionField V.unop.left a := by
      have ha := sectionTrivialization_value X hdim D V.unop.left g hg' a
      simpa only [a, LinearEquiv.apply_symm_apply] using ha
    have hb : rationalValue X V.unop.left t.val =
        (h : X.functionField) * X.germToFunctionField V.unop.left b := by
      have hb := sectionTrivialization_value X hdim E V.unop.left h hh' b
      simpa only [b, LinearEquiv.apply_symm_apply] using hb
    change rationalValue X V.unop.left
      (sectionTrivialization X hdim (D + E) V.unop.left (g * h)
        (product_local_order X D E V.unop.left g h hg' hh') (a * b)).val =
      rationalValue X V.unop.left (divisorMultiplySections X D E V.unop.left s t).val
    rw [sectionTrivialization_value, divisorMultiplySections_value, ha, hb, map_mul]
    change ((g : X.functionField) * (h : X.functionField)) *
      (X.germToFunctionField V.unop.left a * X.germToFunctionField V.unop.left b) = _
    ring
  · have h0 : V.unop.left = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hV ⟨⟨x, hx⟩⟩).elim
      · simp
    have : Subsingleton ((divisorSheaf X (D + E)).val.obj (op V.unop.left)) := by
      rw [h0]
      exact divisorSheaf_empty_subsingleton X (D + E)
    exact this.elim _ _

theorem divisorMultiplication_locallyBijective (hdim : topologicalKrullDim X ≤ 1) (D E : Divisor
  X) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (divisorMultiplicationPresheaf X D E) ∧
      PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
        (divisorMultiplicationPresheaf X D E) := by
  apply locallyBijective_of_local_isIso X
  intro x
  obtain ⟨U, hxU, g, hg⟩ := exists_local_principal_function X D x
  obtain ⟨V, hxV, h, hh⟩ := exists_local_principal_function X E x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
  rw [← divisorTensorLocalIso_hom X hdim D E (U ⊓ V) g h
    (fun y hy => hg y hy.1) (fun y hy => hh y hy.2)]
  infer_instance

/-- Multiplication of rational sections is the actual O(D) tensor isomorphism. -/
def divisorTensorIso (hdim : topologicalKrullDim X ≤ 1) (D E : Divisor X) :
    tensorSheaf X (divisorSheaf X D) (divisorSheaf X E) ≅ divisorSheaf X (D + E) :=
  sheafificationMapIsoOfLocallyBijective X (divisorMultiplicationPresheaf X D E)
    (divisorMultiplication_locallyBijective X hdim D E) ≪≫ sheafifyForgetIso X (divisorSheaf X (D
      + E))

theorem divisorTensorIso_hom (hdim : topologicalKrullDim X ≤ 1) (D E : Divisor X) :
    (divisorTensorIso X hdim D E).hom = divisorMultiplicationSheaf X D E := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
    (divisorSheaf X D).val (divisorSheaf X E).val
  let O := divisorSheaf X (D + E)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have he : adj.homEquiv P O = PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) := by
    apply Equiv.ext
    intro f
    exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
  calc
    (divisorTensorIso X hdim D E).hom =
        (adj.homEquiv P O).symm (divisorMultiplicationPresheaf X D E) :=
      (adj.homEquiv_counit P O (divisorMultiplicationPresheaf X D E)).symm
    _ = divisorMultiplicationSheaf X D E := by rw [he]; rfl

/-- The actual O(D) construction is additive into the actual Picard group. -/
def divisorToPicard (hdim : topologicalKrullDim X ≤ 1) : Divisor X →+ PicardGroup X where
  toFun D := classOf X (divisorLineBundle X hdim D)
  map_zero' := by
    apply Quotient.sound
    exact ⟨(globalTrivialization X hdim 0 1 (by
      intro x
      have h : X.ord (1 : X.functionField) x.val = 0 := (localOrder X x).map_zero
      simpa using h)).symm ≪≫
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩
  map_add' D E := by
    apply Quotient.sound
    exact ⟨(divisorTensorIso X hdim D E).symm⟩

theorem divisorToPicard_principal (hdim : topologicalKrullDim X ≤ 1) (f : Additive
  X.functionFieldˣ) :
    divisorToPicard X hdim (principal X f) = 0 :=
  principal_class_eq_trivial X hdim f.toMul

/-- Descent to the actual divisor-class quotient, with the proven tensor law. -/
def divisorClassToPicard (hdim : topologicalKrullDim X ≤ 1) :
    (Divisor X ⧸ (principal X).range) →+ PicardGroup X :=
  QuotientAddGroup.lift _ (divisorToPicard X hdim) (by
    rintro _ ⟨f, rfl⟩
    exact divisorToPicard_principal X hdim f)

@[simp] theorem divisorClassToPicard_mk (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    divisorClassToPicard X hdim (QuotientAddGroup.mk D) = classOf X (divisorLineBundle X hdim D)
      := rfl

theorem divisorClassToPicard_eq_old_map (hdim : topologicalKrullDim X ≤ 1)
    (a : Divisor X ⧸ (principal X).range) :
    divisorClassToPicard X hdim a = divisorClassToLineBundleClass X hdim a := by
  induction a using Quotient.inductionOn with | h D => rfl

/-- Actual tensor powers of O(D) identify with O(nD), including n=0. -/
def divisorPowerIso (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    (n : ℕ) → (tensorPowerLineBundle X (divisorLineBundle X hdim D) n).val ≅ divisorSheaf X (n • D)
  | 0 => by
    rw [zero_smul]
    exact CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf) ≪≫
    globalTrivialization X hdim 0 1 (by
      intro x
      have h : X.ord (1 : X.functionField) x.val = 0 := (localOrder X x).map_zero
      simpa using h)
  | n + 1 =>
    tensorSheafIso X (Iso.refl _) (divisorPowerIso hdim D n) ≪≫
      divisorTensorIso X hdim D (n • D) ≪≫
      eqToIso (congrArg (divisorSheaf X) (by rw [succ_nsmul, add_comm]))
end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

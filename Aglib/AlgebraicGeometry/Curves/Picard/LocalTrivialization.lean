/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Divisors.RegularSections
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorSheaf
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne LineBundle lineBundleSetoid trivialLineBundle)


/-!
# Actual local trivializations of divisor sheaves

C2, K2-018 `lem:k2018-geometric-exact-order`, source basis `7f86e4a`.
On an integral Noetherian scheme of dimension at most one with actual closed
DVR stalks, the constructed fractional-ideal sheaf O(D) is locally free of
rank one. Uniformizer powers and removal of finite closed support construct
the trivializing opens; naturality is checked on the actual sheaf maps.
Principal trivialization O(div(f)) → O is multiplication by f, fixing the
positive-order sign convention. No Picard-group equivalence is assumed.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable (X : Scheme.{u}) [IsIntegral X] [hNoeth : IsNoetherian X]
variable [hDVR : ∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

/-- Send a regular section on a nonempty open to its rational value in the zero-divisor
fractional module. -/
def regularToFractionalZero (U : X.Opens) [Nonempty U] :
    Γ(X, U) →ₗ[Γ(X, U)] fractionalSections X 0 U where
  toFun a := ⟨X.germToFunctionField U a, Or.inr (by
    intro x hx
    simp only [Finsupp.zero_apply, add_zero]
    have : IsDiscreteValuationRing (X.presheaf.stalk x.val) := inferInstance
    apply (order_nonneg_iff_mem_stalk X x.val _).mpr
    exact ⟨X.presheaf.germ U x.val hx a,
      Scheme.algebraMap_germ_eq_germToFunctionField X hx a⟩)⟩
  map_add' a b := by apply Subtype.ext; exact (X.germToFunctionField U).hom.map_add a b
  map_smul' a b := by
    apply Subtype.ext
    change X.germToFunctionField U (a * b) =
      X.germToFunctionField U a * X.germToFunctionField U b
    exact (X.germToFunctionField U).hom.map_mul a b

/-- Identify regular sections with fractional sections of the zero divisor when the curve has
dimension at most one. -/
def fractionalZeroEquiv (hdim : topologicalKrullDim X ≤ 1) (U : X.Opens) [Nonempty U] :
    Γ(X, U) ≃ₗ[Γ(X, U)] fractionalSections X 0 U :=
  LinearEquiv.ofBijective (regularToFractionalZero X U) ⟨by
    intro a b hab
    exact X.germToFunctionField_injective U (congrArg Subtype.val hab), by
    intro f
    have hf : ∀ x : ClosedPoint X, x.val ∈ U → 0 ≤ X.ord f.val x.val := by
      intro x hx
      rcases f.property with h0 | hf
      · simp [h0]
      · simpa using hf x hx
    obtain ⟨a, ha⟩ := exists_section_of_nonneg_orders X hdim U f.val hf
    exact ⟨a, Subtype.ext ha⟩⟩

omit hDVR in
-- Retain the DVR-stalk condition in the fractional-divisor trivialization interface; inversion
-- here follows from the local order homomorphism.
@[nolint unusedArguments]
theorem order_inv [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (x : ClosedPoint X) (g : X.functionFieldˣ) :
    X.ord ((g⁻¹ : X.functionFieldˣ) : X.functionField) x.val =
      -X.ord (g : X.functionField) x.val :=
  (localOrder X x).map_neg (Additive.ofMul g)

/-- Multiply fractional sections by g when its local orders carry the bound for D to the bound
for E. -/
def multiplyFractionalEquiv (D E : Divisor X) (U : X.Opens) [Nonempty U]
    (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + E x = D x) :
    fractionalSections X D U ≃ₗ[Γ(X, U)] fractionalSections X E U where
  toFun f := ⟨(g : X.functionField) * f.val, by
    rcases f.property with hf0 | hf
    · left; simp [hf0]
    by_cases hf0 : f.val = 0
    · left; simp [hf0]
    right
    intro x hx
    rw [Scheme.ord_mul g.ne_zero hf0]
    linarith [hf x hx, hg x hx]⟩
  invFun f := ⟨((g⁻¹ : X.functionFieldˣ) : X.functionField) * f.val, by
    rcases f.property with hf0 | hf
    · left; simp [hf0]
    by_cases hf0 : f.val = 0
    · left; simp [hf0]
    right
    intro x hx
    rw [Scheme.ord_mul (Units.ne_zero _) hf0, order_inv X x g]
    linarith [hf x hx, hg x hx]⟩
  left_inv f := by apply Subtype.ext; simp
  right_inv f := by apply Subtype.ext; simp
  map_add' f h := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' a f := by
    apply Subtype.ext
    change (g : X.functionField) * (algebraMap Γ(X, U) X.functionField a * f.val) =
      algebraMap Γ(X, U) X.functionField a * ((g : X.functionField) * f.val)
    exact mul_left_comm _ _ _

/-- Trivialize the fractional sections of D on an open where the orders of g cancel D. -/
def locallyPrincipalSectionsEquiv (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (U : X.Opens) [Nonempty U] (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0) :
    Γ(X, U) ≃ₗ[Γ(X, U)] fractionalSections X D U :=
  (fractionalZeroEquiv X hdim U).trans
    (multiplyFractionalEquiv X 0 D U g (by simpa using hg))


/-- Identify sections of the constructed divisor sheaf with their literal fractional rational
values. -/
def explicitSheafSectionsEquiv (D : Divisor X) (U : X.Opens) [hU : Nonempty U] :
    (divisorSheaf X D).val.obj (op U) ≃ₗ[Γ(X, U)] fractionalSections X D U where
  toFun s := ⟨rationalValue X U s.val, by
    have h := s.property
    change s.val ∈ (fractionalPresheaf X D).obj (op U) at h
    simp only [fractionalPresheaf] at h
    rw [dite_eq_left hU] at h
    exact h⟩
  invFun f := ⟨(rationalValueEquiv X U).symm f.val, by
    change (rationalValueEquiv X U).symm f.val ∈ (fractionalPresheaf X D).obj (op U)
    simp only [fractionalPresheaf]
    rw [dite_eq_left hU]
    change (rationalValueEquiv X U) ((rationalValueEquiv X U).symm f.val) ∈ fractionalSections X D U
    rw [LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv s := by apply Subtype.ext; exact (rationalValueEquiv X U).symm_apply_apply s.val
  right_inv f := by apply Subtype.ext; exact (rationalValueEquiv X U).apply_symm_apply f.val
  map_add' s t := by apply Subtype.ext; exact (rationalValue X U).map_add _ _
  map_smul' a s := by apply Subtype.ext; exact (rationalValue X U).map_smul _ _

/-- The section trivialization on a nonempty open, given by multiplying regular rational
values by g. -/
def nonemptyTrivialization (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (U : X.Opens) [Nonempty U] (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0) :
    Γ(X, U) ≃ₗ[Γ(X, U)] (divisorSheaf X D).val.obj (op U) :=
  (locallyPrincipalSectionsEquiv X hdim D U g hg).trans
    (explicitSheafSectionsEquiv X D U).symm

theorem nonemptyTrivialization_value (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (U : X.Opens) [Nonempty U] (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0)
    (a : Γ(X, U)) :
    rationalValue X U (nonemptyTrivialization X hdim D U g hg a).val =
      (g : X.functionField) * X.germToFunctionField U a := by
  have h := (explicitSheafSectionsEquiv X D U).apply_symm_apply
    (locallyPrincipalSectionsEquiv X hdim D U g hg a)
  exact congrArg Subtype.val h

/-- The regular-section trivialization determined by g, including the unique map on an empty
open. -/
def sectionTrivialization (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (U : X.Opens) (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0) :
    Γ(X, U) ≃ₗ[Γ(X, U)] (divisorSheaf X D).val.obj (op U) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    exact nonemptyTrivialization X hdim D U g hg
  · have hU0 : U = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hU ⟨⟨x, hx⟩⟩).elim
      · simp
    subst U
    let := divisorSheaf_empty_subsingleton X D
    exact LinearEquiv.ofSubsingleton _ _

theorem sectionTrivialization_value (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (U : X.Opens) [hU : Nonempty U] (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0)
    (a : Γ(X, U)) :
    rationalValue X U (sectionTrivialization X hdim D U g hg a).val =
      (g : X.functionField) * X.germToFunctionField U a := by
  simpa only [sectionTrivialization, dite_eq_left hU] using
    nonemptyTrivialization_value X hdim D U g hg a

theorem sectionTrivialization_naturality (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) {U V : X.Opens} (i : U ⟶ V) (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ V → X.ord (g : X.functionField) x.val + D x = 0)
    (a : Γ(X, V)) :
    (divisorSheaf X D).val.map i.op (sectionTrivialization X hdim D V g hg a) =
    sectionTrivialization X hdim D U g (fun x hx => hg x (i.le hx)) (X.presheaf.map i.op a) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    let : Nonempty V := ⟨⟨hU.some.val, i.le hU.some.property⟩⟩
    apply Subtype.ext
    apply (rationalValueEquiv X U).injective
    change rationalValue X U ((rationalFunctions X).val.map i.op
      (sectionTrivialization X hdim D V g hg a).val) =
      rationalValue X U (sectionTrivialization X hdim D U g
        (fun x hx => hg x (i.le hx)) (X.presheaf.map i.op a)).val
    rw [rationalValue_restrict, sectionTrivialization_value, sectionTrivialization_value]
    congr 1
    exact (X.presheaf.germ_res_apply i (genericPoint X) _ a).symm
  · have hU0 : U = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hU ⟨⟨x, hx⟩⟩).elim
      · simp
    subst U
    let := divisorSheaf_empty_subsingleton X D
    exact @Subsingleton.elim ((divisorSheaf X D).val.obj (op ⊥))
      (divisorSheaf_empty_subsingleton X D) _ _

/-- The sheaf isomorphism on U induced by the compatible section trivializations determined by
g. -/
def divisorSheafLocalIso (hdim : topologicalKrullDim X ≤ 1)
    (D : Divisor X) (U : X.Opens) (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + D x = 0) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅ (divisorSheaf X D).over U :=
  (SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over U)).preimageIso <|
    PresheafOfModules.isoMk
      (fun V => (sectionTrivialization X hdim D V.unop.left g
        (fun x hx => hg x (V.unop.hom.le hx))).toModuleIso)
      (by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (sectionTrivialization_naturality X hdim D f.unop.left g
          (fun x hx => hg x (V.unop.hom.le hx)) a).symm)


omit hNoeth hDVR in
-- Retain the noetherian DVR-curve conditions used by divisor-sheaf trivialization; this
-- neighborhood is obtained directly by removing the finite closed support.
@[nolint unusedArguments]
theorem exists_open_divisor_zero [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] (D : Divisor X) (x : X)
    (hx : ∀ y : ClosedPoint X, y.val = x → D y = 0) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y : ClosedPoint X, y.val ∈ U → D y = 0 := by
  classical
  let S : Set X := ⋃ y ∈ D.support, ({y.val} : Set X)
  have hS : IsClosed S := isClosed_biUnion_finset fun y _ => y.property
  let U : X.Opens := ⟨Sᶜ, hS.isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · intro hxS
    simp only [S, Set.mem_iUnion, Set.mem_singleton_iff] at hxS
    obtain ⟨y, hy, hxy⟩ := hxS
    exact (Finsupp.mem_support_iff.mp hy) (hx y hxy.symm)
  · intro y hyU
    by_contra hy
    exact hyU (Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr
      ⟨Finsupp.mem_support_iff.mpr hy, Set.mem_singleton _⟩⟩)



theorem exists_local_principal_function (D : Divisor X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ g : X.functionFieldˣ,
      ∀ y : ClosedPoint X, y.val ∈ U → X.ord (g : X.functionField) y.val + D y = 0 := by
  classical
  by_cases hx : IsClosed ({x} : Set X)
  · let y : ClosedPoint X := ⟨x, hx⟩
    have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      inferInstanceAs (IsDiscreteValuationRing (X.presheaf.stalk y.val))
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
    have ht0 : algebraMap (X.presheaf.stalk x) X.functionField t ≠ 0 := by
      simpa only [map_zero] using
        (IsFractionRing.injective (X.presheaf.stalk x) X.functionField).ne ht.ne_zero
    let g0 : X.functionFieldˣ := Units.mk0 _ ht0
    let g := g0 ^ (-D y)
    have hval : (principal X (Additive.ofMul g) + D) y = 0 := by
      change localOrder X y (Additive.ofMul (g0 ^ (-D y))) + D y = 0
      rw [ofMul_zpow, map_zsmul]
      have h1 : localOrder X y (Additive.ofMul g0) = 1 :=
        order_uniformizer X y (coheight_eq_one_of_dvr X x) t ht
      rw [h1]
      simp
    obtain ⟨U, hxU, hU⟩ := exists_open_divisor_zero X
      (principal X (Additive.ofMul g) + D) x (by
        intro z hz
        have hz' : z = y := Subtype.ext hz
        simpa [hz'] using hval)
    exact ⟨U, hxU, g, hU⟩
  · obtain ⟨U, hxU, hU⟩ := exists_open_divisor_zero X D x (by
      intro y hy
      exact False.elim (hx (hy ▸ y.property)))
    refine ⟨U, hxU, 1, ?_⟩
    intro y hy
    have ho : X.ord (1 : X.functionField) y.val = 0 := (localOrder X y).map_zero
    rw [Units.val_one, ho, zero_add]
    exact hU y hy


open AlgebraicGeometry.Scheme.OverField.Curve.Picard

theorem divisorSheaf_locallyRankOne (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    IsLocallyRankOne X (divisorSheaf X D) := by
  choose U hx g hg using exists_local_principal_function X D
  let e (x : X) : SheafOfModules.free (R := X.ringCatSheaf.over (U x)) PUnit.{u + 1} ≅
      (divisorSheaf X D).over (U x) :=
    (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit (X.ringCatSheaf.over (U x)))) ≪≫
      divisorSheafLocalIso X hdim D (U x) (g x) (hg x)
  let q : (divisorSheaf X D).LocalGeneratorsData.{u} := {
    I := X
    X := U
    coversTop := by
      intro V x hxV
      exact ⟨U x ⊓ V, homOfLE inf_le_right,
        ⟨x, ⟨homOfLE inf_le_left⟩⟩, hx x, hxV⟩
    generators x := (SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (U x)) PUnit.{u + 1}).ofEpi (e x).hom }
  refine ⟨q, ?_, fun _ => ⟨Equiv.refl _⟩⟩
  constructor
  intro x
  dsimp [q]
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  infer_instance

/-- The divisor sheaf equipped with the proved local rank-one structure on a curve of
dimension at most one. -/
def divisorLineBundle (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X) : LineBundle X :=
  ⟨divisorSheaf X D, divisorSheaf_locallyRankOne X hdim D⟩

/-- Trivialize the divisor sheaf by a rational unit whose orders cancel D at every closed
point. -/
def globalTrivialization (hdim : topologicalKrullDim X ≤ 1) (D : Divisor X)
    (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, X.ord (g : X.functionField) x.val + D x = 0) :
    SheafOfModules.unit X.ringCatSheaf ≅ divisorSheaf X D :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => (sectionTrivialization X hdim D U.unop g (fun x _ => hg x)).toModuleIso)
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (sectionTrivialization_naturality X hdim D f.unop g (fun x _ => hg x) a).symm)

/-- Multiplication by f trivializes O(div(f)), with the positive order convention. -/
def principalTrivialization (hdim : topologicalKrullDim X ≤ 1) (f : X.functionFieldˣ) :
    divisorSheaf X (principal X (Additive.ofMul f)) ≅ SheafOfModules.unit X.ringCatSheaf :=
  (globalTrivialization X hdim _ f⁻¹ (by
    intro x
    change X.ord ((f⁻¹ : X.functionFieldˣ) : X.functionField) x.val +
      X.ord (f : X.functionField) x.val = 0
    rw [order_inv]
    exact neg_add_cancel _)).symm

theorem principal_class_eq_trivial (hdim : topologicalKrullDim X ≤ 1)
    (f : X.functionFieldˣ) :
    Quotient.mk (lineBundleSetoid X) (divisorLineBundle X hdim (principal X (Additive.ofMul f))) =
      Quotient.mk (lineBundleSetoid X) (trivialLineBundle X) := by
  apply Quotient.sound
  exact ⟨principalTrivialization X hdim f ≪≫
    (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩


end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

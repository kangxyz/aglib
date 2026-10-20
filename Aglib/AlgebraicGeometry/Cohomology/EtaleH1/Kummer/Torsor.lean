/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.ExtensionTorsor
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorTrivial

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.Torsor` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0f46de2d4f131394db0af079b9a8ade517f7a4e794813f6dedd2fffbd9bfb21d`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleH1
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual positive Kummer root torsors and their Ext classes

Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.

C4 local/generic representative construction, K2-018
`lem:k2018-geometric-exact-order`, frozen basis `7f86e4a`.

For an actual global unit f, the torsor is A's actual extension-fibre sheaf
of our constructed Kummer short exact sequence over f. The only local-root
input is the explicitly retained generic03PL sheaf Epi family at positive
invertible n. Actual sections are proved to be units a with a^n=f after
restriction; the action is literal multiplication by the actual root of
unity. Positive transport from p to q is q/p, fixing the sign required by
the existing field Kummer value sigma(a)/a.

The inversion equivalence from these positive roots to normalized sections
f*s^n=1 is proved, and its coefficient action is explicitly inverted. These
are not silently identified with the same marked torsor. The canonical H1
class is the actual torsorExtClass. Powers have zero class without any
classification premise; its exact global power kernel additionally uses A's
precise Stacks03AJ canonical-map bijectivity. No pair/Picard H1 comparison,
generic divisor formula or Bockstein equality is assumed or claimed here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace GroupCohomology.Kummer.Torsor
open AlgebraicGeometry.Scheme.EtaleH1 GroupCohomology.Kummer.Coefficients
universe u

/-- The section of the multiplicative coefficient sheaf corresponding to the global unit `f`. -/
def unitSection (X : Scheme.{u}) (f : Γ(X, ⊤)ˣ) :
    (gm X).obj.obj (op (etaleTerminal X)) :=
  (unitsSections X _).symm (Additive.ofMul f)

/-- The restriction of the global unit `f` to the etale test scheme `U`. -/
def unitRestriction (X : Scheme.{u}) (f : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ) : Γ(U.unop.left, ⊤)ˣ :=
  Units.map U.unop.hom.appTop.hom.toMonoidHom f

theorem unitSection_restrict (X : Scheme.{u}) (f : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ) :
    (unitsSections X U (restrictSection (gm X) (unitSection X f) U)).toMul =
      unitRestriction X f U := by
  rw [restrictSection, unitsSections_naturality]
  rw [unitSection, AddEquiv.apply_symm_apply]
  rfl

/-- The genuine root torsor of a global unit, with the positive root convention. -/
def rootTorsor (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ) : Torsor (mu X n) :=
  extensionFiberTorsor (sequence X n) (unitSection X f) (sequence_shortExact h X n hn hinv)

/-- Sections of the root torsor as units whose `n`th power is the restriction of `f`,
using the supplied power-surjectivity input at positive invertible level. -/
def rootSectionsEquiv (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ) :
    (rootTorsor h X n hn hinv f).carrier.obj.obj U ≃
      {a : Γ(U.unop.left, ⊤)ˣ // a ^ n = unitRestriction X f U} where
  toFun t := ⟨(unitsSections X U t.val).toMul, by
    have ht := congrArg (fun z => (unitsSections X U z).toMul) t.property
    change (unitsSections X U ((power X n).hom.app U t.val)).toMul =
      (unitsSections X U (restrictSection (gm X) (unitSection X f) U)).toMul at ht
    rw [power_apply, unitSection_restrict] at ht
    exact ht⟩
  invFun a := ⟨(unitsSections X U).symm (Additive.ofMul a.val), by
    apply (unitsSections X U).injective
    apply Additive.toMul.injective
    change (unitsSections X U ((power X n).hom.app U ((unitsSections X U).symm _))).toMul =
      (unitsSections X U (restrictSection (gm X) (unitSection X f) U)).toMul
    rw [power_apply, AddEquiv.apply_symm_apply, unitSection_restrict]
    exact a.property⟩
  left_inv t := by
    apply Subtype.ext
    exact (unitsSections X U).symm_apply_apply t.val
  right_inv a := by
    apply Subtype.ext
    exact congrArg Additive.toMul ((unitsSections X U).apply_symm_apply _)

/-- The action is literal multiplication of a chosen root by a root of unity. -/
theorem rootSections_action (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ)
    (ζ : (mu X n).obj.obj U) (t : (rootTorsor h X n hn hinv f).carrier.obj.obj U) :
    (rootSectionsEquiv h X n hn hinv f U ((rootTorsor h X n hn hinv f).action U ζ t)).val =
      ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ) *
        (rootSectionsEquiv h X n hn hinv f U t).val := by
  change (unitsSections X U ((inclusion X n).hom.app U ζ + (show (gm X).obj.obj U from
      t.val))).toMul = _
  rw [map_add]
  change (unitsSections X U ((inclusion X n).hom.app U ζ)).toMul * _ = _
  rw [inclusion_apply]
  rfl

/-- Positive transport of roots gives q/p, matching the existing Kummer cocycle. -/
theorem root_transport_ratio (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ)
    (ζ : (mu X n).obj.obj U) (s t : (rootTorsor h X n hn hinv f).carrier.obj.obj U)
    (ht : (rootTorsor h X n hn hinv f).action U ζ s = t) :
    ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ) =
      (rootSectionsEquiv h X n hn hinv f U t).val /
        (rootSectionsEquiv h X n hn hinv f U s).val := by
  apply (eq_div_iff_mul_eq').mpr
  exact (rootSections_action h X n hn hinv f U ζ s).symm.trans
    (congrArg (fun q => (rootSectionsEquiv h X n hn hinv f U q).val) ht)

/-- Actual inversion from positive roots to normalized sections. -/
def inverseRootEquiv {A : Type*} [CommGroup A] (n : ℕ) (f : A) :
    {a : A // a ^ n = f} ≃ {s : A // f * s ^ n = 1} where
  toFun a := ⟨a.val⁻¹, by rw [inv_pow, a.property, mul_inv_cancel]⟩
  invFun s := ⟨s.val⁻¹, by
    rw [inv_pow]
    exact (eq_inv_iff_mul_eq_one.mpr s.property).symm⟩
  left_inv a := by apply Subtype.ext; exact inv_inv _
  right_inv s := by apply Subtype.ext; exact inv_inv _

/-- Inversion reverses the coefficient action; it cannot preserve the marking silently. -/
theorem inverseRootEquiv_action {A : Type*} [CommGroup A] (n : ℕ) (f ζ a : A)
    (ha : a ^ n = f) (hζ : ζ ^ n = 1) :
    (inverseRootEquiv n f ⟨ζ * a, by rw [mul_pow, hζ, ha, one_mul]⟩).val =
      ζ⁻¹ * (inverseRootEquiv n f ⟨a, ha⟩).val := by
  exact mul_inv _ _


/-- Restriction of a root is restriction of its actual invertible function. -/
theorem rootSections_naturality (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (f : Γ(X, ⊤)ˣ)
    {U V : X.Etaleᵒᵖ} (q : U ⟶ V)
    (t : (rootTorsor h X n hn hinv f).carrier.obj.obj U) :
    (rootSectionsEquiv h X n hn hinv f V
      ((rootTorsor h X n hn hinv f).carrier.obj.map q t)).val =
      Units.map q.unop.left.appTop.hom.toMonoidHom
        (rootSectionsEquiv h X n hn hinv f U t).val :=
  unitsSections_naturality X q t.val

@[simp] theorem unitRestriction_terminal (X : Scheme.{u}) (f : Γ(X, ⊤)ˣ) :
    unitRestriction X f (op (etaleTerminal X)) = f := by
  apply Units.ext
  change (show X ⟶ X from 𝟙 X).appTop f.val = f.val
  simp

section Cohomology
universe w
variable (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
variable (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The canonical Ext H1 class of the actual positive root torsor. -/
def rootClass (f : Γ(X, ⊤)ˣ) : H1Etale X (mu X n) :=
  torsorExtClass (rootTorsor h X n hn hinv f)

theorem rootClass_eq_zero_of_power (a : Γ(X, ⊤)ˣ) :
    rootClass h X n hn hinv (a ^ n) = 0 := by
  apply torsorExtClass_eq_zero_of_section
  exact (rootSectionsEquiv h X n hn hinv (a ^ n) (op (etaleTerminal X))).symm
    ⟨a, (unitRestriction_terminal X (a ^ n)).symm⟩

/-- The exact global-unit kernel uses only A's precise canonical torsor classification. -/
theorem rootClass_eq_zero_iff (hclass : Stacks03AJ.{u, w} X) (f : Γ(X, ⊤)ˣ) :
    rootClass h X n hn hinv f = 0 ↔ ∃ a : Γ(X, ⊤)ˣ, a ^ n = f := by
  rw [rootClass, torsorExtClass_eq_zero_iff_globalSection _ hclass]
  constructor
  · rintro ⟨t⟩
    let a := rootSectionsEquiv h X n hn hinv f (op (etaleTerminal X)) t
    exact ⟨a.val, a.property.trans (unitRestriction_terminal X f)⟩
  · rintro ⟨a, ha⟩
    exact ⟨(rootSectionsEquiv h X n hn hinv f (op (etaleTerminal X))).symm
      ⟨a, ha.trans (unitRestriction_terminal X f).symm⟩⟩
end Cohomology

end GroupCohomology.Kummer.Torsor

/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.LocalTrivialization
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Abel
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible (LineBundleClass lineBundleSetoid)


/-!
# From actual divisor classes to line-bundle classes

C2 public facade, K2-018 `lem:k2018-geometric-exact-order`, source basis
`7f86e4a`. All earlier fractional-sheaf and local-trivialization names remain
available through this import. Multiplication by a rational unit gives actual
sheaf isomorphisms for principal shifts, hence a well-defined map from the
actual divisor quotient to isomorphism classes of actual line bundles.
Surjectivity, the inverse, and the tensor-group Picard equivalence are not yet
claimed. In particular LineBundleClass has not been replaced by a divisor quotient.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
open AlgebraicGeometry.Scheme.OverField.Curve.Picard
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

def nonemptyShiftEquiv (D E : Divisor X) (U : X.Opens) [Nonempty U]
    (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + E x = D x) :
    (divisorSheaf X D).val.obj (op U) ≃ₗ[Γ(X, U)] (divisorSheaf X E).val.obj (op U) :=
  (explicitSheafSectionsEquiv X D U).trans
    ((multiplyFractionalEquiv X D E U g hg).trans (explicitSheafSectionsEquiv X E U).symm)

theorem nonemptyShiftEquiv_value (D E : Divisor X) (U : X.Opens) [Nonempty U]
    (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + E x = D x)
    (s : (divisorSheaf X D).val.obj (op U)) :
    rationalValue X U (nonemptyShiftEquiv X D E U g hg s).val =
      (g : X.functionField) * rationalValue X U s.val := by
  have h := (explicitSheafSectionsEquiv X E U).apply_symm_apply
    (multiplyFractionalEquiv X D E U g hg (explicitSheafSectionsEquiv X D U s))
  exact congrArg Subtype.val h

def sectionShiftEquiv (D E : Divisor X) (U : X.Opens)
    (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + E x = D x) :
    (divisorSheaf X D).val.obj (op U) ≃ₗ[Γ(X, U)] (divisorSheaf X E).val.obj (op U) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    exact nonemptyShiftEquiv X D E U g hg
  · have hU0 : U = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hU ⟨⟨x, hx⟩⟩).elim
      · simp
    subst U
    let := divisorSheaf_empty_subsingleton X D
    let := divisorSheaf_empty_subsingleton X E
    exact LinearEquiv.ofSubsingleton _ _

theorem sectionShiftEquiv_value (D E : Divisor X) (U : X.Opens) [hU : Nonempty U]
    (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ U → X.ord (g : X.functionField) x.val + E x = D x)
    (s : (divisorSheaf X D).val.obj (op U)) :
    rationalValue X U (sectionShiftEquiv X D E U g hg s).val =
      (g : X.functionField) * rationalValue X U s.val := by
  simpa only [sectionShiftEquiv, dite_eq_left hU] using
    nonemptyShiftEquiv_value X D E U g hg s

theorem sectionShiftEquiv_naturality (D E : Divisor X) {U V : X.Opens} (i : U ⟶ V)
    (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, x.val ∈ V → X.ord (g : X.functionField) x.val + E x = D x)
    (s : (divisorSheaf X D).val.obj (op V)) :
    (divisorSheaf X E).val.map i.op (sectionShiftEquiv X D E V g hg s) =
    sectionShiftEquiv X D E U g (fun x hx => hg x (i.le hx))
      ((divisorSheaf X D).val.map i.op s) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    let : Nonempty V := ⟨⟨hU.some.val, i.le hU.some.property⟩⟩
    apply Subtype.ext
    apply (rationalValueEquiv X U).injective
    change rationalValue X U ((rationalFunctions X).val.map i.op
      (sectionShiftEquiv X D E V g hg s).val) =
      rationalValue X U (sectionShiftEquiv X D E U g
        (fun x hx => hg x (i.le hx)) ((divisorSheaf X D).val.map i.op s)).val
    rw [rationalValue_restrict, sectionShiftEquiv_value, sectionShiftEquiv_value]
    congr 1
    exact (rationalValue_restrict X i s.val).symm
  · have hU0 : U = ⊥ := by
      ext x
      constructor
      · intro hx
        exact (hU ⟨⟨x, hx⟩⟩).elim
      · simp
    subst U
    exact @Subsingleton.elim ((divisorSheaf X E).val.obj (op ⊥))
      (divisorSheaf_empty_subsingleton X E) _ _

def divisorSheafShiftIso (D E : Divisor X) (g : X.functionFieldˣ)
    (hg : ∀ x : ClosedPoint X, X.ord (g : X.functionField) x.val + E x = D x) :
    divisorSheaf X D ≅ divisorSheaf X E :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => (sectionShiftEquiv X D E U.unop g (fun x _ => hg x)).toModuleIso)
      (by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (sectionShiftEquiv_naturality X D E f.unop g (fun x _ => hg x) a).symm)

def principalShiftIso (D : Divisor X) (f : X.functionFieldˣ) :
    divisorSheaf X D ≅ divisorSheaf X (D + principal X (Additive.ofMul f)) :=
  divisorSheafShiftIso X _ _ f⁻¹ (by
    intro x
    change X.ord ((f⁻¹ : X.functionFieldˣ) : X.functionField) x.val +
      (D x + X.ord (f : X.functionField) x.val) = D x
    rw [order_inv]
    omega)

def divisorClassToLineBundleClass (hdim : topologicalKrullDim X ≤ 1) :
    (Divisor X ⧸ (principal X).range) → LineBundleClass X :=
  Quotient.lift (fun D => Quotient.mk (lineBundleSetoid X) (divisorLineBundle X hdim D)) (by
    intro D E hDE
    obtain ⟨f, hf⟩ := QuotientAddGroup.leftRel_apply.mp hDE
    have hE : E = D + principal X f := by
      rw [hf]
      abel
    subst E
    apply Quotient.sound
    exact ⟨principalShiftIso X D f.toMul⟩)

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass

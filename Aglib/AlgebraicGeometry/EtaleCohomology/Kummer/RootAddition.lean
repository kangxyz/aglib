/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Torsor
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorSum

/-! # Multiplication of actual positive root classes

Multiplication of actual root sections constructs a coefficient-additive
morphism from the original product torsor. The complete generic contracted
sum construction supplies the Ext addition law. No torsor classification,
Picard comparison or global-unit root-surjectivity premise is needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

namespace GroupCohomology.Kummer.Torsor

universe u

variable (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
  (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))

/-- Multiply actual positive roots, retaining their original root torsors. -/
def rootMulSection (f g : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ)
    (s : (rootTorsor h X n hn hinv f).carrier.obj.obj U)
    (t : (rootTorsor h X n hn hinv g).carrier.obj.obj U) :
    (rootTorsor h X n hn hinv (f * g)).carrier.obj.obj U :=
  (rootSectionsEquiv h X n hn hinv (f * g) U).symm
    ⟨(rootSectionsEquiv h X n hn hinv f U s).val *
      (rootSectionsEquiv h X n hn hinv g U t).val, by
      rw [mul_pow, (rootSectionsEquiv h X n hn hinv f U s).property,
        (rootSectionsEquiv h X n hn hinv g U t).property]
      exact (map_mul (Units.map U.unop.hom.appTop.hom.toMonoidHom) f g).symm⟩

/-- The constructed section is multiplication on the original unit coordinates. -/
theorem rootMulSection_value (f g : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ)
    (s : (rootTorsor h X n hn hinv f).carrier.obj.obj U)
    (t : (rootTorsor h X n hn hinv g).carrier.obj.obj U) :
    (rootSectionsEquiv h X n hn hinv (f * g) U
      (rootMulSection h X n hn hinv f g U s t)).val =
    (rootSectionsEquiv h X n hn hinv f U s).val *
      (rootSectionsEquiv h X n hn hinv g U t).val :=
  congrArg Subtype.val ((rootSectionsEquiv h X n hn hinv (f * g) U).apply_symm_apply _)

/-- Original root restriction commutes with actual multiplication. -/
theorem rootMulSection_naturality (f g : Γ(X, ⊤)ˣ) {U V : X.Etaleᵒᵖ} (q : U ⟶ V)
    (s : (rootTorsor h X n hn hinv f).carrier.obj.obj U)
    (t : (rootTorsor h X n hn hinv g).carrier.obj.obj U) :
    (rootTorsor h X n hn hinv (f * g)).carrier.obj.map q
      (rootMulSection h X n hn hinv f g U s t) =
    rootMulSection h X n hn hinv f g V
      ((rootTorsor h X n hn hinv f).carrier.obj.map q s)
      ((rootTorsor h X n hn hinv g).carrier.obj.map q t) := by
  apply (rootSectionsEquiv h X n hn hinv (f * g) V).injective
  apply Subtype.ext
  rw [rootSections_naturality, rootMulSection_value, rootMulSection_value,
    rootSections_naturality, rootSections_naturality, map_mul]

/-- The original positive actions multiply, equivalently add their root coefficients. -/
theorem rootMulSection_equivariant (f g : Γ(X, ⊤)ˣ) (U : X.Etaleᵒᵖ)
    (a b : (mu X n).obj.obj U)
    (s : (rootTorsor h X n hn hinv f).carrier.obj.obj U)
    (t : (rootTorsor h X n hn hinv g).carrier.obj.obj U) :
    rootMulSection h X n hn hinv f g U
      ((rootTorsor h X n hn hinv f).action U a s)
      ((rootTorsor h X n hn hinv g).action U b t) =
    (rootTorsor h X n hn hinv (f * g)).action U (a + b)
      (rootMulSection h X n hn hinv f g U s t) := by
  apply (rootSectionsEquiv h X n hn hinv (f * g) U).injective
  apply Subtype.ext
  have hab : ((rootsSections X n U (a + b)).toMul : Γ(U.unop.left, ⊤)ˣ) =
      ((rootsSections X n U a).toMul : Γ(U.unop.left, ⊤)ˣ) *
        ((rootsSections X n U b).toMul : Γ(U.unop.left, ⊤)ˣ) :=
    congrArg (fun z : Additive (rootsOfUnity n Γ(U.unop.left, ⊤)) =>
      (z.toMul : Γ(U.unop.left, ⊤)ˣ)) ((rootsSections X n U).map_add a b)
  refine (rootMulSection_value h X n hn hinv f g U _ _).trans ?_
  refine (congrArg₂ (· * ·)
    (rootSections_action h X n hn hinv f U a s)
    (rootSections_action h X n hn hinv g U b t)).trans ?_
  refine Eq.trans ?_ ((congrArg₂ (· * ·) hab
    (rootMulSection_value h X n hn hinv f g U s t)).symm.trans
      (rootSections_action h X n hn hinv (f * g) U (a + b)
        (rootMulSection h X n hn hinv f g U s t)).symm)
  ac_rfl

/-- The actual multiplication morphism is relative to original coefficient addition. -/
def rootMulTorsorHom (f g : Γ(X, ⊤)ˣ) :
    Scheme.EtaleCohomology.Torsor.Hom (torsorCoefficientAdd (mu X n))
      (torsorProduct (rootTorsor h X n hn hinv f) (rootTorsor h X n hn hinv g))
      (rootTorsor h X n hn hinv (f * g)) where
  map := ⟨{ app U := ↾(fun s => rootMulSection h X n hn hinv f g U s.1 s.2)
            naturality {U V} q := by
              ext s
              exact (rootMulSection_naturality h X n hn hinv f g q s.1 s.2).symm }⟩
  equivariant U a s := rootMulSection_equivariant h X n hn hinv f g U a.1 a.2 s.1 s.2

universe w
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Multiplication of original positive root torsors is addition of their original Ext classes. -/
theorem rootClass_mul (f g : Γ(X, ⊤)ˣ) :
    rootClass h X n hn hinv (f * g) =
      rootClass h X n hn hinv f + rootClass h X n hn hinv g := by
  calc
    _ = coefficientMap (torsorCoefficientAdd (mu X n))
        (torsorExtClass (torsorProduct
          (rootTorsor h X n hn hinv f) (rootTorsor h X n hn hinv g))) :=
      (torsorExtClass_naturality (rootMulTorsorHom h X n hn hinv f g)).symm
    _ = torsorExtClass (torsorSum
        (rootTorsor h X n hn hinv f) (rootTorsor h X n hn hinv g)) :=
      (torsorExtClass_pushout _ _).symm
    _ = _ := torsorExtClass_sum _ _

/-- The original positive root-class map as an additive homomorphism on actual units. -/
def rootClassHom : Additive Γ(X, ⊤)ˣ →+ H1Etale X (mu X n) where
  toFun a := rootClass h X n hn hinv a.toMul
  map_zero' := by
    simpa using rootClass_eq_zero_of_power h X n hn hinv (1 : Γ(X, ⊤)ˣ)
  map_add' a b := rootClass_mul h X n hn hinv a.toMul b.toMul

end GroupCohomology.Kummer.Torsor

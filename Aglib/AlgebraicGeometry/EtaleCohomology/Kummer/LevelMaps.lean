/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-!
# Original roots coefficient maps between Kummer levels

The map `μ_(mn) → μ_n` is the original root-kernel lift of the m-th power map.
It is defined at every pair of natural levels, including zero. Its original
inclusion square determines its section values, identity, composition and
geometric pullback laws. Positivity and invertibility enter only for the
original Kummer short exact sequences and their connecting homomorphisms.
No primitive-root choices occur in these maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace GroupCohomology.Kummer.Coefficients

attribute [local instance] AlgebraicGeometry.Scheme.EtaleCohomology.hasSheafifyLarge

variable (X : Scheme.{u})

/-- Composition of the original multiplicative power maps multiplies their levels. -/
@[reassoc]
theorem power_comp (m n : ℕ) : power X m ≫ power X n = power X (m * n) := by
  simp only [power, Preadditive.nsmul_comp, Category.id_comp, smul_smul]

/-- Equality transport of the root coefficient retains its original inclusion. -/
@[reassoc]
theorem inclusion_eqToHom {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (mu X) h) ≫ inclusion X b = inclusion X a := by
  subst b
  simp

/-- The canonical roots power map is the lift into the original represented root kernel. -/
def rootsLevelMap (m n : ℕ) : mu X (m * n) ⟶ mu X n :=
  kernelLift X n (inclusion X (m * n) ≫ power X m) (by
    rw [Category.assoc, power_comp, inclusion_power])

/-- The whole coefficient map has the literal m-th power as its underlying units map. -/
@[reassoc]
theorem rootsLevelMap_inclusion (m n : ℕ) :
    rootsLevelMap X m n ≫ inclusion X n = inclusion X (m * n) ≫ power X m :=
  kernelLift_inclusion X n _ _

/-- The original section coordinate is exactly the m-th power of the original root. -/
theorem rootsLevelMap_sections (m n : ℕ) (V : X.Etaleᵒᵖ)
    (a : (mu X (m * n)).obj.obj V) :
    ((rootsSections X n V ((rootsLevelMap X m n).hom.app V a)).toMul :
        Γ(V.unop.left, ⊤)ˣ) =
      (((rootsSections X (m * n) V a).toMul : Γ(V.unop.left, ⊤)ˣ) ^ m) := by
  have h := congrArg (fun g : mu X (m * n) ⟶ gm X =>
    (unitsSections X V (g.hom.app V a)).toMul) (rootsLevelMap_inclusion X m n)
  change (unitsSections X V ((inclusion X n).hom.app V
      ((rootsLevelMap X m n).hom.app V a))).toMul =
    (unitsSections X V ((power X m).hom.app V
      ((inclusion X (m * n)).hom.app V a))).toMul at h
  rw [inclusion_apply, power_apply, inclusion_apply] at h
  exact h

/-- Multiplier one is the original equality transport, without a new coefficient isomorphism. -/
theorem rootsLevelMap_one (n : ℕ) :
    rootsLevelMap X 1 n = eqToHom (congrArg (mu X) (one_mul n)) := by
  apply (cancel_mono (inclusion X n)).mp
  rw [rootsLevelMap_inclusion, inclusion_eqToHom X (one_mul n)]
  simp only [power, one_nsmul, Category.comp_id]

/-- The whole level family composes by actual powers and original arithmetic equality transport. -/
theorem rootsLevelMap_comp (a b n : ℕ) :
    rootsLevelMap X a (b * n) ≫ rootsLevelMap X b n =
      eqToHom (congrArg (mu X) (Nat.mul_assoc a b n).symm) ≫
        rootsLevelMap X (a * b) n := by
  apply (cancel_mono (inclusion X n)).mp
  simp only [Category.assoc, rootsLevelMap_inclusion]
  rw [← Category.assoc, rootsLevelMap_inclusion]
  simp only [Category.assoc, power_comp]
  rw [← Category.assoc, inclusion_eqToHom X (Nat.mul_assoc a b n).symm]

/-- The map of the original Kummer short complexes, with power m in the middle and identity
on the right-hand units sheaf. -/
def sequenceLevelHom (m n : ℕ) : sequence X (m * n) ⟶ sequence X n where
  τ₁ := rootsLevelMap X m n
  τ₂ := power X m
  τ₃ := 𝟙 (gm X)
  comm₁₂ := rootsLevelMap_inclusion X m n
  comm₂₃ := by
    change power X m ≫ power X n = power X (m * n) ≫ 𝟙 (gm X)
    rw [power_comp, Category.comp_id]

end GroupCohomology.Kummer.Coefficients

namespace GroupCohomology.Kummer.CoefficientBaseChange

open Coefficients AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X)

/-- The literal roots units commute with the whole original level maps at every level. -/
theorem rootsLevelMap_unit (m n : ℕ) :
    rootsLevelMap X m n ≫ rootsUnit f n =
      rootsUnit f (m * n) ≫ (directImage f).map (rootsLevelMap S m n) := by
  apply (cancel_mono ((directImage f).map (inclusion S n))).mp
  simp only [Category.assoc]
  rw [← Kummer.inclusion_unit f n, ← (directImage f).map_comp,
    rootsLevelMap_inclusion, (directImage f).map_comp]
  simp only [← Category.assoc]
  rw [rootsLevelMap_inclusion, ← Kummer.inclusion_unit f (m * n)]
  simp only [Category.assoc]
  apply congrArg (fun a => inclusion X (m * n) ≫ a)
  simp only [power, CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- Geometric inverse image preserves the canonical roots power map through the original
roots pullback isomorphisms. -/
theorem rootsLevelMap_pullback (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (hinv' : IsUnit ((m * n : ℕ) : Γ(X, ⊤))) :
    (inverseImage f).map (rootsLevelMap X m n) ≫ (rootsPullbackIso f n hn hinv).hom =
      (rootsPullbackIso f (m * n) (Nat.mul_pos hm hn) hinv').hom ≫ rootsLevelMap S m n := by
  rw [← rootsUnit_adjoint f n hn hinv,
    ← rootsUnit_adjoint f (m * n) (Nat.mul_pos hm hn) hinv']
  exact Kummer.adjoint_square (inverseImageAdjunction f)
    (rootsLevelMap X m n) (rootsLevelMap S m n)
    (rootsUnit f (m * n)) (rootsUnit f n) (rootsLevelMap_unit f m n)

/-- The same whole coefficient square in the inverse-comparison orientation
used by the original lower-shriek counits and finite traces. -/
theorem rootsLevelMap_pullback_inv (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (hinv' : IsUnit ((m * n : ℕ) : Γ(X, ⊤))) :
    rootsLevelMap S m n ≫ (rootsPullbackIso f n hn hinv).inv =
      (rootsPullbackIso f (m * n) (Nat.mul_pos hm hn) hinv').inv ≫
        (inverseImage f).map (rootsLevelMap X m n) := by
  apply (cancel_mono (rootsPullbackIso f n hn hinv).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rootsLevelMap_pullback f m n hm hn hinv hinv', Iso.inv_hom_id_assoc]

end GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open GroupCohomology.Kummer.Coefficients

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(X, ⊤))) (hinv' : IsUnit ((m * n : ℕ) : Γ(X, ⊤)))

/-- The entire original Kummer boundary commutes with reduction of its roots level. -/
theorem boundary_level (q : ℕ) :
    (Sheaf.H.map (rootsLevelMap X m n) (q + 1)).comp
        (boundary X (m * n) (Nat.mul_pos hm hn) hinv' q) =
      boundary X n hn hinv q := by
  apply AddMonoidHom.ext
  intro a
  have h := Sheaf.H.δ_naturality q (q + 1) rfl
    (shortExact X (m * n) (Nat.mul_pos hm hn) hinv') (shortExact X n hn hinv)
    (sequenceLevelHom X m n) a
  change boundary X n hn hinv q (Sheaf.H.map (𝟙 (gm X)) q a) =
    Sheaf.H.map (rootsLevelMap X m n) (q + 1)
      (boundary X (m * n) (Nat.mul_pos hm hn) hinv' q a) at h
  rw [Sheaf.H.map_id_apply] at h
  exact h.symm

/-- The original Picard boundary has the same class on the right of the Kummer level square. -/
theorem picardBoundary_level :
    (Sheaf.H.map (rootsLevelMap X m n) 2).comp
        (picardBoundary X (m * n) (Nat.mul_pos hm hn) hinv') =
      picardBoundary X n hn hinv := by
  apply AddMonoidHom.ext
  intro a
  exact DFunLike.congr_fun (boundary_level X m n hm hn hinv hinv' 1)
    (Picard.picardCohomologyEquiv X a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

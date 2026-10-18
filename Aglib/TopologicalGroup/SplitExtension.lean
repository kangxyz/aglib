/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.MulAction

/-!
# Coordinates for an actual continuous split extension

Construction prerequisite for `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, on the source basis
`e73d98b1b5c1e5abcdebf7d058e436d792b87982` used by
`R5Lab.Galois.PointedCohomology`.

The inputs are actual groups, a projection homomorphism `p`, a section
homomorphism `s`, the identity `p (s g) = g`, and their continuity proofs.
Conjugation preserves the actual subgroup `p.ker`; its action and continuity
are proved, rather than supplied as hypotheses. The product coordinates have
the constructed multiplication `(n, g) * (m, h) = (n * g • m, g * h)` and
inherited kernel/product topology. The coordinate homeomorphism has formulas
`e ↦ (e * s (p e)⁻¹, p e)` and `(n, g) ↦ n * s g`.

`coordinateGroup` is a group structure on the product set, with semidirect
multiplication. `coordinateMulEquiv` explicitly selects its multiplication;
the ordinary product-group instance on the same set is also available in Lean.
The cocycle consumer only needs the constructed `kernelAction`, its proved
`kernelContinuousSMul`, and the product-coordinate formulas.

This module proves the general algebraic and topological constructor. It does
not identify the kernel with a geometric fundamental group, instantiate the
scheme-induced maps, or compare continuous cohomology with étale H¹.
-/

@[expose] public section

namespace TopologicalGroup.SplitExtension

variable {E G : Type*} [Group E] [Group G]

/-- Kernel identity, auxiliary to `K2-018#eq:k2018-pointed-character`'s
split-extension construction, on the module source basis. -/
@[simp] theorem kernel_projection (p : E →* G) (n : p.ker) : p (n : E) = 1 :=
  n.property

/-- Conjugation preserves the actual kernel. Construction prerequisite for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
def kernelConjugate (p : E →* G) (s : G →* E) (g : G) (n : p.ker) : p.ker :=
  ⟨s g * n * (s g)⁻¹, by
    change p (s g * (n : E) * (s g)⁻¹) = 1
    simp [map_mul]⟩

/-- Conjugation formula for the `K2-018#eq:k2018-pointed-character`
construction prerequisite, on the module source basis. -/
@[simp] theorem kernelConjugate_val (p : E →* G) (s : G →* E)
    (g : G) (n : p.ker) :
    (kernelConjugate p s g n : E) = s g * n * (s g)⁻¹ := rfl

/-- Constructed kernel action for `K2-018#eq:k2018-pointed-character`,
on the module source basis. Only the actual homomorphisms are inputs. -/
abbrev kernelAction (p : E →* G) (s : G →* E) : MulDistribMulAction G p.ker where
  smul := kernelConjugate p s
  one_smul n := by
    change kernelConjugate p s 1 n = n
    apply Subtype.ext
    simp [kernelConjugate]
  mul_smul g h n := by
    change kernelConjugate p s (g * h) n =
      kernelConjugate p s g (kernelConjugate p s h n)
    apply Subtype.ext
    simp [kernelConjugate, map_mul, mul_inv_rev, mul_assoc]
  smul_one g := by
    change kernelConjugate p s g 1 = 1
    apply Subtype.ext
    simp [kernelConjugate]
  smul_mul g n m := by
    change kernelConjugate p s g (n * m) =
      kernelConjugate p s g n * kernelConjugate p s g m
    apply Subtype.ext
    simp [kernelConjugate, mul_assoc]

/-- The action is actual conjugation for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
theorem kernelAction_smul_val (p : E →* G) (s : G →* E) (g : G) (n : p.ker) :
    letI := kernelAction p s
    ((g • n : p.ker) : E) = s g * n * (s g)⁻¹ := rfl

/-- Semidirect multiplication for the `K2-018#eq:k2018-pointed-character`
construction prerequisite, on the module source basis. -/
def coordinateMul (p : E →* G) (s : G →* E) (x y : p.ker × G) : p.ker × G :=
  (x.1 * kernelConjugate p s x.2 y.1, x.2 * y.2)

/-- Action-notation multiplication for the `K2-018#eq:k2018-pointed-character`
construction prerequisite, on the module source basis. -/
theorem coordinateMul_eq (p : E →* G) (s : G →* E)
    (n m : p.ker) (g h : G) :
    letI := kernelAction p s
    coordinateMul p s (n, g) (m, h) = (n * g • m, g * h) := rfl

/-- Semidirect inversion for the `K2-018#eq:k2018-pointed-character`
construction prerequisite, on the module source basis. -/
def coordinateInv (p : E →* G) (s : G →* E) (x : p.ker × G) : p.ker × G :=
  (kernelConjugate p s x.2⁻¹ x.1⁻¹, x.2⁻¹)

/-- Semidirect group structure for `K2-018#eq:k2018-pointed-character`,
on the module source basis. This structure has the specified coordinate
multiplication; the standard product-group instance has a different multiplication. -/
abbrev coordinateGroup (p : E →* G) (s : G →* E) : Group (p.ker × G) where
  mul := coordinateMul p s
  one := (1, 1)
  inv := coordinateInv p s
  div x y := coordinateMul p s x (coordinateInv p s y)
  npow := @npowRec (p.ker × G) ⟨(1, 1)⟩ ⟨coordinateMul p s⟩
  zpow := @zpowRec (p.ker × G) ⟨(1, 1)⟩ ⟨coordinateMul p s⟩ ⟨coordinateInv p s⟩
    (@npowRec (p.ker × G) ⟨(1, 1)⟩ ⟨coordinateMul p s⟩)
  mul_assoc x y z := by
    let := kernelAction p s
    apply Prod.ext
    · change (x.1 * x.2 • y.1) * (x.2 * y.2) • z.1 =
        x.1 * x.2 • (y.1 * y.2 • z.1)
      simp [mul_smul, smul_mul', mul_assoc]
    · exact mul_assoc _ _ _
  one_mul x := by
    let := kernelAction p s
    apply Prod.ext
    · change 1 * (1 : G) • x.1 = x.1
      simp
    · exact one_mul _
  mul_one x := by
    let := kernelAction p s
    apply Prod.ext
    · change x.1 * x.2 • (1 : p.ker) = x.1
      simp
    · exact mul_one _
  inv_mul_cancel x := by
    let := kernelAction p s
    apply Prod.ext
    · change (x.2⁻¹ • x.1⁻¹) * x.2⁻¹ • x.1 = 1
      rw [← smul_mul']
      simp
    · exact inv_mul_cancel _

/-- Forward coordinates for the `K2-018#eq:k2018-pointed-character`
construction prerequisite, on the module source basis. Uses the actual splitting identity. -/
def toCoordinates (p : E →* G) (s : G →* E) (hps : ∀ g, p (s g) = g)
    (e : E) : p.ker × G :=
  (⟨e * (s (p e))⁻¹, by
    change p (e * (s (p e))⁻¹) = 1
    simp [map_mul, hps]⟩, p e)

/-- Forward kernel-coordinate formula for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
@[simp] theorem toCoordinates_fst_val (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (e : E) :
    ((toCoordinates p s hps e).1 : E) = e * (s (p e))⁻¹ := rfl

/-- Reassembly map for the `K2-018#eq:k2018-pointed-character`
construction prerequisite, on the module source basis. -/
def fromCoordinates (p : E →* G) (s : G →* E) (x : p.ker × G) : E :=
  x.1 * s x.2

/-- Reassembly after decomposition for `K2-018#eq:k2018-pointed-character`'s
construction prerequisite, on the module source basis. -/
@[simp] theorem fromCoordinates_toCoordinates (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (e : E) :
    fromCoordinates p s (toCoordinates p s hps e) = e := by
  simp [fromCoordinates, toCoordinates, mul_assoc]

/-- Decomposition after reassembly for `K2-018#eq:k2018-pointed-character`'s
construction prerequisite, on the module source basis. -/
@[simp] theorem toCoordinates_fromCoordinates (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (x : p.ker × G) :
    toCoordinates p s hps (fromCoordinates p s x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    simp [fromCoordinates, toCoordinates, map_mul, hps, mul_assoc]
  · simp [fromCoordinates, toCoordinates, map_mul, hps]

/-- Derived coordinate equivalence for `K2-018#eq:k2018-pointed-character`,
on the module source basis. No decomposition is assumed. -/
def coordinateEquiv (p : E →* G) (s : G →* E) (hps : ∀ g, p (s g) = g) :
    E ≃ p.ker × G where
  toFun := toCoordinates p s hps
  invFun := fromCoordinates p s
  left_inv := fromCoordinates_toCoordinates p s hps
  right_inv := toCoordinates_fromCoordinates p s hps

/-- Multiplication in forward coordinates for `K2-018#eq:k2018-pointed-character`,
on the module source basis; this is the cocycle consumer's group law. -/
theorem toCoordinates_mul (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (e f : E) :
    toCoordinates p s hps (e * f) =
      coordinateMul p s (toCoordinates p s hps e) (toCoordinates p s hps f) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [toCoordinates, coordinateMul, kernelConjugate, map_mul, mul_inv_rev, mul_assoc]
  · exact map_mul p e f

/-- Reassembly preserves semidirect multiplication for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem fromCoordinates_mul (p : E →* G) (s : G →* E) (x y : p.ker × G) :
    fromCoordinates p s (coordinateMul p s x y) =
      fromCoordinates p s x * fromCoordinates p s y := by
  simp [fromCoordinates, coordinateMul, kernelConjugate, map_mul, mul_assoc]

/-- Reassembly multiplication in the cocycle consumer's action notation for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem fromCoordinates_mul_action (p : E →* G) (s : G →* E)
    (n m : p.ker) (g h : G) :
    letI := kernelAction p s
    fromCoordinates p s (n * g • m, g * h) =
      fromCoordinates p s (n, g) * fromCoordinates p s (m, h) :=
  fromCoordinates_mul p s (n, g) (m, h)

/-- Inversion in forward coordinates for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
theorem toCoordinates_inv (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (e : E) :
    toCoordinates p s hps e⁻¹ = coordinateInv p s (toCoordinates p s hps e) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [toCoordinates, coordinateInv, kernelConjugate, mul_inv_rev]
  · exact map_inv p e

/-- Reassembly preserves semidirect inversion for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem fromCoordinates_inv (p : E →* G) (s : G →* E) (x : p.ker × G) :
    fromCoordinates p s (coordinateInv p s x) = (fromCoordinates p s x)⁻¹ := by
  simp [fromCoordinates, coordinateInv, kernelConjugate, mul_inv_rev, mul_assoc]

/-- Derived group isomorphism for `K2-018#eq:k2018-pointed-character`,
on the module source basis, with the proved semidirect multiplication selected explicitly. -/
def coordinateMulEquiv (p : E →* G) (s : G →* E) (hps : ∀ g, p (s g) = g) :
    letI : Mul (p.ker × G) := (coordinateGroup p s).toMul
    E ≃* p.ker × G := by
  letI : Mul (p.ker × G) := (coordinateGroup p s).toMul
  exact { coordinateEquiv p s hps with map_mul' := toCoordinates_mul p s hps }

/-- Actual projection in coordinates for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
@[simp] theorem toCoordinates_projection (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (e : E) : (toCoordinates p s hps e).2 = p e := rfl

/-- Actual section in coordinates for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
@[simp] theorem toCoordinates_section (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (g : G) :
    toCoordinates p s hps (s g) = (1, g) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [toCoordinates, hps]
  · exact hps g

/-- Actual kernel inclusion in coordinates for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
@[simp] theorem toCoordinates_kernel (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (n : p.ker) :
    toCoordinates p s hps (n : E) = (n, 1) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [toCoordinates]
  · exact n.property

/-- Projection of reassembly for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
@[simp] theorem projection_fromCoordinates (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (x : p.ker × G) :
    p (fromCoordinates p s x) = x.2 := by
  simp [fromCoordinates, map_mul, hps]

/-- Reassembly of section coordinates for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
@[simp] theorem fromCoordinates_section (p : E →* G) (s : G →* E) (g : G) :
    fromCoordinates p s (1, g) = s g := by
  simp [fromCoordinates]

/-- Reassembly of kernel coordinates for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
@[simp] theorem fromCoordinates_kernel (p : E →* G) (s : G →* E) (n : p.ker) :
    fromCoordinates p s (n, 1) = n := by
  simp [fromCoordinates]

section Topology

variable [TopologicalSpace E] [TopologicalSpace G]
  [IsTopologicalGroup E]

/-- Joint continuity of the constructed kernel action for
`K2-018#eq:k2018-pointed-character`, on the module source basis.
Uses only continuity of the actual section and the ambient topological-group structure. -/
theorem continuous_kernelConjugate (p : E →* G) (s : G →* E) (hs : Continuous s) :
    Continuous (fun x : G × p.ker => kernelConjugate p s x.1 x.2) := by
  apply Continuous.subtype_mk
  exact ((hs.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).mul (hs.comp continuous_fst).inv

/-- Continuous action instance for `K2-018#eq:k2018-pointed-character`,
on the module source basis. Install the constructed action first. -/
theorem kernelContinuousSMul (p : E →* G) (s : G →* E) (hs : Continuous s) :
    letI := kernelAction p s
    ContinuousSMul G p.ker := by
  let := kernelAction p s
  exact ⟨continuous_kernelConjugate p s hs⟩

/-- Forward continuity for `K2-018#eq:k2018-pointed-character`'s
construction prerequisite, on the module source basis. -/
theorem continuous_toCoordinates (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (hp : Continuous p) (hs : Continuous s) :
    Continuous (toCoordinates p s hps) := by
  exact ((continuous_id.mul (hs.comp hp).inv).subtype_mk _).prodMk hp

/-- Inverse continuity for `K2-018#eq:k2018-pointed-character`'s
construction prerequisite, on the module source basis. -/
theorem continuous_fromCoordinates (p : E →* G) (s : G →* E) (hs : Continuous s) :
    Continuous (fromCoordinates p s) :=
  (continuous_subtype_val.comp continuous_fst).mul (hs.comp continuous_snd)

/-- Derived coordinate homeomorphism for `K2-018#eq:k2018-pointed-character`,
on the module source basis, for the inherited kernel and product topology. -/
def coordinateHomeomorph (p : E →* G) (s : G →* E)
    (hps : ∀ g, p (s g) = g) (hp : Continuous p) (hs : Continuous s) :
    E ≃ₜ p.ker × G where
  toEquiv := coordinateEquiv p s hps
  continuous_toFun := continuous_toCoordinates p s hps hp hs
  continuous_invFun := continuous_fromCoordinates p s hs

variable [IsTopologicalGroup G]

/-- Joint continuity of the semidirect multiplication for
`K2-018#eq:k2018-pointed-character`, on the module source basis. -/
theorem continuous_coordinateMul (p : E →* G) (s : G →* E) (hs : Continuous s) :
    Continuous (fun z : (p.ker × G) × (p.ker × G) => coordinateMul p s z.1 z.2) := by
  let := kernelAction p s
  let := kernelContinuousSMul p s hs
  exact ((continuous_fst.fst).mul (continuous_fst.snd.smul continuous_snd.fst)).prodMk
    (continuous_fst.snd.mul continuous_snd.snd)

/-- Continuity of semidirect inversion for `K2-018#eq:k2018-pointed-character`,
on the module source basis. -/
theorem continuous_coordinateInv (p : E →* G) (s : G →* E) (hs : Continuous s) :
    Continuous (coordinateInv p s) := by
  let := kernelAction p s
  let := kernelContinuousSMul p s hs
  exact (continuous_snd.inv.smul continuous_fst.inv).prodMk continuous_snd.inv

/-- Topological semidirect group for `K2-018#eq:k2018-pointed-character`,
on the module source basis. Both operations are proved continuous in the product topology. -/
theorem coordinateIsTopologicalGroup (p : E →* G) (s : G →* E) (hs : Continuous s) :
    letI := coordinateGroup p s
    IsTopologicalGroup (p.ker × G) := by
  let := coordinateGroup p s
  exact { continuous_mul := continuous_coordinateMul p s hs
          continuous_inv := continuous_coordinateInv p s hs }

end Topology
end TopologicalGroup.SplitExtension

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 a86aee9bb001d9a81d66595ba91a74708c1e1dbe540e848a952ee7bf24b692f8.
Definitions, hypotheses and universes are retained modulo native names. -/

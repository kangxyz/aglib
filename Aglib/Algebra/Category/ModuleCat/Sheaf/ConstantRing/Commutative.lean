/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Basic
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Commutativity of the original constant ring sheaf

If the coefficient ring is commutative, sections of its original RingCat-valued
constant ring sheaf commute: locally they lift through the original constant
ring unit, and equality is detected by sheaf separation. Adding this proof to
the original section rings gives a CommRingCat-valued sheaf whose underlying
ring sheaf is literally the existing constant ring sheaf. No ring transport,
new module carrier or second sheafification model is introduced.

This is the coefficient boundary needed to apply the existing commutative-ring
internal-Hom construction to the actual constant-ring module sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type r) [CommRing Λ] [HasWeakSheafify J RingCat.{r}]
  [J.WEqualsLocallyBijective RingCat.{r}] [J.HasSheafCompose (forget RingCat.{r})]

/-- Sections of the original constant sheaf of a commutative ring commute. -/
theorem section_mul_comm (U : Cᵒᵖ) (a b : (constantRing J Λ).obj.obj U) : a * b = b * a := by
  let η := constantRingUnit J Λ
  apply (constantRing J Λ).isSeparated U.unop
    (Presheaf.imageSieve η a ⊓ Presheaf.imageSieve η b)
    (J.intersection_covering (Presheaf.imageSieve_mem J η a) (Presheaf.imageSieve_mem J η b))
  intro V f hf
  obtain ⟨x, hx⟩ := hf.1
  obtain ⟨y, hy⟩ := hf.2
  change Λ at x y
  change ((constantRing J Λ).obj.map f.op).hom (a * b) =
    ((constantRing J Λ).obj.map f.op).hom (b * a)
  rw [map_mul, map_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm x y]

/-- The original section ring with its proved commutativity, retaining the original ring parent. -/
abbrev commRingSection (U : Cᵒᵖ) : CommRing ((constantRing J Λ).obj.obj U) where
  __ := (inferInstance : Ring ((constantRing J Λ).obj.obj U))
  mul_comm := section_mul_comm J Λ U

/-- The unchanged original constant-ring presheaf with commutative ring objects. -/
def commutativePresheaf : Cᵒᵖ ⥤ CommRingCat.{r} where
  obj U :=
    letI := commRingSection J Λ U
    CommRingCat.of ((constantRing J Λ).obj.obj U)
  map {U V} f := by
    letI := commRingSection J Λ U
    letI := commRingSection J Λ V
    exact CommRingCat.ofHom ((constantRing J Λ).obj.map f).hom
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom ((constantRing J Λ).obj.map_id U) x
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom ((constantRing J Λ).obj.map_comp f g) x

/-- Forgetting commutativity retains the exact original constant-ring presheaf. -/
theorem commutativePresheaf_forget :
    commutativePresheaf J Λ ⋙ forget₂ CommRingCat RingCat = (constantRing J Λ).obj := rfl

/-- The actual constant ring sheaf equipped with its proved commutative structure. -/
def commutativeSheaf : Sheaf J CommRingCat.{r} where
  obj := commutativePresheaf J Λ
  property := Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ CommRingCat RingCat)
    (constantRing J Λ).property

variable [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

/-- The commutative lift has literally the original underlying constant ring sheaf. -/
theorem commutativeSheaf_forget :
    (sheafCompose J (forget₂ CommRingCat RingCat)).obj (commutativeSheaf J Λ) =
      constantRing J Λ := rfl

end ModuleCat.Sheaf.ConstantRing

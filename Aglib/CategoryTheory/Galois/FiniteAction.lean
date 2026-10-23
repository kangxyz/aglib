/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.GroupTheory.GroupAction.Quotient

/-! # The actual finite quotient action supplied by a Galois representative

Evaluation-surjectivity forces the stabilizer of the representing point to
act trivially on the represented fibre. The original fibre permutation action
therefore descends through its native finite stabilizer quotient.
-/

@[expose] public noncomputable section

namespace CategoryTheory.PreGaloisCategory

universe c h v

variable {C : Type c} [Category.{h} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{v}) [FiberFunctor F]
  {T A : C} (a : F.obj T)
  (heval : Function.Surjective (fun f : T ⟶ A => F.map f a))

omit [GaloisCategory C] [FiberFunctor F] in
include heval in
/-- Stabilizers of the chosen representing point act trivially on the whole
represented fibre, by the literal naturality square. -/
theorem stabilizer_le_fiberAction_ker :
    MulAction.stabilizer (Aut F) a ≤ (MulAction.toPermHom (Aut F) (F.obj A)).ker := by
  intro g hg
  change MulAction.toPermHom (Aut F) (F.obj A) g = 1
  ext x
  obtain ⟨f, rfl⟩ := heval x
  change g • F.map f a = F.map f a
  rw [mulAction_naturality, (MulAction.mem_stabilizer_iff.mp hg)]

omit [GaloisCategory C] [FiberFunctor F] in
/-- The native stabilizer quotient is finite because its orbit is a subset of
the finite fibre of the representing object. -/
theorem finite_fiberStabilizerQuotient :
    Finite ((Aut F) ⧸ MulAction.stabilizer (Aut F) a) :=
  Finite.of_equiv (MulAction.orbit (Aut F) a)
    (MulAction.orbitEquivQuotientStabilizer (Aut F) a)

variable [IsGalois T]

attribute [local instance] stabilizer_normal_of_isGalois

/-- The original fibre permutation action descends through the actual finite
normal stabilizer quotient of the Galois representing object. -/
def fiberQuotientAction :
    ((Aut F) ⧸ MulAction.stabilizer (Aut F) a) →* Equiv.Perm (F.obj A) :=
  QuotientGroup.lift _ (MulAction.toPermHom (Aut F) (F.obj A))
    (stabilizer_le_fiberAction_ker F a heval)

/-- Evaluation on the quotient class retains the literal original action. -/
@[simp] theorem fiberQuotientAction_mk (g : Aut F) (x : F.obj A) :
    fiberQuotientAction F a heval (QuotientGroup.mk g) x = g • x := rfl

end CategoryTheory.PreGaloisCategory

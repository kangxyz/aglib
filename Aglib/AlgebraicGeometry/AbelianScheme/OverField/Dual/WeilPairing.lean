/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.KernelIso
public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationRoots
public import Aglib.AlgebraicGeometry.Group.Kernel.MultiplicationAnnihilation

/-! The original Weil pairing with values in the actual roots scheme. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open Scheme.OverField Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

private structure WeilPairingData {k : Type u} [Field k] (T : FScheme k) (n : ℕ) where
  roots : T ⟶ MultiplicativeGroup.rootsScheme (Base k) n
  evaluation : T ⟶ MultiplicativeGroup.scheme (Base k)
  inclusion : roots ≫ MultiplicativeGroup.rootsInclusion (Base k) n = evaluation

private def evaluationRootsData {k : Type u} [Field k] {G H : Grp (FScheme k)}
    [IsFinite G.X.hom] [IsCommMonObj G.X] (f : H ⟶ CartierDuality.dualGroup G)
    (n : ℕ) (hkill : (𝟙 G.X) ^ n = 1) :
    WeilPairingData (G.X ⊗ H.X) n :=
  let a := 𝟙 G.X ⊗ₘ f.hom.hom
  ⟨a ≫ CartierDuality.evaluationRoots G n hkill,
    a ≫ CartierDuality.evaluation G,
    CartierDuality.comp_evaluationRoots_comp_inclusion G n hkill a⟩

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

variable [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]

private def weilPairingData (n : ℕ) (hn : 0 < n) :
    WeilPairingData ((MultiplicationKernel.kernelGroup A n).X ⊗
      (dualMultiplicationKernel A P R n).X) n := by
  let G := MultiplicationKernel.kernelGroup A n
  let H := dualMultiplicationKernel A P R n
  let fin : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let comm : IsCommMonObj G.X :=
    Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let f : H ⟶ @CartierDuality.dualGroup k _ G fin comm := multiplicationKernelCartierHom A P R n hn
  let hkill : (𝟙 G.X) ^ n = 1 := Kernel.multiplication_kernel_pow_eq_one A n
  exact @evaluationRootsData k _ G H fin comm f n hkill

/-- The original pairing taking values in the actual roots scheme. -/
@[no_expose]
def weilPairingMorphism (n : ℕ) (hn : 0 < n) :
    (MultiplicationKernel.kernelGroup A n).X ⊗ (dualMultiplicationKernel A P R n).X ⟶
      MultiplicativeGroup.rootsScheme (Base k) n :=
  (weilPairingData A P R n hn).roots

/-- The original evaluation of the original normalized character map. -/
@[no_expose]
def weilPairingEvaluation (n : ℕ) (hn : 0 < n) :
    (MultiplicationKernel.kernelGroup A n).X ⊗ (dualMultiplicationKernel A P R n).X ⟶
      MultiplicativeGroup.scheme (Base k) :=
  (weilPairingData A P R n hn).evaluation

/-- The root inclusion recovers the same original evaluation. -/
theorem weilPairingMorphism_comp_inclusion (n : ℕ) (hn : 0 < n) :
    weilPairingMorphism A P R n hn ≫ MultiplicativeGroup.rootsInclusion (Base k) n =
      weilPairingEvaluation A P R n hn :=
  (weilPairingData A P R n hn).inclusion

/-- The original evaluation uses the original normalized character map. -/
theorem weilPairingEvaluation_eq (n : ℕ) (hn : 0 < n) :
    let G := MultiplicationKernel.kernelGroup A n
    let fin := Multiplication.kernelGroup_isFinite_of_pos A n hn
    let comm := Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
    weilPairingEvaluation A P R n hn =
      (𝟙 G.X ⊗ₘ (multiplicationKernelCartierHom A P R n hn).hom.hom) ≫
        @CartierDuality.evaluation k _ G fin comm := by
  unfold weilPairingEvaluation weilPairingData evaluationRootsData
  rfl

end AlgebraicGeometry.Scheme.RelativePicard

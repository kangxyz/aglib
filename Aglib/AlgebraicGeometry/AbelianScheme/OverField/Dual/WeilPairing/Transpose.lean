/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing
public import Aglib.AlgebraicGeometry.Group.CartierDuality.Functor.Iso

/-! The second adjoint of the original Weil pairing by Cartier biduality. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory BraidedCategory
open Scheme.OverField Scheme.Group

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

private structure TransposeData {k : Type u} [Field k] (T : FScheme k) where
  first : T ⟶ MultiplicativeGroup.scheme (Base k)
  second : T ⟶ MultiplicativeGroup.scheme (Base k)
  transpose : first = second

private def transposeEvaluationData {k : Type u} [Field k] {G H : Grp (FScheme k)}
    [IsFinite G.X.hom] [IsFinite H.X.hom] [IsCommMonObj G.X] [IsCommMonObj H.X]
    (f : H ⟶ CartierDuality.dualGroup G) (e : H ≅ CartierDuality.dualGroup G)
    (h : f = e.hom) : TransposeData (G.X ⊗ H.X) :=
  ⟨(𝟙 G.X ⊗ₘ f.hom.hom) ≫ CartierDuality.evaluation G,
    (β_ G.X H.X).hom ≫ (𝟙 H.X ⊗ₘ (CartierDuality.evaluationTransposeIso e).hom.hom.hom) ≫
      CartierDuality.evaluation H,
    (congrArg (fun g : H ⟶ CartierDuality.dualGroup G =>
      (𝟙 G.X ⊗ₘ g.hom.hom) ≫ CartierDuality.evaluation G) h).trans
      (CartierDuality.evaluation_transpose e)⟩

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom] [IsCommMonObj A.X]

/-- The other original adjoint, using native Cartier biduality. -/
@[no_expose]
def weilPairingTransposeIso (n : ℕ) (hn : 0 < n) :
    letI := isFinite_dualMultiplicationKernel A P R n hn
    letI := isCommMonObj_dualMultiplicationKernel A P R n
    MultiplicationKernel.kernelGroup A n ≅
      CartierDuality.dualGroup (dualMultiplicationKernel A P R n) := by
  let G := MultiplicationKernel.kernelGroup A n
  let H := dualMultiplicationKernel A P R n
  let : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let : IsCommMonObj G.X := Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let : IsFinite H.X.hom := isFinite_dualMultiplicationKernel A P R n hn
  let : IsCommMonObj H.X := isCommMonObj_dualMultiplicationKernel A P R n
  exact CartierDuality.evaluationTransposeIso (G := G) (H := H)
    (multiplicationKernelCartierIso A P R n hn)

private def weilTransposeData (n : ℕ) (hn : 0 < n) :
    TransposeData ((MultiplicationKernel.kernelGroup A n).X ⊗
      (dualMultiplicationKernel A P R n).X) := by
  let G := MultiplicationKernel.kernelGroup A n
  let H := dualMultiplicationKernel A P R n
  let finG : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let commG : IsCommMonObj G.X :=
    Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let finH : IsFinite H.X.hom := isFinite_dualMultiplicationKernel A P R n hn
  let commH : IsCommMonObj H.X := isCommMonObj_dualMultiplicationKernel A P R n
  let f : H ⟶ @CartierDuality.dualGroup k _ G finG commG :=
    multiplicationKernelCartierHom A P R n hn
  let e : H ≅ @CartierDuality.dualGroup k _ G finG commG :=
    multiplicationKernelCartierIso A P R n hn
  have h : e.hom = f := multiplicationKernelCartierIso_hom A P R n hn
  exact @transposeEvaluationData k _ G H finG finH commG commH f e h.symm

private theorem weilPairingEvaluation_eq_first (n : ℕ) (hn : 0 < n) :
    weilPairingEvaluation A P R n hn = (weilTransposeData A P R n hn).first := by
  unfold weilTransposeData transposeEvaluationData
  exact weilPairingEvaluation_eq A P R n hn

/-- The same original evaluation described by the other adjoint. -/
@[no_expose]
def weilPairingTransposeEvaluation (n : ℕ) (hn : 0 < n) :
    (MultiplicationKernel.kernelGroup A n).X ⊗ (dualMultiplicationKernel A P R n).X ⟶
      MultiplicativeGroup.scheme (Base k) :=
  (weilTransposeData A P R n hn).second

/-- The same original root factor also has the transpose evaluation. -/
theorem weilPairingMorphism_comp_inclusion_transpose (n : ℕ) (hn : 0 < n) :
    weilPairingMorphism A P R n hn ≫ MultiplicativeGroup.rootsInclusion (Base k) n =
      weilPairingTransposeEvaluation A P R n hn :=
  (weilPairingMorphism_comp_inclusion A P R n hn).trans
    ((weilPairingEvaluation_eq_first A P R n hn).trans (weilTransposeData A P R n hn).transpose)

/-- The transpose uses the original swapped evaluation and original other adjoint. -/
theorem weilPairingTransposeEvaluation_eq (n : ℕ) (hn : 0 < n) :
    let G := MultiplicationKernel.kernelGroup A n
    let H := dualMultiplicationKernel A P R n
    let fin := isFinite_dualMultiplicationKernel A P R n hn
    let comm := isCommMonObj_dualMultiplicationKernel A P R n
    weilPairingTransposeEvaluation A P R n hn =
      (β_ G.X H.X).hom ≫ (𝟙 H.X ⊗ₘ (weilPairingTransposeIso A P R n hn).hom.hom.hom) ≫
        @CartierDuality.evaluation k _ H fin comm := by
  unfold weilPairingTransposeEvaluation weilTransposeData transposeEvaluationData
    weilPairingTransposeIso
  rfl

end AlgebraicGeometry.Scheme.RelativePicard

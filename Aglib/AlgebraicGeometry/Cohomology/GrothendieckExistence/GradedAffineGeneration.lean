/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedGenerators
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineEvaluation

/-! # Original homogeneous generators on affine sections -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

local instance affineGeneratorCoefficient_isQuasicoherent (m : ℕ) :
    (F.obj.obj (op m)).IsQuasicoherent :=
  quasicoherent_of_affineCharts _ (fun R j _ => (F.property.coherent m R j).1)

/-- The original first-level generators span every graded piece on every
actual affine open. No finite-type or generation hypothesis is introduced. -/
theorem formalGradedPieceGenerator_affine_span (n : ℕ) (U : X.affineOpens) :
    Submodule.span Γ(X, U.val)
      {z : Γ(F.gradedPiece n, U.val) | ∃ a : ↥(I ^ n),
        ∃ y : Γ(F.obj.obj (op 1), U.val),
          z = (formalGradedPieceGenerator f I F n a).app U.val y} = ⊤ := by
  let S := idealSectionsFunctor X U.val
  let P := Submodule.span Γ(X, U.val)
    {z : Γ(F.gradedPiece n, U.val) | ∃ a : ↥(I ^ n),
      ∃ y : Γ(F.obj.obj (op 1), U.val),
        z = (formalGradedPieceGenerator f I F n a).app U.val y}
  let g := Sigma.desc (formalGradedPieceGenerator f I F n)
  let : (∐ fun _ : ↥(I ^ n) => F.obj.obj (op 1)).IsQuasicoherent :=
    quasicoherent_coproduct _
  let c := S.mapCocone
    (Cofan.mk _ (Sigma.ι (fun _ : ↥(I ^ n) => F.obj.obj (op 1))))
  have hc : IsColimit c := affineOpenSectionsIsColimit U
    (fun _ => affineGeneratorCoefficient_isQuasicoherent f I F 1)
    (coproductIsCoproduct (fun _ : ↥(I ^ n) => F.obj.obj (op 1)))
  have hz : S.map g ≫ ModuleCat.ofHom P.mkQ = 0 := by
    apply hc.hom_ext
    intro a
    ext x
    change P.mkQ ((S.map g) ((c.ι.app a) x)) = 0
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    apply Submodule.subset_span
    refine ⟨a.as, x, ?_⟩
    have h := congrArg S.map
      (Sigma.ι_comp_desc (formalGradedPieceGenerator f I F n) a.as)
    rw [S.map_comp] at h
    exact congrArg (fun k => k x) h
  apply top_unique
  intro x _
  let : (kernel g).IsQuasicoherent := quasicoherent_kernel g
  obtain ⟨y, rfl⟩ := affineOpenSections_epi_surjective U g x
  apply (Submodule.Quotient.mk_eq_zero P).mp
  exact congrArg (fun k => k y) hz

end AlgebraicGeometry.Scheme.Cohomology

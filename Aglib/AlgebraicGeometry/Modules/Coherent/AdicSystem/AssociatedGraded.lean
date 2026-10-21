/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Basic
public import Aglib.AlgebraicGeometry.Modules.Coherent.Subobjects
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# The original successive pieces of a coherent formal system

The degree-`n` piece is the actual kernel of the adjacent transition
`F_(n+1) → F_n` on the fixed scheme. These are coherent independently of any
algebraization. Their native coproduct has the original split component
inclusions and projections. This file constructs the underlying graded
coefficient only; the action and coherent geometric realization over the
associated-graded base are separate obligations.

These individual transition kernels are not the categorical kernels of
morphisms of formal systems, and no levelwise-kernel exactness is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  (F : AdicSystem X K)

/-- The actual degree-`n` transition kernel, including degree zero. -/
abbrev gradedPiece (n : ℕ) : X.Modules := kernel (F.transition n)

instance gradedPiece_isQuasicoherent (n : ℕ) : (F.gradedPiece n).IsQuasicoherent := by
  let : (F.obj.obj (op (n + 1))).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (F.property.coherent (n + 1) R j).1)
  let : (F.obj.obj (op n)).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (F.property.coherent n R j).1)
  exact quasicoherent_kernel (F.transition n)

/-- Every successive piece is coherent without an algebraization hypothesis. -/
theorem gradedPiece_coherent (n : ℕ) : affineLocallyFiniteType X (F.gradedPiece n) :=
  affineLocallyFiniteType_of_quasicoherent_mono (kernel.ι (F.transition n))
    (F.property.coherent (n + 1))

/-- The degree-zero piece is canonically the original first formal coefficient. -/
def gradedPieceZeroIso : F.gradedPiece 0 ≅ F.obj.obj (op 1) :=
  kernelIsoOfEq (F.zero_isZero.eq_of_tgt (F.transition 0) 0) ≪≫ kernelZeroIsoSource

/-- The degree-zero comparison is the original kernel inclusion. -/
@[simp]
theorem gradedPieceZeroIso_hom : (F.gradedPieceZeroIso).hom = kernel.ι (F.transition 0) := by
  simp [gradedPieceZeroIso, kernelZeroIsoSource_hom]

/-- A formal-system map induces the original map of adjacent transition kernels. -/
def gradedPieceMap {G : AdicSystem X K} (φ : F ⟶ G) (n : ℕ) :
    F.gradedPiece n ⟶ G.gradedPiece n :=
  kernel.map (F.transition n) (G.transition n)
    (φ.hom.app (op (n + 1))) (φ.hom.app (op n)) (F.transition_naturality φ n)

/-- The component map retains the original coefficient map after inclusion. -/
@[reassoc (attr := simp)]
theorem gradedPieceMap_ι {G : AdicSystem X K} (φ : F ⟶ G) (n : ℕ) :
    F.gradedPieceMap φ n ≫ kernel.ι (G.transition n) =
      kernel.ι (F.transition n) ≫ φ.hom.app (op (n + 1)) := by
  simp [gradedPieceMap]

/-- The underlying graded coefficient is the native coproduct of all successive pieces. -/
abbrev gradedUnderlying : X.Modules := ∐ F.gradedPiece

/-- The native inclusion of one original successive piece. -/
abbrev gradedι (n : ℕ) : F.gradedPiece n ⟶ F.gradedUnderlying := Sigma.ι F.gradedPiece n

/-- The component projection is the canonical projection associated to the native coproduct. -/
def gradedπ (n : ℕ) : F.gradedUnderlying ⟶ F.gradedPiece n :=
  (Bicone.ofColimitCocone (colimit.isColimit (Discrete.functor F.gradedPiece))).π n

/-- Every successive piece is a retract of the underlying graded coefficient. -/
@[reassoc (attr := simp)]
theorem gradedι_gradedπ (n : ℕ) : F.gradedι n ≫ F.gradedπ n = 𝟙 (F.gradedPiece n) := by
  exact bicone_ι_π_self (Bicone.ofColimitCocone
    (colimit.isColimit (Discrete.functor F.gradedPiece))) n

/-- Different original graded pieces have zero mixed inclusion/projection. -/
@[reassoc (attr := simp)]
theorem gradedι_gradedπ_of_ne {m n : ℕ} (h : m ≠ n) :
    F.gradedι m ≫ F.gradedπ n = 0 := by
  exact bicone_ι_π_ne (Bicone.ofColimitCocone
    (colimit.isColimit (Discrete.functor F.gradedPiece))) h

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

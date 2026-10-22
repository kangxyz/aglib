/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.IndependentQuotientDefects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedDefects
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientSystem

/-! # Uniform bounds on the original independently reduced formal maps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {I : X.IdealSheafData} {F G : AdicSystem X I}

/-- An independent quotient doubles one uniform bound, independently of both
formal indices. The quotiented system retains its original stage maps. -/
theorem DefectsKilled.quotient {J : X.IdealSheafData} {t : ℕ} {φ : F ⟶ G}
    (h : DefectsKilled J t φ) (K : X.IdealSheafData) :
    DefectsKilled J (t * 2) ((quotientFunctor X I K).map φ) := by
  intro n
  let : (F.obj.obj (op n)).IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _
      (fun R j _ => (F.property.coherent n R j).1)
  let : (G.obj.obj (op n)).IsQuasicoherent :=
    QuasiCoherent.quasicoherent_of_affineCharts _
      (fun R j _ => (G.property.coherent n R j).1)
  exact independentQuotient_defectsKilled (φ.hom.app (op n)) J K t (h n).1 (h n).2

/-- A square of actual formal maps with isomorphic endpoints transports each
ordinary kernel and cokernel bound without changing the exponent. -/
theorem DefectsKilled.of_iso_square {F' G' : AdicSystem X I}
    {J : X.IdealSheafData} {t : ℕ} {φ : F ⟶ G} {ψ : F' ⟶ G'}
    (h : DefectsKilled J t ψ) (e : F ≅ F') (d : G ≅ G')
    (hs : φ ≫ d.hom = e.hom ≫ ψ) : DefectsKilled J t φ := by
  let T := adicSystemToDiagram X I
  intro n
  let en := (T.mapIso e).app (op n)
  let dn := (T.mapIso d).app (op n)
  have hn : φ.hom.app (op n) ≫ dn.hom = en.hom ≫ ψ.hom.app (op n) :=
    congrArg (fun z : F ⟶ G' => z.hom.app (op n)) hs
  exact ⟨killedByIdealSheaf_of_iso _ (kernel.mapIso _ _ en dn hn).symm (h n).1,
    killedByIdealSheaf_of_iso _ (cokernel.mapIso _ _ en dn hn).symm (h n).2⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

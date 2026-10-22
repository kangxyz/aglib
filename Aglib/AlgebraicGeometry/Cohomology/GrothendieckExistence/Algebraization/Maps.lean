/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.Operations

/-! # Lifting algebra maps with the whole original-stage certificate

A compatible formal algebra map lifts by coherent fullness. Unit and
multiplication preservation are detected only on the coherent unit and source
tensor square. The resulting native algebra map retains every original stage.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {J : Type u₂} [Category.{v₂} J]
  {A B : CommMon C} {F G : J ⥤ C}
  [hF : ∀ j, MonObj (F.obj j)] [hG : ∀ j, MonObj (G.obj j)]
  (qA : (Functor.const J).obj A.X ⟶ F)
  (qB : (Functor.const J).obj B.X ⟶ G)
  [hqA : ∀ j, IsMonHom (show A.X ⟶ F.obj j from qA.app j)]
  [hqB : ∀ j, IsMonHom (show B.X ⟶ G.obj j from qB.app j)]
  (phi : F ⟶ G) [hphi : ∀ j, IsMonHom (phi.app j)]

/-- Native algebra-map lifting, including the complete diagram equation. -/
def algebraMapOfLiftedFamily
    (p : { f : A.X ⟶ B.X //
      (Functor.const J).map f ≫ qB = qA ≫ phi })
    (hUnit : JointlyDetects (fun j => qB.app j) (𝟙_ C))
    (hTensor : JointlyDetects (fun j => qB.app j) (A.X ⊗ A.X)) :
    { f : A ⟶ B // (Functor.const J).map f.hom.hom ≫ qB = qA ≫ phi } := by
  let hComp : ∀ j, IsMonHom (p.val ≫ qB.app j) := fun j => by
    have hp : p.val ≫ qB.app j = qA.app j ≫ phi.app j :=
      NatTrans.congr_app p.property j
    rw [hp]
    infer_instance
  let hMap : IsMonHom p.val :=
    isMonHom_of_jointDetection (M := B.X) (N := A.X) (fun j => qB.app j) p.val hUnit hTensor
  exact ⟨CommMon.homMk (Mon.Hom.mk p.val (isMonHom_hom := hMap)), p.property⟩

omit hF hG hqA hqB hphi in
/-- The original family determines the lifted native algebra map uniquely. -/
theorem algebraMapOfLiftedFamily_unique
    (h : JointlyDetects (fun j => qB.app j) A.X)
    (a b : A ⟶ B)
    (ha : (Functor.const J).map a.hom.hom ≫ qB = qA ≫ phi)
    (hb : (Functor.const J).map b.hom.hom ≫ qB = qA ≫ phi) : a = b := by
  apply CommMon.hom_ext
  exact h _ _ fun j => NatTrans.congr_app (ha.trans hb.symm) j

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  (h : (completionFunctor X K).FullyFaithful)
  {F G : AdicSystem X K} [AdicAlgebraStructure F] [AdicAlgebraStructure G]
  (d : AdicAlgebraizationData F) (e : AdicAlgebraizationData G)
  (phi : F ⟶ G) [hPhi : ∀ n, IsMonHom (phi.hom.app n)]

/-- Lift a formal algebra map to the actual coherent native algebras and
retain all its original quotient-map equations simultaneously. -/
def algebraizationMapData :
    { f : d.algebra ⟶ e.algebra //
      (Functor.const ℕᵒᵖ).map f.hom.hom ≫ e.quotientMaps =
        d.quotientMaps ≫ phi.hom } := by
  let U : X.CoherentSheaf := ⟨𝟙_ X.Modules, Support.unit_coherent X⟩
  let T : X.CoherentSheaf := ⟨d.coherent.obj ⊗ d.coherent.obj,
    QuasiCoherent.affineLocallyFiniteType_tensor _ _ d.coherent.property d.coherent.property⟩
  let p := originalCompletionLiftData K h e.beta d.coherent (d.quotientMaps ≫ phi.hom)
  exact algebraMapOfLiftedFamily d.quotientMaps e.quotientMaps phi.hom
    ⟨p.val.hom, p.property⟩
    (originalCompletionMaps_jointlyDetects K h e.beta U)
    (originalCompletionMaps_jointlyDetects K h e.beta T)

include h in
omit hPhi in
/-- The lifted map is uniquely determined by the full original quotient family. -/
theorem algebraizationMap_unique (a b : d.algebra ⟶ e.algebra)
    (ha : (Functor.const ℕᵒᵖ).map a.hom.hom ≫ e.quotientMaps =
      d.quotientMaps ≫ phi.hom)
    (hb : (Functor.const ℕᵒᵖ).map b.hom.hom ≫ e.quotientMaps =
      d.quotientMaps ≫ phi.hom) : a = b :=
  algebraMapOfLiftedFamily_unique d.quotientMaps e.quotientMaps phi.hom
    (originalCompletionMaps_jointlyDetects K h e.beta d.coherent) a b ha hb

end AlgebraicGeometry.Scheme.Modules.Coherent

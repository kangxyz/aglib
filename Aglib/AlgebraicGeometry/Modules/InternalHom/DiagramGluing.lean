/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.OpenCoverExt

/-! # Gluing original module-valued diagram morphisms

The original stage morphisms glue through the native Hom sheaf. Their original
transition equations are local, so the glued stages form an actual natural
transformation. No exactness or quasicoherence of an ambient target is used.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.InternalHom
universe u v w w'
variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
  (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
  (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
  {C : Type w} [Category.{w'} C] (F G : C ⥤ X.Modules)
  (q : ∀ i, F ⋙ restrictFunctor (a i) ⟶ G ⋙ restrictFunctor (a i))
  (hq : ∀ c, RestrictionHomCompatible a (F.obj c) (G.obj c)
    (fun i => (q i).app c))

/-- Glue an entire family of original diagram morphisms, retaining all transitions. -/
def glueRestrictionDiagramHom : F ⟶ G where
  app c := glueRestrictionHom Y a hcover (F.obj c) (G.obj c)
    (fun i => (q i).app c) (hq c)
  naturality c d t := by
    apply hom_ext_of_openCover Y a hcover
    intro i
    rw [Functor.map_comp, Functor.map_comp,
      glueRestrictionHom_restrict, glueRestrictionHom_restrict]
    exact (q i).naturality t

/-- Every glued stage restricts to the original local stage. -/
theorem glueRestrictionDiagramHom_restrict (i : ι) :
    Functor.whiskerRight (glueRestrictionDiagramHom Y a hcover F G q hq)
      (restrictFunctor (a i)) = q i := by
  apply NatTrans.ext
  funext c
  exact glueRestrictionHom_restrict Y a hcover (F.obj c) (G.obj c)
    (fun i => (q i).app c) (hq c) i

/-- The original local diagram maps determine the original global map uniquely. -/
theorem glueRestrictionDiagramHom_unique (r : F ⟶ G)
    (hr : ∀ i, Functor.whiskerRight r (restrictFunctor (a i)) = q i) :
    r = glueRestrictionDiagramHom Y a hcover F G q hq := by
  apply NatTrans.ext
  funext c
  apply glueRestrictionHom_unique Y a hcover (F.obj c) (G.obj c)
    (fun i => (q i).app c) (hq c)
  intro i
  exact congrArg (fun η => η.app c) (hr i)

/-- A comparison equation into any ambient diagram glues from the actual
restricted equations; its individual stages need not be monomorphisms. -/
theorem glueRestrictionDiagramHom_comp
    (T : C ⥤ X.Modules) (ψ : G ⟶ T) (γ : F ⟶ T)
    (heq : ∀ i, q i ≫ Functor.whiskerRight ψ (restrictFunctor (a i)) =
      Functor.whiskerRight γ (restrictFunctor (a i))) :
    glueRestrictionDiagramHom Y a hcover F G q hq ≫ ψ = γ := by
  apply NatTrans.ext
  funext c
  apply hom_ext_of_openCover Y a hcover
  intro i
  change (restrictFunctor (a i)).map
    ((glueRestrictionDiagramHom Y a hcover F G q hq).app c ≫ ψ.app c) = _
  rw [Functor.map_comp]
  have hr := congrArg (fun η => η.app c)
    (glueRestrictionDiagramHom_restrict Y a hcover F G q hq i)
  change (restrictFunctor (a i)).map
    ((glueRestrictionDiagramHom Y a hcover F G q hq).app c) = (q i).app c at hr
  rw [hr]
  exact congrArg (fun η => η.app c) (heq i)

end AlgebraicGeometry.Scheme.Modules.InternalHom

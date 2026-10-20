/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.TwistPresentation.Epimorphism
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Stalk
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback

/-!
# Finite negative-twist presentations on closed projective subschemes

The actual closed pushforward is presented on native polynomial projective space.
Geometric pullback, its finite-coproduct comparison and the original closed-immersion
counit then give the epimorphism on the original scheme. The source consists of finitely
many copies of one actual pulled-back negative twist and is finite locally free.

The affine-locally finite-type version works over any commutative base ring.
The coherent-object corollary derives local Noetherianity from the closed embedding
over the given Noetherian affine base. No regularity condition is used.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts
universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Projective

variable (R : Type u) [CommRing R] (ι : Type u)
  {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace R ι)

/-- A finite sum of the same actual pulled-back twist is finite locally free. -/
theorem twistCoproduct_isFiniteLocallyFree (I : Type u) [Finite I] (d : ℤ) :
    IsFiniteLocallyFree X
      (∐ fun _ : I => (pullback i).obj (ProjectiveSpace.twistingSheaf R ι d)) := by
  let F : I → X.Modules :=
    fun _ => (pullback i).obj (ProjectiveSpace.twistingSheaf R ι d)
  let : IsFiniteLocallyFree X (∏ᶜ F) :=
    (finiteLocallyFree X).prop_product (fun _ => inferInstance)
  exact finiteLocallyFree_of_iso
    ((biproduct.isoProduct F).symm ≪≫ biproduct.isoCoproduct F)

/-- The actual quotient map is the original pulled-back map followed by the original
counit, with the canonical finite-coproduct comparison on its source. -/
def twistCoproductMap {I : Type u} [Finite I] (d : ℤ) (M : X.Modules)
    (φ : (∐ fun _ : I => ProjectiveSpace.twistingSheaf R ι d) ⟶
      (pushforward i).obj M) :
    (∐ fun _ : I => (pullback i).obj (ProjectiveSpace.twistingSheaf R ι d)) ⟶ M :=
  (PreservesCoproduct.iso (pullback i)
    (fun _ : I => ProjectiveSpace.twistingSheaf R ι d)).inv ≫
      (pullback i).map φ ≫ (pullbackPushforwardAdjunction i).counit.app M

/-- Closed-immersion pullback of an actual presentation is an epimorphism.
The counit is a proved isomorphism on every module sheaf. -/
theorem twistCoproductMap_epi [IsClosedImmersion i] {I : Type u} [Finite I]
    (d : ℤ) (M : X.Modules)
    (φ : (∐ fun _ : I => ProjectiveSpace.twistingSheaf R ι d) ⟶
      (pushforward i).obj M) [Epi φ] : Epi (twistCoproductMap R ι i d M φ) := by
  let := pullbackPushforwardCounit_isIso_of_closedImmersion i M
  dsimp only [twistCoproductMap]
  infer_instance

/-- Every finite-type quasicoherent module on the original closed projective subscheme
is an actual quotient of a finite sum of one common strictly negative twist. Its
positive degree can exceed any prescribed bound, and its source is finite locally free. -/
theorem exists_uniformNegativeTwistEpimorphism [Finite ι] [IsClosedImmersion i]
    (M : X.Modules) (hM : affineLocallyFiniteType X M) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ ∃ (I : Type u) (_ : Finite I)
      (π : (∐ fun _ : I =>
        (pullback i).obj (ProjectiveSpace.twistingSheaf R ι (-(N : ℤ)))) ⟶ M),
      Epi π ∧ IsFiniteLocallyFree X
        (∐ fun _ : I => (pullback i).obj (ProjectiveSpace.twistingSheaf R ι (-(N : ℤ)))) := by
  have hpush : affineLocallyFiniteType (ProjectiveSpace R ι) ((pushforward i).obj M) :=
    Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward i hM
  obtain ⟨N, hN, I, hI, φ, hφ, _⟩ :=
    ProjectiveSpace.exists_uniformNegativeTwistEpimorphism R ι ((pushforward i).obj M)
      hpush (B + 1)
  let := hI
  let := hφ
  refine ⟨N, (Nat.lt_succ_self B).trans_le hN, I, hI,
    twistCoproductMap R ι i (-(N : ℤ)) M φ, ?_, ?_⟩
  · exact twistCoproductMap_epi R ι i _ M φ
  · exact twistCoproduct_isFiniteLocallyFree R ι i I (-(N : ℤ))

/-- The requested coherent-object presentation over a Noetherian affine base.
The actual closed embedding supplies local Noetherianity of the original scheme. -/
theorem exists_coherent_uniformNegativeTwistEpimorphism
    [IsNoetherianRing R] [Finite ι] [IsClosedImmersion i] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
    ∀ (M : Scheme.CoherentSheaf X) (B : ℕ),
      ∃ N : ℕ, B < N ∧ ∃ (I : Type u) (_ : Finite I)
        (π : (∐ fun _ : I =>
          (pullback i).obj (ProjectiveSpace.twistingSheaf R ι (-(N : ℤ)))) ⟶ M.obj),
        Epi π ∧ IsFiniteLocallyFree X
          (∐ fun _ : I => (pullback i).obj (ProjectiveSpace.twistingSheaf R ι (-(N : ℤ)))) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
  intro M B
  exact exists_uniformNegativeTwistEpimorphism R ι i M.obj M.property B

end AlgebraicGeometry.Scheme.Modules.Coherent.Projective

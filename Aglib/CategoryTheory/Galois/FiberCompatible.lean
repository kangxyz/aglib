/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.GaloisObjects

/-! # Galois objects under functors compatible with their actual fibres

The fibre comparison transports the original regular deck action without any
connectedness assumption on the image. Connectedness of the image is needed
only for its Galoisness and the deck-group equivalence. Full faithfulness of the
functor is not assumed.
-/

@[expose] public noncomputable section

namespace CategoryTheory.PreGaloisCategory

universe c h d j v

variable {C : Type c} [Category.{h} C] [GaloisCategory C]
  {D : Type d} [Category.{j} D] [GaloisCategory D]
  (F : C ⥤ FintypeCat.{v}) [FiberFunctor F]
  (G : D ⥤ FintypeCat.{v}) [FiberFunctor G]
  (T : C ⥤ D) (e : F ≅ T ⋙ G)

/-- The actual comparison of the finite fibres, without a new action model. -/
def compatibleFiberEquiv (Y : C) : F.obj Y ≃ G.obj (T.obj Y) :=
  FintypeCat.equivEquivIso.symm (e.app Y)

omit [GaloisCategory C] [GaloisCategory D] [FiberFunctor F] [FiberFunctor G] in
/-- Evaluation of the original mapped deck transformation is the literal
naturality equation for the given fibre comparison. -/
theorem compatibleFiberEquiv_mapAut (Y : C) (σ : Aut Y) (y : F.obj Y) :
    compatibleFiberEquiv F G T e Y (F.map σ.hom y) =
      G.map (Functor.mapAut Y T σ).hom (compatibleFiberEquiv F G T e Y y) := by
  exact congrArg (fun f => f y) (e.hom.naturality σ.hom)

omit [GaloisCategory D] [FiberFunctor G] in
include F e in
/-- The unchanged mapped deck action is regular on every target fibre point.
The target object need not be connected; only the source is assumed Galois. -/
theorem mappedOrbit_bijective_of_fiberCompatible (Y : C) [IsGalois Y]
    (y : G.obj (T.obj Y)) :
    Function.Bijective (fun σ : Aut Y => G.map (Functor.mapAut Y T σ).hom y) := by
  let ε := compatibleFiberEquiv F G T e Y
  have h : (fun σ : Aut Y => G.map (Functor.mapAut Y T σ).hom y) =
      fun σ => ε (F.map σ.hom (ε.symm y)) := by
    funext σ
    exact (congrArg (fun t => G.map (Functor.mapAut Y T σ).hom t)
      (ε.apply_symm_apply y)).symm.trans
        (compatibleFiberEquiv_mapAut F G T e Y σ (ε.symm y)).symm
  rw [h]
  exact ε.bijective.comp (evaluation_aut_bijective_of_isGalois F Y (ε.symm y))

variable (Y : C) [IsGalois Y] [IsConnected (T.obj Y)]

include e in
/-- The image of a Galois object is Galois whenever it is connected: the
original deck transformations already act transitively on the target fibre. -/
theorem isGalois_obj_of_fiberCompatible : IsGalois (T.obj Y) := by
  apply (isGalois_iff_pretransitive G (T.obj Y)).mpr
  constructor
  intro x y
  obtain ⟨σ, hσ⟩ := (mappedOrbit_bijective_of_fiberCompatible F G T e Y x).surjective y
  exact ⟨Functor.mapAut Y T σ, hσ⟩

include e in
/-- The actual functor map on deck groups is bijective. This follows from
pointwise evaluation and connectedness, not from assumed full faithfulness. -/
theorem mapAut_bijective_of_fiberCompatible :
    Function.Bijective (Functor.mapAut Y T) := by
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected F Y
  let z := compatibleFiberEquiv F G T e Y y
  have h := mappedOrbit_bijective_of_fiberCompatible F G T e Y z
  refine ⟨?_, ?_⟩
  · intro σ τ hστ
    exact h.injective (congrArg (fun a : Aut (T.obj Y) => G.map a.hom z) hστ)
  · intro τ
    obtain ⟨σ, hσ⟩ := h.surjective (G.map τ.hom z)
    exact ⟨σ, evaluation_aut_injective_of_isConnected G (T.obj Y) z hσ⟩

/-- The original functor map, as a multiplicative equivalence of deck groups. -/
def mapAutEquivOfFiberCompatible : Aut Y ≃* Aut (T.obj Y) :=
  MulEquiv.ofBijective (Functor.mapAut Y T)
    (mapAut_bijective_of_fiberCompatible F G T e Y)

include e in
/-- Compatible fibres and connected image preserve the actual deck-group order. -/
theorem card_aut_obj_of_fiberCompatible : Nat.card (Aut (T.obj Y)) = Nat.card (Aut Y) :=
  (Nat.card_congr (mapAutEquivOfFiberCompatible F G T e Y).toEquiv).symm

end CategoryTheory.PreGaloisCategory

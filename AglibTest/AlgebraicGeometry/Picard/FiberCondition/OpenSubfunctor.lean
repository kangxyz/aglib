/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.FiberCondition.OpenSubfunctor

/-! Focused consumer of the open-subsheaf lemma for `Pic_{X/S,(fppf)}` (Kleiman, *The Picard
scheme*, arXiv:math/0504020v1, proof of Thm 4.8, pp. 28–29, with fppf in place of étale): on
locally Noetherian test schemes the subsheaf `Pic^C` of a fiber condition is an open subfunctor in
the sense consumed by `Scheme.LocalRepresentability`, and the open `U_ξ` represents
`Pic^C ×_{Pic} h_T`. The condition that always holds cuts out all of `Pic_{X/S,(fppf)}`. -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.RelativePicard Scheme.LocalRepresentability

universe u

variable {S X : Scheme.{u}} {p : X ⟶ S} (C : FiberCondition p)

example {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    IsOpen {t : T.left | C.HoldsAt ξ t} :=
  C.isOpen_setOf_holdsAt ξ

example {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T))
    {Z : Over S} (g : Z ⟶ T) :
    (fppfPicardSheaf p).obj.map g.op ξ ∈ C.subfunctor.obj (op Z) ↔
      g.left ⁻¹ᵁ C.opens ξ = ⊤ :=
  C.map_mem_subfunctor_iff ξ g

example {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    ξ ∈ C.subfunctor.obj (op T) ↔ C.opens ξ = ⊤ :=
  C.mem_subfunctor_iff_opens_eq_top ξ

example
    (hC : ∀ T : Over S, IsLocallyNoetherian T.left →
      ∀ a : (familyPicardFunctor p).obj (op T), IsClosed {t : T.left | C.Holds T a t})
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    IsClopen {t : T.left | C.HoldsAt ξ t} :=
  C.isClopen_setOf_holdsAt_of_isClosed hC ξ

example (D : FiberCondition p) {T : Over S} [IsLocallyNoetherian T.left]
    (ξ : (fppfPicardSheaf p).obj.obj (op T)) : (C ⊓ D).opens ξ = C.opens ξ ⊓ D.opens ξ :=
  C.opens_inf D ξ

/-- The consumer form: an open subfunctor on locally Noetherian test schemes. -/
example : IsOpenSubfunctor C.locallyNoetherianSubfunctor :=
  C.isOpenSubfunctor

/-- `Pic^C ×_{Pic} h_T` is representable, by the open subscheme `U_ξ`. -/
example {T : Scheme.LocallyNoetherianOver S} (ξ : (fppfPicardSheaf p).obj.obj (op T.obj)) :
    (C.preimageSubfunctor ξ).toFunctor.IsRepresentable :=
  (C.preimageRepresentableBy ξ).isRepresentable

example {T : Scheme.LocallyNoetherianOver S} (ξ : (fppfPicardSheaf p).obj.obj (op T.obj))
    {Z : Scheme.LocallyNoetherianOver S} (k : Z ⟶ restrictOpens T (C.opens ξ)) :
    ((C.preimageRepresentableBy ξ).homEquiv k).1 = k ≫ restrictOpensι T (C.opens ξ) :=
  C.preimageRepresentableBy_homEquiv_coe ξ k

/-- The condition that always holds cuts out all of `Pic_{X/S,(fppf)}`, on every `S`-scheme. -/
example {T : Over S} (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    ξ ∈ (⟨fun _ _ _ ↦ True, fun _ _ _ ↦ Iff.rfl, fun _ _ _ ↦ isOpen_univ⟩ :
      FiberCondition p).subfunctor.obj (op T) := by
  rw [FiberCondition.mem_subfunctor_iff]
  intro t
  obtain ⟨V, h, a, -, -, ⟨v, rfl⟩, ha⟩ := FiberCondition.exists_flat_app_eq ξ t
  exact ⟨_, _, v, a, rfl, ha, trivial⟩

/-- Families of conditions: monotonicity, disjointness and covering of the opens. -/
example {D : FiberCondition p}
    (hCD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
      C.Holds T a t → D.Holds T a t)
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    C.opens ξ ≤ D.opens ξ :=
  C.opens_mono hCD ξ

example {D : FiberCondition p}
    (hCD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
      C.Holds T a t → ¬ D.Holds T a t)
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    Disjoint (C.opens ξ) (D.opens ξ) :=
  C.disjoint_opens hCD ξ

example {ι : Type*} (D : ι → FiberCondition p)
    (hD : ∀ (T : Over S) (a : (familyPicardFunctor p).obj (op T)) (t : T.left),
      ∃ i, (D i).Holds T a t)
    {T : Over S} [IsLocallyNoetherian T.left] (ξ : (fppfPicardSheaf p).obj.obj (op T)) :
    ⨆ i, (D i).opens ξ = ⊤ :=
  FiberCondition.iSup_opens_eq_top D hD ξ

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.isOpenSubfunctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FiberCondition.isOpenSubfunctor

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.preimageRepresentableBy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FiberCondition.preimageRepresentableBy

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.FiberCondition.isClopen_setOf_holdsAt_of_isClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FiberCondition.isClopen_setOf_holdsAt_of_isClosed

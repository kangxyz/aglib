/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ModelBaseFactor
public import Aglib.AlgebraicGeometry.Morphisms.Finite.SurjectiveBaseChange
public import Aglib.AlgebraicGeometry.FunctionField.Map

/-! # The original modeled arrow over the generic residue field

An actual field model map supplies finiteness and surjectivity of the same
arrow over the actual generic residue-field fibre. The field factorization,
cartesian comparisons and descent are constructed internally.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FinitePresentationDescent.Model.Map

universe u

/-- The original dominant field point factors through the actual generic residue field. -/
def genericFactor {S : Scheme.{u}} [IsIntegral S] {L : Type u} [Field L]
    (π : Spec (.of L) ⟶ S) [IsDominant π] :
    {φ : S.residueField (genericPoint S) ⟶ .of L //
      Spec.map φ ≫ S.fromSpecResidueField (genericPoint S) = π} := by
  apply Classical.choice
  obtain ⟨⟨y, φ⟩, hφ⟩ := (Scheme.SpecToEquivOfField _ _).symm.surjective π
  have hfac : Spec.map φ ≫ S.fromSpecResidueField y = π := by
    simpa only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] using hφ
  have hy : y = genericPoint S := by
    let z := Nonempty.some (inferInstance : Nonempty (Spec (.of L)))
    have hpoint := congrArg (fun q : Spec (.of L) ⟶ S => q z) hfac
    have hpoint' : y = π z := by
      simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using hpoint
    apply hpoint'.trans
    rw [Subsingleton.elim z (genericPoint (Spec (.of L)))]
    exact Scheme.map_genericPoint_of_isDominant _ π
  subst y
  exact ⟨⟨φ, hfac⟩⟩

variable {S Z W : Scheme.{u}} [IsIntegral S] {L : Type u} [Field L]
    (π : Spec (.of L) ⟶ S) [IsDominant π]
    {t : Z ⟶ Spec (.of L)} {s : W ⟶ Spec (.of L)}

/-- Factor the same original model using the single field factorization. -/
def genericModel (M : Model π t) :
    Model (Spec.map (genericFactor π).val) t :=
  M.factorBase (Spec.map (genericFactor π).val)
    (S.fromSpecResidueField (genericPoint S)) (genericFactor π).property

/-- The original field-to-generic-fibre comparison is surjective. This
interface also applies simultaneously to every branch of a joint cover. -/
theorem genericModel_comparison_surjective (M : Model π t) :
    Surjective (genericModel π M).p := by
  let : Surjective (Spec.map (genericFactor π).val) :=
    ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ x⟩⟩
  exact MorphismProperty.of_isPullback (genericModel π M).square.flip
    (inferInstance : Surjective (Spec.map (genericFactor π).val))

/-- The unchanged original map on the models after the same factorization. -/
def genericMap {M : Model π t} {N : Model π s}
    {m : Over.mk t ⟶ Over.mk s} (a : Map M N m) :
    Map (genericModel π M) (genericModel π N) m :=
  a.factorBase (Spec.map (genericFactor π).val)
    (S.fromSpecResidueField (genericPoint S)) (genericFactor π).property

/-- The generic modeled arrow is the actual pullback of the original stage
arrow. Both projections and the stage arrow remain unchanged. -/
theorem genericMap_isPullback {M : Model π t} {N : Model π s}
    {m : Over.mk t ⟶ Over.mk s} (a : Map M N m) :
    IsPullback (pullback.fst M.f (S.fromSpecResidueField (genericPoint S)))
      (genericMap π a).hom.left a.hom.left (N.f.fiberι (genericPoint S)) := by
  let b := S.fromSpecResidueField (genericPoint S)
  have ha : a.hom.left ≫ N.f = M.f := Over.w a.hom
  have hcomm : pullback.fst M.f b ≫ a.hom.left =
      (genericMap π a).hom.left ≫ pullback.fst N.f b := by
    simp only [b, genericMap, Model.Map.factorBase, Over.pullback_map_left]
    exact (pullback.lift_fst _ _ _).symm
  have Hwhole : IsPullback (pullback.fst M.f b)
      ((genericMap π a).hom.left ≫ (genericModel π N).f)
      (a.hom.left ≫ N.f) b := by
    change IsPullback (pullback.fst M.f b)
      (((Over.pullback b).map a.hom).left ≫ pullback.snd N.f b)
      (a.hom.left ≫ N.f) b
    have hη := Over.w ((Over.pullback b).map a.hom)
    change ((Over.pullback b).map a.hom).left ≫ pullback.snd N.f b =
      pullback.snd M.f b at hη
    rw [hη, ha]
    exact IsPullback.of_hasPullback M.f b
  exact Hwhole.of_bot hcomm (IsPullback.of_hasPullback N.f b)

/-- An original finite field arrow makes the corresponding generic-fibre
arrow finite. Surjectivity of that branch is not required. -/
theorem finite_genericFibre
    (M : Model π t) (N : Model π s)
    {m : Over.mk t ⟶ Over.mk s} (a : Map M N m)
    [IsProper M.f] [IsSeparated N.f] [IsFinite m.left] :
    IsFinite (pullback.snd a.hom.left (N.f.fiberι (genericPoint S))) := by
  let H := genericMap_isPullback π a
  have ha : a.hom.left ≫ N.f = M.f := Over.w a.hom
  let : IsProper (a.hom.left ≫ N.f) := by rw [ha]; infer_instance
  let : IsProper a.hom.left := IsProper.of_comp a.hom.left N.f
  let : IsProper (genericMap π a).hom.left :=
    MorphismProperty.of_isPullback H (inferInstance : IsProper a.hom.left)
  let : Surjective (genericModel π N).p := genericModel_comparison_surjective π N
  have hfinite : IsFinite (genericMap π a).hom.left :=
    Scheme.isFinite_of_isProper_of_isPullback (genericMap π a).isPullback.flip
  have he : H.isoPullback.inv ≫ (genericMap π a).hom.left =
      pullback.snd a.hom.left (N.f.fiberι (genericPoint S)) := H.isoPullback_inv_snd
  have hE : IsFinite H.isoPullback.inv := inferInstance
  rw [← he]
  exact MorphismProperty.comp_mem (@IsFinite : MorphismProperty Scheme.{u})
    H.isoPullback.inv (genericMap π a).hom.left hE hfinite

/-- An original surjective field arrow makes the corresponding generic-fibre
arrow surjective, without properness or finiteness assumptions. -/
theorem surjective_genericFibre
    (M : Model π t) (N : Model π s)
    {m : Over.mk t ⟶ Over.mk s} (a : Map M N m) [Surjective m.left] :
    Surjective (pullback.snd a.hom.left (N.f.fiberι (genericPoint S))) := by
  let H := genericMap_isPullback π a
  let : Surjective (genericModel π N).p := genericModel_comparison_surjective π N
  have hsurj : Surjective (genericMap π a).hom.left := by
    constructor
    intro x
    obtain ⟨w, hw⟩ := (genericModel π N).p.surjective x
    obtain ⟨z, hz⟩ := m.left.surjective w
    refine ⟨(genericModel π M).p z, ?_⟩
    have he := congrArg (fun q => q z) (genericMap π a).comm
    simpa only [Scheme.Hom.comp_apply, hz, hw] using he
  have he : H.isoPullback.inv ≫ (genericMap π a).hom.left =
      pullback.snd a.hom.left (N.f.fiberι (genericPoint S)) := H.isoPullback_inv_snd
  let : Surjective (genericMap π a).hom.left := hsurj
  rw [← he]
  exact ⟨(genericMap π a).hom.left.surjective.comp H.isoPullback.inv.surjective⟩

/-- Joint surjectivity of the original field family supplies joint
surjectivity of the original generic-fibre coproduct map. No individual
branch is assumed surjective and no total-cover model is introduced. -/
theorem surjective_genericFibre_sigma
    {I : Type u} {C : I → Scheme.{u}} {q : ∀ i, C i ⟶ Spec (.of L)}
    (N : Model π s) (M : ∀ i, Model π (q i))
    {m : ∀ i, Over.mk (q i) ⟶ Over.mk s}
    (a : ∀ i, Map (M i) N (m i))
    [Surjective (Sigma.desc fun i => (m i).left)] :
    Surjective (pullback.snd (Sigma.desc fun i => (a i).hom.left)
      (N.f.fiberι (genericPoint S))) := by
  constructor
  intro x
  let : Surjective (genericModel π N).p := genericModel_comparison_surjective π N
  obtain ⟨w, hw⟩ := (genericModel π N).p.surjective x
  obtain ⟨v, hv⟩ := (Sigma.desc fun i => (m i).left).surjective w
  obtain ⟨⟨i, z⟩, hz⟩ := (AlgebraicGeometry.sigmaMk C).surjective v
  have hfield : (m i).left z = w := by
    have hdesc := congrArg (fun f : C i ⟶ W => f z)
      (Sigma.ι_comp_desc (fun j => (m j).left) i)
    calc
      (m i).left z = (Sigma.desc fun j => (m j).left) (Sigma.ι C i z) := hdesc.symm
      _ = (Sigma.desc fun j => (m j).left) v := by
        rw [← AlgebraicGeometry.sigmaMk_mk, hz]
      _ = w := hv
  have hproj : (genericModel π N).p ≫ N.f.fiberι (genericPoint S) = N.p := by
    change _ ≫ pullback.fst N.f (S.fromSpecResidueField (genericPoint S)) = _
    dsimp only [genericModel, Model.factorBase]
    exact (IsPullback.of_hasPullback N.f
      (S.fromSpecResidueField (genericPoint S))).lift_fst _ _ _
  have htarget : N.p w = N.f.fiberι (genericPoint S) x := by
    have h := congrArg (fun f : W ⟶ N.X => f w) hproj
    change N.f.fiberι (genericPoint S) ((genericModel π N).p w) = N.p w at h
    rw [hw] at h
    exact h.symm
  let y := Sigma.ι (fun j => (M j).X) i ((M i).p z)
  have hy : (Sigma.desc fun j => (a j).hom.left) y =
      N.f.fiberι (genericPoint S) x := by
    have hdesc := congrArg (fun f : (M i).X ⟶ N.X => f ((M i).p z))
      (Sigma.ι_comp_desc (fun j => (a j).hom.left) i)
    have hmap := congrArg (fun f : C i ⟶ N.X => f z) (a i).comm
    calc
      _ = (a i).hom.left ((M i).p z) := hdesc
      _ = N.p ((m i).left z) := hmap
      _ = N.f.fiberι (genericPoint S) x := by rw [hfield]; exact htarget
  obtain ⟨z', _, hz'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Sigma.desc fun j => (a j).hom.left)
    (g := N.f.fiberι (genericPoint S)) y x hy
  exact ⟨z', hz'⟩

end AlgebraicGeometry.Scheme.FinitePresentationDescent.Model.Map

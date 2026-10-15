/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorStalkPure.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 99]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The original pure tensor of two module germs

Common section representatives define a bilinear map into the stalk of the
original sheafified tensor. All scalar actions are the original stalk actions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Two module germs have representatives over one open neighborhood. -/
theorem exists_two_module_germ_representatives (X : Scheme.{u}) (x : X)
    (M N : X.Modules) (m : M.presheaf.stalk x) (n : N.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)),
      M.presheaf.germ U x hx s = m ∧ N.presheaf.germ U x hx t = n := by
  obtain ⟨V, hxV, s, rfl⟩ := M.presheaf.exists_germ_eq m
  obtain ⟨U, hUV, hxU, t, rfl⟩ := N.presheaf.exists_le_germ_eq n hxV
  exact ⟨U, hxU, M.presheaf.map (homOfLE hUV).op s, t,
    M.presheaf.germ_res_apply _ _ _ _, rfl⟩

/-- The original tensor germ is unchanged when both representatives are restricted. -/
theorem moduleTensorSection_germ_restrict (X : Scheme.{u}) (x : X) (M N : X.Modules)
    {U V : X.Opens} (i : U ⟶ V) (hx : x ∈ U) (s : Γ(M, V)) (t : Γ(N, V)) :
    ((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
        (moduleTensorSection X M N U (M.presheaf.map i.op s) (N.presheaf.map i.op t)) =
      ((moduleTensorLeftFunctor X M).obj N).presheaf.germ V x (i.le hx)
        (moduleTensorSection X M N V s t) := by
  rw [← moduleTensorSection_restrict M N i s t]
  exact ((moduleTensorLeftFunctor X M).obj N).presheaf.germ_res_apply i x hx _

/-- The pure tensor germ depends only on the two input germs. -/
theorem moduleTensorSection_germ_eq (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (U V : X.Opens) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : Γ(M, U)) (s' : Γ(M, V)) (t : Γ(N, U)) (t' : Γ(N, V))
    (hm : M.presheaf.germ U x hxU s = M.presheaf.germ V x hxV s')
    (hn : N.presheaf.germ U x hxU t = N.presheaf.germ V x hxV t') :
    ((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hxU
        (moduleTensorSection X M N U s t) =
      ((moduleTensorLeftFunctor X M).obj N).presheaf.germ V x hxV
        (moduleTensorSection X M N V s' t') := by
  obtain ⟨W, hxW, iWU, iWV, hmW⟩ := M.presheaf.germ_eq x hxU hxV s s' hm
  obtain ⟨Z, hxZ, iZU, iZV, hnZ⟩ := N.presheaf.germ_eq x hxU hxV t t' hn
  let a : W ⊓ Z ⟶ U := homOfLE inf_le_left ≫ iWU
  let b : W ⊓ Z ⟶ V := homOfLE inf_le_left ≫ iWV
  have hm' : M.presheaf.map a.op s = M.presheaf.map b.op s' := by
    have h := congrArg (fun z => M.presheaf.map (homOfLE inf_le_left : W ⊓ Z ⟶ W).op z) hmW
    simpa only [a, b, op_comp, Functor.map_comp, AddCommGrpCat.comp_apply] using h
  have hn' : N.presheaf.map a.op t = N.presheaf.map b.op t' := by
    have h := congrArg (fun z => N.presheaf.map (homOfLE inf_le_right : W ⊓ Z ⟶ Z).op z) hnZ
    have ha : a = homOfLE inf_le_right ≫ iZU := Subsingleton.elim _ _
    have hb : b = homOfLE inf_le_right ≫ iZV := Subsingleton.elim _ _
    simpa only [ha, hb, op_comp, Functor.map_comp, AddCommGrpCat.comp_apply] using h
  rw [← moduleTensorSection_germ_restrict X x M N a ⟨hxW, hxZ⟩ s t,
    ← moduleTensorSection_germ_restrict X x M N b ⟨hxW, hxZ⟩ s' t', hm', hn']

/-- Common representatives define the original pure tensor of two module germs. -/
def moduleTensorStalkPure (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (m : M.presheaf.stalk x) (n : N.presheaf.stalk x) :
    ((moduleTensorLeftFunctor X M).obj N).presheaf.stalk x := by
  let h := exists_two_module_germ_representatives X x M N m n
  let U := Classical.choose h
  let hx := Classical.choose (Classical.choose_spec h)
  let s := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
  let t := Classical.choose (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec h)))
  exact ((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
    (moduleTensorSection X M N U s t)

/-- Evaluation on any simultaneous representatives, independently of the choices. -/
theorem moduleTensorStalkPure_germ (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    moduleTensorStalkPure X x M N (M.presheaf.germ U x hx s) (N.presheaf.germ U x hx t) =
      ((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
        (moduleTensorSection X M N U s t) := by
  let h := exists_two_module_germ_representatives X x M N
    (M.presheaf.germ U x hx s) (N.presheaf.germ U x hx t)
  unfold moduleTensorStalkPure
  exact moduleTensorSection_germ_eq X x M N _ U _ hx _ s _ t
    (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h)))).1
    (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h)))).2

end AlgebraicGeometry.Scheme.Modules

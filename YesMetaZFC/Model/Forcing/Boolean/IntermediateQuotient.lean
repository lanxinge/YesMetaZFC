import YesMetaZFC.Model.Forcing.Boolean.GenericName
import YesMetaZFC.Model.Forcing.CCC.Basic
import YesMetaZFC.Model.Forcing.Iteration.Names.Generic
import YesMetaZFC.Model.Forcing.Extension.Choice

/-! # 在原小泛型扩张中构造商条件集

先在 M[H] 中分离 H 所命中的旧正则开集，再分离与它们的全部嵌入像相容的
旧目标正条件。商载体实际属于 M[H]；不在较大的扩张中代造这个集合。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem image_cmp_l (hZF : M.Models ZF) (hN : Extensional N)
    (j : M.Domain → N.Domain) (inj : Function.Injective j)
    (full : ∀ a y, N.mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y) {B R z p q : M.Domain} :
    Cmp_d N (j B) (j R) (j z) (j p) (j q) ↔ Cmp_d M B R z p q := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hN
  constructor
  · rintro ⟨r,hr,rq⟩
    obtain ⟨s,hs,rfl⟩ := (full B r).mp hr.1
    exact ⟨s,⟨hs,fun eq => hr.2.1 (congrArg j eq),(entry s p R).mpr hr.2.2⟩,(entry s q R).mpr rq⟩
  · rintro ⟨r,hr,rq⟩
    exact ⟨j r,⟨(image_member_l j inj full).mpr hr.1,fun eq => hr.2.1 (inj eq),
      (entry r p R).mp hr.2.2⟩,(entry r q R).mp rq⟩

def Qread_d (j : M.Domain → N.Domain) (H : M.Domain → Prop) (A L V d J : M.Domain) (D : N.Domain) : Prop :=
  ∀ x, N.mem x D ↔ ∃ q, M.mem q L ∧ q ≠ d ∧ j q = x ∧
    ∀ a y, M.mem a A → (∃ r, H r ∧ M.mem r a) → Entry_d M a y J → Cmp_d M L V d q y

theorem Qread_d.order_l (hZF : M.Models ZF) (hN : Extensional N)
    {j : M.Domain → N.Domain} (inj : Function.Injective j)
    (full : ∀ a y, N.mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y)
    {H : M.Domain → Prop} {A L V d J : M.Domain} {D : N.Domain}
    (read : Qread_d j H A L V d J D) (O : Cond_order_d M L V d) : Cond_order_d N D (j V) (j d) := by
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hN
  refine ⟨?_,?_,?_⟩
  · intro x hx
    obtain ⟨q,hq,_,rfl,_⟩ := (read x).mp hx
    exact (entry q q V).mp (O.refl q hq)
  · intro x y z hx hy hz xy yz
    obtain ⟨a,ha,_,rfl,_⟩ := (read x).mp hx
    obtain ⟨b,hb,_,rfl,_⟩ := (read y).mp hy
    obtain ⟨c,hc,_,rfl,_⟩ := (read z).mp hz
    exact (entry a c V).mp (O.trans a b c ha hb hc ((entry a b V).mpr xy) ((entry b c V).mpr yz))
  · intro x hx xd
    obtain ⟨q,hq,_,rfl,_⟩ := (read x).mp hx
    exact congrArg j (O.zero q hq ((entry q d V).mpr xd))

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem quotient_intermediate_l {Q T w A L V d J : M.Domain} (O : Cond_order_d M Q T w)
    {H : M.Domain → Prop} (generic : Generic_d M Q T w H) (fn : M.IsSetFunctionFromTo I J A L) :
    ∃ c, H c ∧ ∃ j : M.Domain → (extension_l M hZF Q T w H).Domain, Function.Injective j ∧
      (∀ a y, (extension_l M hZF Q T w H).mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y) ∧
      (∀ a t, Check_d M c a t → Qval_d M Q T w H t (j a)) ∧
      ∃ D : (extension_l M hZF Q T w H).Domain, Qread_d j H A L V d J D := by
  let E := extension_l M hZF Q T w H
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨b,hb⟩ := generic.inhabited
  obtain ⟨γ,name⟩ := gname_exists_l hZF (generic.proper b hb).1
  obtain ⟨Y,value⟩ := name_value_l (R := T) (z := w) (U := H) name.1
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hZF generic hb
  have ground := gname_value_l hZF O generic name value j checks
  have hy r : E.mem (j r) Y ↔ H r :=
    (ground (j r)).trans ⟨fun ⟨s,hs,eq⟩ => inj eq ▸ hs,fun hr => ⟨r,hr,rfl⟩⟩
  let ρ : Env E 1 := ⟨fun _ => Y,fun _ => Y⟩
  let φ : UnarySchema 1 := { body := .existsE (.conj (.mem .newest (.bound 1)) (.mem .newest (.bound 2))) }
  obtain ⟨W,members⟩ := ZF.separation_exists_d hE φ ρ (j A)
  have member x : E.mem x W ↔ E.mem x (j A) ∧ ∃ r, E.mem r x ∧ E.mem r Y := by
    have h := members x
    simp only [φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at h
    exact h
  have oldMember a : E.mem (j a) W ↔ M.mem a A ∧ ∃ r, H r ∧ M.mem r a := by
    apply (member (j a)).trans
    apply and_congr (image_member_l j inj full)
    constructor
    · rintro ⟨x,hx,hY⟩
      obtain ⟨r,ra,rfl⟩ := (full a x).mp hx
      exact ⟨r,(hy r).mp hY,ra⟩
    · rintro ⟨r,hr,ra⟩
      exact ⟨j r,(full a (j r)).mpr ⟨r,ra,rfl⟩,(hy r).mpr hr⟩
  let η : Env E 5 := ⟨fun i => [j L,j V,j d,j J,W].get i,fun _ => Y⟩
  let ψ : UnarySchema 5 := { body := set[6] ⟪
    ⌜(.newest : Term 6)⌝ₛ ≠ ⌜(.bound 3 : Term 6)⌝ₛ ∧
    (∀ a ∈ ⌜(.bound 5 : Term 6)⌝ₛ, ∀ y, ⌜entry_m⌝ₚ(a,y,⌜(.bound 4 : Term 6)⌝ₛ) →
      ⌜cmp_m⌝ₚ(⌜(.bound 1 : Term 6)⌝ₛ,⌜(.bound 2 : Term 6)⌝ₛ,⌜(.bound 3 : Term 6)⌝ₛ,⌜(.newest : Term 6)⌝ₛ,y))⟫ }
  obtain ⟨D,conditions⟩ := ZF.separation_exists_d hE ψ η (j L)
  have read x : E.mem x D ↔ E.mem x (j L) ∧ x ≠ j d ∧
      ∀ a, E.mem a W → ∀ y, Entry_d E a y (j J) → Cmp_d E (j L) (j V) (j d) x y := by
    apply (conditions x).trans (and_congr_right fun _ => ?_)
    simp only [ψ,Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hE.1,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff,entry_sat_l E hE.1,cmp_sat_l E hE.1,Definitional.Term.eval_weaken]
    rfl
  have entry := image_entry_iff_l j inj full (KP.exists_pair (ZF.modelsKP hZF)) hE.1
  have imageFn := image_function_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) j inj full fn
  refine ⟨b,hb,j,inj,full,checks,D,fun x => (read x).trans ⟨?_,?_⟩⟩
  · rintro ⟨hx,hz,compat⟩
    obtain ⟨q,hq,rfl⟩ := (full L x).mp hx
    refine ⟨q,hq,fun eq => hz (congrArg j eq),rfl,fun a y ha hit ay => ?_⟩
    exact (image_cmp_l hZF hE.1 j inj full).mp
      (compat (j a) ((oldMember a).mpr ⟨ha,hit⟩) (j y) ((entry a y J).mp ay))
  · rintro ⟨q,hq,hz,rfl,compat⟩
    refine ⟨(image_member_l j inj full).mpr hq,fun eq => hz (inj eq),fun a ha y ay => ?_⟩
    obtain ⟨s,hs,rfl⟩ := (full A a).mp ((member a).mp ha).1
    obtain ⟨t,_,rfl⟩ := (full L y).mp (imageFn.output_mem_of_pairMember ay)
    exact (image_cmp_l hZF hE.1 j inj full).mpr (compat s t hs ((oldMember s).mp ha).2 ((entry s t J).mpr ay))

end YesMetaZFC.Model.Forcing.Internal

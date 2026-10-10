import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Hull

/-! # 有限基上的正元数真值表

语法元数是外部有限数；赋值、元组与真值表都是背景模型内的对象。
元组使用 Jensen 的右嵌套约定，单元组就是其唯一坐标。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rt_tuple_d : {n : Nat} → (Fin (n + 1) → M.Domain) → M.Domain → Prop
  | 0, e, p => p = e 0
  | n + 1, e, p => ∃ q, KPair_d M p (e 0) q ∧ Rt_tuple_d (n := n) (fun i => e i.succ) q

theorem rt_tuple_inj_l {n} {e f : Fin (n + 1) → M.Domain} {p : M.Domain}
    (he : Rt_tuple_d e p) (hf : Rt_tuple_d f p) : e = f := by
  induction n generalizing p with
  | zero =>
    funext i
    have hi : i = 0 := by omega
    subst i
    exact he.symm.trans hf
  | succ n ih =>
    obtain ⟨q, hq, he⟩ := he
    obtain ⟨r, hr, hf⟩ := hf
    obtain ⟨h0, hqr⟩ := kpair_injective_l M hq hr; subst r
    exact funext (Fin.cases h0 (congrFun (ih he hf)))

theorem rt_tuple_unique_l (hE : Extensional M) {n} {e : Fin (n + 1) → M.Domain} {p q : M.Domain}
    (hp : Rt_tuple_d e p) (hq : Rt_tuple_d e q) : p = q := by
  induction n generalizing p q with
  | zero => exact hp.trans hq.symm
  | succ n ih =>
    obtain ⟨r, hr, hp⟩ := hp
    obtain ⟨s, hs, hq⟩ := hq
    have he := ih hp hq; subst s
    exact kpair_unique_l M hE hr hs

theorem rt_tuple_exists_l (hKP : M.Models KP) {n} (e : Fin (n + 1) → M.Domain) : ∃ p, Rt_tuple_d e p := by
  induction n with
  | zero => exact ⟨e 0, rfl⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih (fun i => e i.succ)
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total (e 0) q
    exact ⟨p, q, hp, hq⟩

abbrev Rt_env (U : M.Domain) (n : Nat) := Fin (n + 1) → {x : M.Domain // M.mem x U}

def Rt_table_d {n} (U : M.Domain) (P : Rt_env U n → Prop) (R : M.Domain) : Prop :=
  ∀ p, M.mem p R ↔ ∃ e, Rt_tuple_d (fun i => (e i).val) p ∧ P e

theorem rt_env_inj_l {U : M.Domain} {n} {e f : Rt_env U n} {p : M.Domain}
    (he : Rt_tuple_d (fun i => (e i).val) p) (hf : Rt_tuple_d (fun i => (f i).val) p) : e = f :=
  funext fun i => Subtype.ext (congrFun (rt_tuple_inj_l he hf) i)

theorem Rd_closed_d.exists_l {C : M.Domain} (hC : Rd_closed_d C) (hKP : M.Models KP)
    (k : Rd_sym) {a b c : M.Domain} (ha : M.mem a C) (hb : M.mem b C) (hc : M.mem c C) :
    ∃ t, M.mem t C ∧ Rd_fun_d k a b c t := by
  obtain ⟨t, ht⟩ := rd_fun_exists_l hKP k a b c
  exact ⟨t, hC k a b c ha hb hc t ht, ht⟩

theorem rt_power_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C) (hU : M.mem U C) (n : Nat) :
    ∃ R, M.mem R C ∧ Rt_table_d (n := n) U (fun _ => True) R := by
  induction n with
  | zero =>
    refine ⟨U, hU, fun p => ?_⟩
    exact ⟨fun hp => ⟨fun _ => ⟨p, hp⟩, rfl, trivial⟩, fun ⟨e, he, _⟩ => he ▸ (e 0).property⟩
  | succ n ih =>
    obtain ⟨S, hSC, hS⟩ := ih
    obtain ⟨R, hRC, hR⟩ := hC.exists_l hKP .prod hU hSC hU
    refine ⟨R, hRC, fun p => (hR p).trans ?_⟩
    constructor
    · rintro ⟨a, q, ha, hq, hp⟩
      obtain ⟨e, he, _⟩ := (hS q).mp hq
      let f : Rt_env U (n + 1) := Fin.cases ⟨a, ha⟩ e
      exact ⟨f, ⟨q, hp, he⟩, trivial⟩
    · rintro ⟨e, ⟨q, hp, hq⟩, _⟩
      exact ⟨(e 0).val, q, (e 0).property, (hS q).mpr ⟨fun i => e i.succ, hq, trivial⟩, hp⟩

theorem rt_neg_l (hKP : M.Models KP) {C U R : M.Domain} {n} {P : Rt_env U n → Prop}
    (hC : Rd_closed_d C) (hU : M.mem U C) (hRC : M.mem R C) (hR : Rt_table_d U P R) :
    ∃ S, M.mem S C ∧ Rt_table_d U (fun e => ¬ P e) S := by
  obtain ⟨D, hDC, hD⟩ := rt_power_l hKP hC hU n
  obtain ⟨S, hSC, hS⟩ := hC.exists_l hKP .diff hDC hRC hU
  refine ⟨S, hSC, fun p => (hS p).trans ?_⟩
  constructor
  · rintro ⟨hp, hn⟩
    obtain ⟨e, he, _⟩ := (hD p).mp hp
    exact ⟨e, he, fun h => hn ((hR p).mpr ⟨e, he, h⟩)⟩
  · rintro ⟨e, he, hn⟩
    refine ⟨(hD p).mpr ⟨e, he, trivial⟩, fun hp => ?_⟩
    obtain ⟨f, hf, hp⟩ := (hR p).mp hp
    exact hn (rt_env_inj_l hf he ▸ hp)

theorem rt_and_l (hKP : M.Models KP) {C U R S : M.Domain} {n} {P Q : Rt_env U n → Prop}
    (hC : Rd_closed_d C) (hRC : M.mem R C) (hSC : M.mem S C)
    (hR : Rt_table_d U P R) (hS : Rt_table_d U Q S) :
    ∃ T, M.mem T C ∧ Rt_table_d U (fun e => P e ∧ Q e) T := by
  obtain ⟨D, hDC, hD⟩ := hC.exists_l hKP .diff hRC hSC hRC
  obtain ⟨T, hTC, hT⟩ := hC.exists_l hKP .diff hRC hDC hRC
  classical
  have ht p : M.mem p T ↔ M.mem p R ∧ M.mem p S := by
    rw [hT p]; change (M.mem p R ∧ ¬ M.mem p D) ↔ _
    rw [hD p]; change (M.mem p R ∧ ¬ (M.mem p R ∧ ¬ M.mem p S)) ↔ _
    exact ⟨fun ⟨h, hn⟩ => ⟨h, Classical.byContradiction (fun hs => hn ⟨h, hs⟩)⟩,
      fun ⟨h, hs⟩ => ⟨h, fun hn => hn.2 hs⟩⟩
  refine ⟨T, hTC, fun p => (ht p).trans ?_⟩
  constructor
  · rintro ⟨hp, hq⟩
    obtain ⟨e, he, hp⟩ := (hR p).mp hp
    obtain ⟨f, hf, hq⟩ := (hS p).mp hq
    exact ⟨e, he, hp, rt_env_inj_l hf he ▸ hq⟩
  · exact fun ⟨e, he, hp, hq⟩ => ⟨(hR p).mpr ⟨e, he, hp⟩, (hS p).mpr ⟨e, he, hq⟩⟩

theorem rt_exists_l (hKP : M.Models KP) {C U R : M.Domain} {n} {P : Rt_env U (n + 1) → Prop}
    (hC : Rd_closed_d C) (hRC : M.mem R C) (hR : Rt_table_d U P R) :
    ∃ S, M.mem S C ∧ Rt_table_d U (fun e => ∃ x, P (Fin.cases x e)) S := by
  obtain ⟨S, hSC, hS⟩ := hC.exists_l hKP .range hRC hRC hRC
  refine ⟨S, hSC, fun p => (hS p).trans ?_⟩
  constructor
  · rintro ⟨a, q, hq, hqR⟩
    obtain ⟨e, ⟨r, hr, he⟩, hp⟩ := (hR q).mp hqR
    obtain ⟨_, hpr⟩ := kpair_injective_l M hq hr; subst r
    refine ⟨fun i => e i.succ, he, e 0, ?_⟩
    have heq : Fin.cases (e 0) (fun i => e i.succ) = e := funext (Fin.cases rfl (fun _ => rfl))
    exact heq.symm ▸ hp
  · rintro ⟨e, he, x, hp⟩
    obtain ⟨q, hq⟩ := (kp_pair_l hKP).total x.val p
    let f : Rt_env U (n + 1) := Fin.cases x e
    exact ⟨x.val, q, hq, (hR q).mpr ⟨f, ⟨p, hq, he⟩, hp⟩⟩

end YesMetaZFC.SetTheory.InnerModel

import YesMetaZFC.SetTheory.LargeCardinal.Demand.Parameters
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy

/-! # demanding 类型游戏的增长与继续规则

三阶段事件和重置规则复用原实现。继续只读取较早走法的节点长度 j，
要求当前长度为其后继；旧回答元数由 2j+3 计算，超过关系方向保持旧 w 到新 u。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_growth_d (e c A n h κ B : M.Domain) : Prop :=
  (n = e ∧ M.mem A B) ∨ ∃ j v ℓ k τ u, M.SuccessorOf n j ∧ Tg_event_d I c j e h v ∧
    Td_move_d v ℓ k τ u ∧ M.mem τ κ

def td_growth_m {d} (e c A n h κ B : Term d) : Formula 1 d := set[d] ⟪
  (⌜n⌝ₛ = ⌜e⌝ₛ ∧ ⌜A⌝ₛ ∈ ⌜B⌝ₛ) ∨ (∃ j v ℓ k τ u,
    ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ,j) ∧ ⌜tg_event_m⌝ₚ(⌜c⌝ₛ,j,⌜e⌝ₛ,⌜h⌝ₛ,v) ∧
    ⌜td_move_m⌝ₚ(v,ℓ,k,τ,u) ∧ τ ∈ ⌜κ⌝ₛ)⟫
derive_free_closed td_growth_m

theorem td_growth_sat_l {d} (ρ : Env M d) (e c A n h κ B : Term d) :
    Formula.satisfies ρ (td_growth_m e c A n h κ B) ↔
      Td_growth_d hZF (e.eval ρ) (c.eval ρ) (A.eval ρ) (n.eval ρ) (h.eval ρ) (κ.eval ρ) (B.eval ρ) := by
  simp only [td_growth_m,Td_growth_d,Formula.satisfies_disj_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff,tg_event_sat_l I hZF.1,td_move_sat_l hZF.1,Definitional.Term.eval_weaken]
  rfl

def Td_continue_d (ω e a c δ n h ℓ κ k N U D u : M.Domain) : Prop :=
  M.mem ℓ n ∧ ∃ v w ℓ₀ j κ₀ u₀ τ T d q l m B V W,
    Tg_event_d I c ℓ e h v ∧ Td_move_d v ℓ₀ j κ₀ u₀ ∧ Tg_event_d I c ℓ a h w ∧ KPair_d M w τ T ∧
    M.SuccessorOf k j ∧ Td_arity_d I j d q l m ∧
    M.IsLimitOrdinal τ ∧ V_d I τ B ∧ (∀ y, M.mem y V ↔ M.mem y B ∨ y = τ) ∧ Tt_pool_d I ω m V W ∧
    Tx_exceeds_d hZF ω δ τ m V W T κ N U D u

def td_continue0_m : Formula 1 14 :=
  let ω : Term 14 := .bound 0; let e : Term 14 := .bound 1; let a : Term 14 := .bound 2
  let c : Term 14 := .bound 3; let δ : Term 14 := .bound 4; let n : Term 14 := .bound 5
  let h : Term 14 := .bound 6; let ℓ : Term 14 := .bound 7; let κ : Term 14 := .bound 8
  let k : Term 14 := .bound 9; let N : Term 14 := .bound 10; let U : Term 14 := .bound 11
  let D : Term 14 := .bound 12; let u : Term 14 := .bound 13
  set[14] ⟪⌜ℓ⌝ₛ ∈ ⌜n⌝ₛ ∧ (∃ v w ℓ₀ j κ₀ u₀ τ T d q l m B V W,
    ⌜tg_event_m⌝ₚ(⌜c⌝ₛ,⌜ℓ⌝ₛ,⌜e⌝ₛ,⌜h⌝ₛ,v) ∧ ⌜td_move_m⌝ₚ(v,ℓ₀,j,κ₀,u₀) ∧
    ⌜tg_event_m⌝ₚ(⌜c⌝ₛ,⌜ℓ⌝ₛ,⌜a⌝ₛ,⌜h⌝ₛ,w) ∧ ⌜kpair0_m⌝ₚ(w,τ,T) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜k⌝ₛ,j) ∧ ⌜td_arity_m⌝ₚ(j,d,q,l,m) ∧
    ⌜Formula.isLimitOrdinal⌝ₚ(τ) ∧ ⌜v_sigma_m⌝ₚ(τ,B) ∧ ⌜tt_constants0_m⌝ₚ(τ,B,V) ∧
    ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ,m,V,W) ∧
    ⌜tx_exceeds_m⌝ₚ(⌜ω⌝ₛ,⌜δ⌝ₛ,τ,m,V,W,T,⌜κ⌝ₛ,⌜N⌝ₛ,⌜U⌝ₛ,⌜D⌝ₛ,⌜u⌝ₛ))⟫

theorem td_continue0_closed_l : td_continue0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_continue0_m,Definitional.Formula.FreeClosed]

def td_continue_m {d} (ω e a c δ n h ℓ κ k N U D u : Term d) : Formula 1 d :=
  td_continue0_m.bind (fun i => [ω,e,a,c,δ,n,h,ℓ,κ,k,N,U,D,u].get i)

@[simp] theorem td_continue_m_freeClosed {d} (ω e a c δ n h ℓ κ k N U D u : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (ha : a.freeSupport = [])
    (hc : c.freeSupport = []) (hd : δ.freeSupport = []) (hn : n.freeSupport = [])
    (hh : h.freeSupport = []) (hl : ℓ.freeSupport = []) (hκ : κ.freeSupport = [])
    (hk : k.freeSupport = []) (hN : N.freeSupport = []) (hU : U.freeSupport = [])
    (hD : D.freeSupport = []) (hu : u.freeSupport = []) :
    (td_continue_m ω e a c δ n h ℓ κ k N U D u).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr td_continue0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw,he,ha,hc,hd,hn,hh,hl,hκ,hk,hN,hU,hD,hu,fun i => Fin.elim0 i⟩

theorem td_continue_sat_l {d} (ρ : Env M d) (ω e a c δ n h ℓ κ k N U D u : Term d) :
    Formula.satisfies ρ (td_continue_m ω e a c δ n h ℓ κ k N U D u) ↔ Td_continue_d hZF
      (ω.eval ρ) (e.eval ρ) (a.eval ρ) (c.eval ρ) (δ.eval ρ) (n.eval ρ) (h.eval ρ) (ℓ.eval ρ)
      (κ.eval ρ) (k.eval ρ) (N.eval ρ) (U.eval ρ) (D.eval ρ) (u.eval ρ) := by
  simp only [td_continue_m,Formula.satisfies_bind,td_continue0_m,Td_continue_d,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,
    tg_event_sat_l I hZF.1,td_move_sat_l hZF.1,kpair0_sat_l hZF.1,
    Formula.satisfies_isSuccessor_iff,td_arity_sat_l I hZF.1,Formula.satisfies_isLimitOrdinal_iff,
    v_sigma_sat_l (ZF.modelsKP hZF),tt_constants0_sat_l hZF.1,tt_pool_sat_l I (ZF.modelsKP hZF),
    tx_exceeds_sat_l hZF,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.1 的第二方走法：双图节点、域增长、重置和继续

元数由内部 k 加倍确定；节点条件读取固定查询行的字面成员性。
零轮使用原重置高度，非零轮只回指 k 少一的旧轮，不再附加旧游戏的 t 坐标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_aux_d (p : Tg_params_d M.Domain) (n h v : M.Domain) : Prop :=
  ∃ ℓ k κ u d q N m x s B U Du Dw pn pm pp pb ph C V E g₀ g₁ g₂ g₃,
    Td_move_d v ℓ k κ u ∧ M.mem k p.ω ∧ M.mem κ p.δ ∧ Td_arity_d I k d q N m ∧
    Tg_digits_d hZF p.c p.b n p.A h x ∧ M.IsRestrictionOf I s x k ∧
    Tg_query_request_d hZF p.ω κ k s p.A ∧
    Td_query_data_d p.Q κ k s p.A B U Du Dw pn pm pp pb ph ∧ M.MemberSubset u Du ∧
    Tg_ee_data_d p.E κ q C V E ⟨g₀,g₁,g₂,g₃⟩ ∧ Tg_elastic_d I q N E ⟨g₀,g₁,g₂,g₃⟩ u ∧
    M.mem pn u ∧ Td_growth_d hZF p.e p.c p.A n h κ B ∧
    ((k = p.e ∧ Tg_reset_d hZF p.ω p.e p.δ p.S p.ν q N U Du u) ∨
      (k ≠ p.e ∧ Td_continue_d hZF p.ω p.e p.a p.c p.δ n h ℓ κ k N U Du u))

def td_aux0_m : Formula 1 15 :=
  let p : Tg_params_d (Term 15) := ⟨.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,
    .bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11⟩
  let n : Term 15 := .bound 12; let h : Term 15 := .bound 13; let v : Term 15 := .bound 14
  set[15] ⟪∃ ℓ k κ u d q N m x s B U Du Dw pn pm pp pb ph C V E g₀ g₁ g₂ g₃,
    ⌜td_move_m⌝ₚ(⌜v⌝ₛ,ℓ,k,κ,u) ∧ k ∈ ⌜p.ω⌝ₛ ∧ κ ∈ ⌜p.δ⌝ₛ ∧ ⌜td_arity_m⌝ₚ(k,d,q,N,m) ∧
    ⌜tg_digits_m⌝ₚ(⌜p.c⌝ₛ,⌜p.b⌝ₛ,⌜n⌝ₛ,⌜p.A⌝ₛ,⌜h⌝ₛ,x) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(s,x,k) ∧
    ⌜tg_query_request_m⌝ₚ(⌜p.ω⌝ₛ,κ,k,s,⌜p.A⌝ₛ) ∧
    ⌜td_query_data_m⌝ₚ(⌜p.Q⌝ₛ,κ,k,s,⌜p.A⌝ₛ,B,U,Du,Dw,pn,pm,pp,pb,ph) ∧ u ⊆ Du ∧
    ⌜tg_ee_data_m⌝ₚ(⌜p.E⌝ₛ,κ,q,C,V,E,g₀,g₁,g₂,g₃) ∧ ⌜tg_elastic_m⌝ₚ(q,N,E,g₀,g₁,g₂,g₃,u) ∧
    pn ∈ u ∧ ⌜td_growth_m⌝ₚ(⌜p.e⌝ₛ,⌜p.c⌝ₛ,⌜p.A⌝ₛ,⌜n⌝ₛ,⌜h⌝ₛ,κ,B) ∧
    ((k = ⌜p.e⌝ₛ ∧ ⌜tg_reset_m⌝ₚ(⌜p.ω⌝ₛ,⌜p.e⌝ₛ,⌜p.δ⌝ₛ,⌜p.S⌝ₛ,⌜p.ν⌝ₛ,q,N,U,Du,u)) ∨
      (¬ (k = ⌜p.e⌝ₛ) ∧ ⌜td_continue_m⌝ₚ(⌜p.ω⌝ₛ,⌜p.e⌝ₛ,⌜p.a⌝ₛ,⌜p.c⌝ₛ,⌜p.δ⌝ₛ,
        ⌜n⌝ₛ,⌜h⌝ₛ,ℓ,κ,k,N,U,Du,u)))⟫

theorem td_aux0_closed_l : td_aux0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_aux0_m,Definitional.Formula.FreeClosed]

def td_aux_m {d} (p : Tg_params_d (Term d)) (n h v : Term d) : Formula 1 d :=
  td_aux0_m.bind (fun i => [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,n,h,v].get i)

@[simp] theorem td_aux_closed_l {d} (p : Tg_params_d (Term d)) (n h v : Term d)
    (hp : p.closed_l) (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (td_aux_m p n h v).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr td_aux0_closed_l
  rcases hp with ⟨hω,he,ha,hb,hc,hδ,hA,hS,hν,hE,hP,hQ⟩
  simp only [Fin.forall_fin_succ]
  exact ⟨hω,he,ha,hb,hc,hδ,hA,hS,hν,hE,hP,hQ,hn,hh,hv,fun i => Fin.elim0 i⟩

theorem td_aux_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (n h v : Term d) :
    Formula.satisfies ρ (td_aux_m p n h v) ↔
      Td_aux_d hZF (p.map_l (fun t => t.eval ρ)) (n.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [td_aux_m,Formula.satisfies_bind,td_aux0_m,Td_aux_d,Tg_params_d.map_l,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,td_move_sat_l hZF.1,
    Formula.satisfies_mem_iff,td_arity_sat_l I hZF.1,tg_digits_sat_l hZF,
    Formula.satisfies_isRestriction_iff I,tg_query_request_sat_l hZF,td_query_data_sat_l hZF.1,
    Formula.satisfies_subset_iff,tg_ee_data_sat_l hZF.1,tg_elastic_sat_l I hZF.1,
    td_growth_sat_l hZF,Formula.satisfies_disj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
    tg_reset_sat_l hZF,Formula.satisfies_neg_iff,td_continue_sat_l hZF,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 7.1 的第一方回答：原 subtype 与三个固定查询

u 的元数为 2k+2，w 的元数为 2k+3。先删除 u 的高度槽，再由固定
程序读取原 subtype；回答只检查 pending、严格秩界与加二最大序数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_reply_d (I : kpair_convention_l.Interpretation M)
    (ω q n m κ τ U E Dw u w b z pp pb ph : M.Domain) (σ : Fin 7 → M.Domain) : Prop :=
  M.MemberSubset w Dw ∧ ∃ v, Td_dcp_d I q n E u v ∧
    Ts_subtype_d ω q κ τ m U w b σ z v ∧ M.mem pp w ∧ M.mem pb w ∧ M.mem ph w

def td_reply0_m : Formula 1 23 :=
  let ω := Term.bound 0; let q := Term.bound 1; let n := Term.bound 2; let m := Term.bound 3
  let κ := Term.bound 4; let τ := Term.bound 5; let U := Term.bound 6; let E := Term.bound 7
  let Dw := Term.bound 8; let u := Term.bound 9; let w := Term.bound 10; let b := Term.bound 11
  let z := Term.bound 12; let pp := Term.bound 13; let pb := Term.bound 14; let ph := Term.bound 15
  let σ : Fin 7 → Term 23 := Fin.cases (.bound 16) (Fin.cases (.bound 17) (Fin.cases (.bound 18)
    (Fin.cases (.bound 19) (Fin.cases (.bound 20) (Fin.cases (.bound 21) (fun _ => .bound 22))))))
  .conj (Formula.subset w Dw) (.existsE (.conj (td_dcp_m q.weaken n.weaken E.weaken u.weaken .newest)
    (.conj (ts_subtype_m ω.weaken q.weaken κ.weaken τ.weaken m.weaken U.weaken w.weaken b.weaken z.weaken .newest
      (fun j => (σ j).weaken)) (.conj (.mem pp.weaken w.weaken) (.conj (.mem pb.weaken w.weaken) (.mem ph.weaken w.weaken))))))

theorem td_reply0_closed_l : td_reply0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_reply0_m,Definitional.Formula.FreeClosed,Fin.forall_fin_succ]

def td_reply_m {d} (ω q n m κ τ U E Dw u w b z pp pb ph : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  td_reply0_m.bind (fun i => [ω,q,n,m,κ,τ,U,E,Dw,u,w,b,z,pp,pb,ph,
    σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i)

@[simp] theorem td_reply_closed_l {d} (ω q n m κ τ U E Dw u w b z pp pb ph : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hq : q.freeSupport = []) (hn : n.freeSupport = []) (hm : m.freeSupport = [])
    (hk : κ.freeSupport = []) (ht : τ.freeSupport = []) (hU : U.freeSupport = []) (hE : E.freeSupport = [])
    (hD : Dw.freeSupport = []) (hu : u.freeSupport = []) (hv : w.freeSupport = []) (hb : b.freeSupport = [])
    (hz : z.freeSupport = []) (hp : pp.freeSupport = []) (hB : pb.freeSupport = []) (hH : ph.freeSupport = [])
    (hσ : ∀ i, (σ i).freeSupport = []) : (td_reply_m ω q n m κ τ U E Dw u w b z pp pb ph σ).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr td_reply0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw,hq,hn,hm,hk,ht,hU,hE,hD,hu,hv,hb,hz,hp,hB,hH,
    hσ 0,hσ 1,hσ 2,hσ 3,hσ 4,hσ 5,hσ 6,fun i => Fin.elim0 i⟩

theorem td_reply_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω q n m κ τ U E Dw u w b z pp pb ph : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (td_reply_m ω q n m κ τ U E Dw u w b z pp pb ph σ) ↔
      Td_reply_d (kp_pair_l hKP) (ω.eval ρ) (q.eval ρ) (n.eval ρ) (m.eval ρ) (κ.eval ρ) (τ.eval ρ)
        (U.eval ρ) (E.eval ρ) (Dw.eval ρ) (u.eval ρ) (w.eval ρ) (b.eval ρ) (z.eval ρ)
        (pp.eval ρ) (pb.eval ρ) (ph.eval ρ) (fun i => (σ i).eval ρ) := by
  simp only [td_reply_m,Formula.satisfies_bind,td_reply0_m,Td_reply_d,Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff,Formula.satisfies_exists_iff,td_dcp_sat_l (kp_pair_l hKP) hKP.1,
    ts_subtype_sat_l hKP,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  have eq : (fun i => (Fin.cases (.bound 16) (Fin.cases (.bound 17) (Fin.cases (.bound 18)
      (Fin.cases (.bound 19) (Fin.cases (.bound 20) (Fin.cases (.bound 21) (fun _ => .bound 22)))))) i : Term 23).eval
      (Definitional.Env.substitute ρ (fun i => [ω,q,n,m,κ,τ,U,E,Dw,u,w,b,z,pp,pb,ph,
        σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i))) = (fun i => (σ i).eval ρ) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  rw [eq]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_answer_d (p : Tg_params_d M.Domain) (n h v : M.Domain) : Prop :=
  ∃ a ℓ k κ u τ w d q N m B U E g₀ g₁ g₂ g₃ C V Du Dw pn pm pp pb ph b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    Tg_event_d I p.c n p.e h a ∧ Td_move_d a ℓ k κ u ∧ KPair_d M v τ w ∧ Td_arity_d I k d q N m ∧
    Tg_ee_data_d p.E κ q B U E ⟨g₀,g₁,g₂,g₃⟩ ∧ M.mem τ p.δ ∧ Tg_query_request_d hZF p.ω τ k p.e p.A ∧
    Td_query_data_d p.Q τ k p.e p.A C V Du Dw pn pm pp pb ph ∧
    Tg_program_data_d p.P q b z (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃
      (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆))))))) ∧
    Td_reply_d I p.ω q N m κ τ U E Dw u w b z pp pb ph (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂
      (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))

def td_answer0_m : Formula 1 15 :=
  let p : Tg_params_d (Term 15) := ⟨.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,
    .bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11⟩
  let n : Term 15 := .bound 12; let h : Term 15 := .bound 13; let v : Term 15 := .bound 14
  set[15] ⟪∃ a ℓ k κ u τ w d q N m B U E g₀ g₁ g₂ g₃ C V Du Dw pn pm pp pb ph b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ,⌜n⌝ₛ,⌜p.e⌝ₛ,⌜h⌝ₛ,a) ∧ ⌜td_move_m⌝ₚ(a,ℓ,k,κ,u) ∧
    ⌜kpair0_m⌝ₚ(⌜v⌝ₛ,τ,w) ∧ ⌜td_arity_m⌝ₚ(k,d,q,N,m) ∧
    ⌜tg_ee_data_m⌝ₚ(⌜p.E⌝ₛ,κ,q,B,U,E,g₀,g₁,g₂,g₃) ∧ τ ∈ ⌜p.δ⌝ₛ ∧
    ⌜tg_query_request_m⌝ₚ(⌜p.ω⌝ₛ,τ,k,⌜p.e⌝ₛ,⌜p.A⌝ₛ) ∧
    ⌜td_query_data_m⌝ₚ(⌜p.Q⌝ₛ,τ,k,⌜p.e⌝ₛ,⌜p.A⌝ₛ,C,V,Du,Dw,pn,pm,pp,pb,ph) ∧
    ⌜fun P q b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P q b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜p.P⌝ₛ,q,b,z,s₀,s₁,s₂,s₃,s₄,s₅,s₆) ∧
    ⌜fun ω q N m κ τ U E Dw u w b z pp pb ph s₀ s₁ s₂ s₃ s₄ s₅ s₆ =>
      td_reply_m ω q N m κ τ U E Dw u w b z pp pb ph
        (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜p.ω⌝ₛ,q,N,m,κ,τ,U,E,Dw,u,w,b,z,pp,pb,ph,s₀,s₁,s₂,s₃,s₄,s₅,s₆)⟫

theorem td_answer0_closed_l : td_answer0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_answer0_m,Definitional.Formula.FreeClosed,Fin.forall_fin_succ]

def td_answer_m {d} (p : Tg_params_d (Term d)) (n h v : Term d) : Formula 1 d :=
  td_answer0_m.bind (fun i => [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,n,h,v].get i)

@[simp] theorem td_answer_closed_l {d} (p : Tg_params_d (Term d)) (n h v : Term d)
    (hp : p.closed_l) (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (td_answer_m p n h v).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr td_answer0_closed_l
  rcases hp with ⟨hω,he,ha,hb,hc,hδ,hA,hS,hν,hE,hP,hQ⟩
  simp only [Fin.forall_fin_succ]
  exact ⟨hω,he,ha,hb,hc,hδ,hA,hS,hν,hE,hP,hQ,hn,hh,hv,fun i => Fin.elim0 i⟩

theorem td_answer_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (n h v : Term d) :
    Formula.satisfies ρ (td_answer_m p n h v) ↔
      Td_answer_d hZF (p.map_l (fun t => t.eval ρ)) (n.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [td_answer_m,Formula.satisfies_bind,td_answer0_m,Td_answer_d,Tg_params_d.map_l,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,tg_event_sat_l I hZF.1,td_move_sat_l hZF.1,
    kpair0_sat_l hZF.1,td_arity_sat_l I hZF.1,tg_ee_data_sat_l hZF.1,Formula.satisfies_mem_iff,
    tg_query_request_sat_l hZF,td_query_data_sat_l hZF.1,tg_program_data_sat_l hZF.1,
    td_reply_sat_l (ZF.modelsKP hZF),tt_eval_cases_l,Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双图继续请求与稠密命中的原公式

请求保存原两图、真实实现高度和后续局面的完整合法性。全部条件写成原语言
公式，供地模型内分离实际稠密集；没有外部合法性或公平性谓词。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_generic_target_d (p : Tg_params_d M.Domain) (ℓ s k N β a b v₀ w₀ κ C v u : M.Domain) : Prop :=
  M.mem κ p.δ ∧ V_d I κ C ∧ Td_move_d v ℓ k κ u ∧
  (∃ μ Y c H m V P r, M.SuccessorOf μ β ∧ V_d I μ Y ∧ Smem_d I c Y H ∧ M.SuccessorOf m N ∧
    (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧
    Tt_realized_d I p.ω c Y H m r p.δ V P u ∧ Rd_entry_d p.e p.S r ∧ Rd_entry_d N β r ∧
    Td_groups_d I p.ω p.e N r a b ∧ ∃ d, M.IsOrdinalAddition I d k k ∧ M.SuccessorOf N d) ∧
  ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z → M.IsRestrictionOf I s z k → M.mem ℓ n →
    Tg_event_d I p.c ℓ p.e h v₀ → Tg_event_d I p.c ℓ p.a h w₀ →
    Td_growth_d hZF p.e p.c p.A n h κ C → Td_aux_d hZF p n h v

def td_generic_target0_m : Formula 1 25 :=
  let p : Tg_params_d (Term 25) := ⟨.bound 0,.bound 1,.bound 2,.bound 3,.bound 4,.bound 5,
    .bound 6,.bound 7,.bound 8,.bound 9,.bound 10,.bound 11⟩
  let v : Fin 25 → Term 25 := Term.bound
  let aux {d} (ω e a b c δ A S ν E P Q n h v : Term d) := td_aux_m ⟨ω,e,a,b,c,δ,A,S,ν,E,P,Q⟩ n h v
  set[25] ⟪⌜v 21⌝ₛ ∈ ⌜p.δ⌝ₛ ∧ ⌜v_m kpair_convention_l⌝ₚ(⌜v 21⌝ₛ,⌜v 22⌝ₛ) ∧
    ⌜td_move_m⌝ₚ(⌜v 23⌝ₛ,⌜v 12⌝ₛ,⌜v 14⌝ₛ,⌜v 21⌝ₛ,⌜v 24⌝ₛ) ∧
    (∃ μ Y c H m V P r, ⌜Formula.isSuccessor⌝ₚ(μ,⌜v 16⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(μ,Y) ∧
      ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c,Y,H) ∧ ⌜Formula.isSuccessor⌝ₚ(m,⌜v 15⌝ₛ) ∧
      ⌜tt_constants0_m⌝ₚ(⌜v 21⌝ₛ,⌜v 22⌝ₛ,V) ∧ ⌜tt_realized_m⌝ₚ(⌜p.ω⌝ₛ,c,Y,H,m,r,⌜p.δ⌝ₛ,V,P,⌜v 24⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜p.e⌝ₛ,⌜p.S⌝ₛ,r) ∧ ⌜rd_entry0_m⌝ₚ(⌜v 15⌝ₛ,⌜v 16⌝ₛ,r) ∧
      ⌜td_groups_m⌝ₚ(⌜p.ω⌝ₛ,⌜p.e⌝ₛ,⌜v 15⌝ₛ,r,⌜v 17⌝ₛ,⌜v 18⌝ₛ) ∧
      (∃ d, ⌜Formula.isOrdinalAddition kpair_convention_l⌝ₚ(d,⌜v 14⌝ₛ,⌜v 14⌝ₛ) ∧
        ⌜Formula.isSuccessor⌝ₚ(⌜v 15⌝ₛ,d))) ∧
    (∀ n h z, ⌜tg_digits_m⌝ₚ(⌜p.c⌝ₛ,⌜p.b⌝ₛ,n,⌜p.A⌝ₛ,h,z) →
      ⌜Formula.isRestriction kpair_convention_l⌝ₚ(⌜v 13⌝ₛ,z,⌜v 14⌝ₛ) → ⌜v 12⌝ₛ ∈ n →
      ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ,⌜v 12⌝ₛ,⌜p.e⌝ₛ,h,⌜v 19⌝ₛ) →
      ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ,⌜v 12⌝ₛ,⌜p.a⌝ₛ,h,⌜v 20⌝ₛ) →
      ⌜td_growth_m⌝ₚ(⌜p.e⌝ₛ,⌜p.c⌝ₛ,⌜p.A⌝ₛ,n,h,⌜v 21⌝ₛ,⌜v 22⌝ₛ) →
      ⌜aux⌝ₚ(⌜p.ω⌝ₛ,⌜p.e⌝ₛ,⌜p.a⌝ₛ,⌜p.b⌝ₛ,⌜p.c⌝ₛ,⌜p.δ⌝ₛ,
        ⌜p.A⌝ₛ,⌜p.S⌝ₛ,⌜p.ν⌝ₛ,⌜p.E⌝ₛ,⌜p.P⌝ₛ,⌜p.Q⌝ₛ,n,h,⌜v 23⌝ₛ))⟫

theorem td_generic_target0_closed_l : td_generic_target0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_generic_target0_m,Definitional.Formula.FreeClosed]
  exact td_aux_closed_l _ _ _ _ (by simp -implicitDefEqProofs [Tg_params_d.closed_l]) rfl rfl rfl

def td_generic_target_m {d} (p : Tg_params_d (Term d)) (ℓ s k N β a b v₀ w₀ κ C v u : Term d) : Formula 1 d :=
  td_generic_target0_m.bind (fun i => [p.ω,p.e,p.a,p.b,p.c,p.δ,p.A,p.S,p.ν,p.E,p.P,p.Q,
    ℓ,s,k,N,β,a,b,v₀,w₀,κ,C,v,u].get i)

@[simp] theorem td_generic_target_closed_l {d} (p : Tg_params_d (Term d)) (ℓ s k N β a b v₀ w₀ κ C v u : Term d)
    (hp : p.closed_l) (hℓ : ℓ.freeSupport = []) (hs : s.freeSupport = []) (hk : k.freeSupport = [])
    (hN : N.freeSupport = []) (hβ : β.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = [])
    (h₀ : v₀.freeSupport = []) (h₁ : w₀.freeSupport = []) (hκ : κ.freeSupport = []) (hC : C.freeSupport = [])
    (hv : v.freeSupport = []) (hu : u.freeSupport = []) : (td_generic_target_m p ℓ s k N β a b v₀ w₀ κ C v u).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr td_generic_target0_closed_l
  rcases hp with ⟨hω,he,hA₀,hB₀,hc,hd,hA,hS,hν,hE,hP,hQ⟩
  simp only [Fin.forall_fin_succ]
  exact ⟨hω,he,hA₀,hB₀,hc,hd,hA,hS,hν,hE,hP,hQ,
    hℓ,hs,hk,hN,hβ,ha,hb,h₀,h₁,hκ,hC,hv,hu,fun i => Fin.elim0 i⟩

theorem td_generic_target_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (ℓ s k N β a b v₀ w₀ κ C v u : Term d) :
    Formula.satisfies ρ (td_generic_target_m p ℓ s k N β a b v₀ w₀ κ C v u) ↔
      Td_generic_target_d hZF (p.map_l (fun t => t.eval ρ)) (ℓ.eval ρ) (s.eval ρ) (k.eval ρ) (N.eval ρ)
        (β.eval ρ) (a.eval ρ) (b.eval ρ) (v₀.eval ρ) (w₀.eval ρ) (κ.eval ρ) (C.eval ρ) (v.eval ρ) (u.eval ρ) := by
  simp only [td_generic_target_m,Formula.satisfies_bind,td_generic_target0_m,Td_generic_target_d,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,v_sat_l I hZF.1,td_move_sat_l hZF.1,
    Formula.satisfies_exists_iff,Formula.satisfies_isSuccessor_iff,Formula.satisfies_isOrdinalAddition_iff I hZF.1,
    smem_sat_l I,tt_constants0_sat_l hZF.1,
    tt_realized_sat_l I (ZF.modelsKP hZF),rd_entry0_sat_l hZF.1,td_groups_sat_l I hZF.1,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,tg_digits_sat_l hZF,
    Formula.satisfies_isRestriction_iff I,tg_event_sat_l I hZF.1,td_growth_sat_l hZF,
    td_aux_sat_l hZF,Definitional.Term.eval_weaken,Tg_params_d.map_l]
  rfl

def Td_dense_hit_d (p : Tg_params_d M.Domain) (ℓ s k N β a b v₀ w₀ E q : M.Domain) : Prop :=
  ∃ κ C v u i, Td_generic_target_d hZF p ℓ s k N β a b v₀ w₀ κ C v u ∧
    M.mem E i ∧ M.mem i p.ω ∧ Rd_entry_d i v q ∧ ∀ j y, M.mem j i → Rd_entry_d j y q → M.mem y C

def td_dense_hit_m {d} (p : Tg_params_d (Term d)) (ℓ s k N β a b v₀ w₀ E q : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (td_generic_target_m (p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken))
      ℓ.weaken.weaken.weaken.weaken.weaken s.weaken.weaken.weaken.weaken.weaken
      k.weaken.weaken.weaken.weaken.weaken N.weaken.weaken.weaken.weaken.weaken β.weaken.weaken.weaken.weaken.weaken
      a.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken
      v₀.weaken.weaken.weaken.weaken.weaken w₀.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (set[d+5] ⟪⌜E.weaken.weaken.weaken.weaken.weaken⌝ₛ ∈ ⌜(.bound 0 : Term (d+5))⌝ₛ ∧
      ⌜(.bound 0 : Term (d+5))⌝ₛ ∈ ⌜p.ω.weaken.weaken.weaken.weaken.weaken⌝ₛ ∧
      ⌜rd_entry0_m⌝ₚ(⌜(.bound 0 : Term (d+5))⌝ₛ,⌜(.bound 2 : Term (d+5))⌝ₛ,⌜q.weaken.weaken.weaken.weaken.weaken⌝ₛ) ∧
      (∀ j y, j ∈ ⌜(.bound 0 : Term (d+5))⌝ₛ →
        ⌜rd_entry0_m⌝ₚ(j,y,⌜q.weaken.weaken.weaken.weaken.weaken⌝ₛ) → y ∈ ⌜(.bound 3 : Term (d+5))⌝ₛ)⟫))))))

theorem td_dense_hit_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (ℓ s k N β a b v₀ w₀ E q : Term d) :
    Formula.satisfies ρ (td_dense_hit_m p ℓ s k N β a b v₀ w₀ E q) ↔
      Td_dense_hit_d hZF (p.map_l (fun t => t.eval ρ)) (ℓ.eval ρ) (s.eval ρ) (k.eval ρ) (N.eval ρ)
        (β.eval ρ) (a.eval ρ) (b.eval ρ) (v₀.eval ρ) (w₀.eval ρ) (E.eval ρ) (q.eval ρ) := by
  simp only [td_dense_hit_m,Td_dense_hit_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    td_generic_target_sat_l hZF,Formula.satisfies_mem_iff,rd_entry0_sat_l hZF.1,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Definitional.Term.eval_weaken,Tg_params_d.map_l]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 游戏全部内部有限历史的实际检查

三阶段依原时序组合 7.1 的双图规则。空历史通过检查；非空历史只检查最后一步，
此前是否首次违规由独立的有限证据层判断，因而第二方违规后不会重新开局。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_step_d (p : Tg_params_d M.Domain) (i h v : M.Domain) : Prop := ∃ n r,
  M.mem n p.ω ∧ M.IsOrdinalDivision I i p.c n r ∧
    ((r = p.e ∧ Td_aux_d hZF p n h v) ∨ (r = p.a ∧ Td_answer_d hZF p n h v) ∨ (r = p.b ∧ M.mem v p.A))

def td_step_m {d} (p : Tg_params_d (Term d)) (i h v : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (.mem (.bound 1) p.ω.weaken.weaken) (.conj
    (Formula.isOrdinalDivision kpair_convention_l i.weaken.weaken p.c.weaken.weaken (.bound 1) .newest)
    (.disj (.conj (Formula.extensionalEq .newest p.e.weaken.weaken)
      (td_aux_m (p.map_l (fun t => t.weaken.weaken)) (.bound 1) h.weaken.weaken v.weaken.weaken))
    (.disj (.conj (Formula.extensionalEq .newest p.a.weaken.weaken)
      (td_answer_m (p.map_l (fun t => t.weaken.weaken)) (.bound 1) h.weaken.weaken v.weaken.weaken))
      (.conj (Formula.extensionalEq .newest p.b.weaken.weaken) (.mem v.weaken.weaken p.A.weaken.weaken)))))))

@[simp] theorem td_step_closed_l {d} (p : Tg_params_d (Term d)) (i h v : Term d)
    (hp : p.closed_l) (hi : i.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (td_step_m p i h v).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  rcases hp with ⟨hω, he, ha, hb, hc, _, hA, _⟩
  simp -implicitDefEqProofs [td_step_m, Definitional.Formula.FreeClosed, hω, he, ha, hb, hc, hA, hi, hh, hv, hp']

theorem td_step_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (i h v : Term d) :
    Formula.satisfies ρ (td_step_m p i h v) ↔ Td_step_d hZF (p.map_l (fun t => t.eval ρ)) (i.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [td_step_m, Td_step_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isOrdinalDivision_iff I hZF.1, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, td_aux_sat_l hZF, td_answer_sat_l hZF,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  rfl

theorem td_step_read_l {p : Tg_params_d M.Domain} {i n r h v : M.Domain}
    (hi : M.IsOrdinal i) (hc : M.IsOrdinal p.c) (nonzero : ∃ x, M.mem x p.c)
    (hn : M.mem n p.ω) (div : M.IsOrdinalDivision I i p.c n r) :
    Td_step_d hZF p i h v ↔
      (r = p.e ∧ Td_aux_d hZF p n h v) ∨ (r = p.a ∧ Td_answer_d hZF p n h v) ∨ (r = p.b ∧ M.mem v p.A) := by
  obtain ⟨q, s, _, unique⟩ := ZF.ordinalDivision_existsUnique_pair hZF I hi hc nonzero
  obtain ⟨en, er⟩ := unique n r div
  refine ⟨?_, fun h => ⟨n, r, hn, div, h⟩⟩
  rintro ⟨n', r', _, d', rule⟩
  obtain ⟨en', er'⟩ := unique n' r' d'
  exact (en'.trans en.symm) ▸ (er'.trans er.symm) ▸ rule

def Td_check_d (p : Tg_params_d M.Domain) (X f : M.Domain) : Prop := (∀ v, ¬ M.mem v f) ∨
  ∃ i j h v, M.mem j p.ω ∧ M.SuccessorOf j i ∧ Fn0_d j X f ∧ M.IsRestrictionOf I h f i ∧
    Rd_entry_d i v f ∧ Td_step_d hZF p i h v

def td_check_m {d} (p : Tg_params_d (Term d)) (X f : Term d) : Formula 1 d :=
  .disj (Formula.forallMem f .falsum) (.existsE (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 2) p.ω.weaken.weaken.weaken.weaken) (.conj (Formula.isSuccessor (.bound 2) (.bound 3))
      (.conj (fn0_m (.bound 2) X.weaken.weaken.weaken.weaken f.weaken.weaken.weaken.weaken)
        (.conj (Formula.isRestriction kpair_convention_l (.bound 1) f.weaken.weaken.weaken.weaken (.bound 3))
          (.conj (rd_entry0_m (.bound 3) .newest f.weaken.weaken.weaken.weaken)
            (td_step_m (p.map_l (fun t => t.weaken.weaken.weaken.weaken)) (.bound 3) (.bound 1) .newest))))))))))

@[simp] theorem td_check_closed_l {d} (p : Tg_params_d (Term d)) (X f : Term d)
    (hp : p.closed_l) (hX : X.freeSupport = []) (hf : f.freeSupport = []) : (td_check_m p X f).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  simp -implicitDefEqProofs [td_check_m, Definitional.Formula.FreeClosed, hp.1, hX, hf, hp']

theorem td_check_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X f : Term d) :
    Formula.satisfies ρ (td_check_m p X f) ↔ Td_check_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (f.eval ρ) := by
  simp only [td_check_m, Td_check_d, Formula.satisfies_disj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_falsum_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff, fn0_sat_l hZF.1,
    Formula.satisfies_isRestriction_iff I, rd_entry0_sat_l hZF.1, td_step_sat_l hZF,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]
  rfl

/-- 最后一步检查的存在证书由实际追加图唯一确定。 -/
theorem Td_check_d.end_l {p : Tg_params_d M.Domain} {X i h t a : M.Domain}
    (check : Td_check_d hZF p X t) (fn : Fn0_d i X h) (endt : Fseq_end_d I p.ω t h a) :
    Td_step_d hZF p i h a := by
  obtain ⟨m, i', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fn).2.1
  subst i'
  rcases check with empty | ⟨k, j, h', a', _, succ, ft, rest, value, step⟩
  · exact (d.last_value.elim fun q hq => empty q hq.2).elim
  · have eq := d.source.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) ft).2.1
    subst m
    have eq := d.length_successor.predecessor_eq hZF.1 d.prefix_sequence.2.1 succ
    subst k
    have eh := rest.eq hZF.1 d.prefix_restriction
    have ea := d.source.2.2.1.2 i a' a value d.last_value
    exact eh ▸ ea ▸ step

theorem td_check_end_l {p : Tg_params_d M.Domain} {X i j h t a : M.Domain}
    (hj : M.mem j p.ω) (succ : M.SuccessorOf j i) (fn : Fn0_d j X t)
    (fh : Fn0_d i X h) (endt : Fseq_end_d I p.ω t h a) (step : Td_step_d hZF p i h a) :
    Td_check_d hZF p X t := by
  obtain ⟨m, i', d⟩ := endt
  have eq := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fh).2.1
  subst i'
  exact Or.inr ⟨i, j, h, a, hj, succ, fn, d.prefix_restriction, d.last_value, step⟩

def Td_histories_d (p : Tg_params_d M.Domain) (X F L : M.Domain) : Prop :=
  Fseq_space_d I p.ω X F ∧ ∀ f, M.mem f L ↔ M.mem f F ∧ Td_check_d hZF p X f

/-- 全体历史与逐步合法集合均存在于原模型中；原公式只使用十二个固定参数。 -/
theorem td_histories_l (p : Tg_params_d M.Domain) {X : M.Domain} (hω : M.IsOmega p.ω) :
    ∃ F L, Td_histories_d hZF p X F L := by
  obtain ⟨F, space⟩ := ZF.fseq_space_exists_l I hZF hω X
  let ρ : Env M 13 := ⟨Fin.cases X (Fin.cases p.Q (Fin.cases p.P (Fin.cases p.E (Fin.cases p.ν
    (Fin.cases p.S (Fin.cases p.A (Fin.cases p.δ (Fin.cases p.c (Fin.cases p.b (Fin.cases p.a
      (Fin.cases p.e (fun _ => p.ω)))))))))))), fun _ => p.ω⟩
  let q : Tg_params_d (Term 14) := ⟨.bound 13, .bound 12, .bound 11, .bound 10, .bound 9, .bound 8,
    .bound 7, .bound 6, .bound 5, .bound 4, .bound 3, .bound 2⟩
  let φ : UnarySchema 13 := {
    body := td_check_m q (.bound 1) .newest
    freeClosed := by
      exact td_check_closed_l q _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl }
  obtain ⟨L, sep⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨F, L, space, fun f => (sep f).trans (and_congr Iff.rfl ?_)⟩
  exact td_check_sat_l hZF (ρ.push f) q (.bound 1) .newest

end YesMetaZFC.SetTheory.LargeCardinal

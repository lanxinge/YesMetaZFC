import YesMetaZFC.SetTheory.LargeCardinal.Game.CatalogRead
import YesMetaZFC.SetTheory.LargeCardinal.Game.DigitsImage
import YesMetaZFC.Model.SetTheory.Types.SubtypeReflect
import YesMetaZFC.Model.SetTheory.Types.DropEmbedding
import YesMetaZFC.Model.SetTheory.Relations.NativeSmemSlice
import YesMetaZFC.Model.SetTheory.Relations.OmegaCut

/-! # 辅助类型游戏的固定参数

十二个参数分别是内部时钟、树和字母表、重置高度及三张实际代码表。
参数记录只组织已构造的数据；有限历史仍以模型自己的函数图表示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u v

structure Tg_params_d (α : Type u) where
  ω : α
  e : α
  a : α
  b : α
  c : α
  δ : α
  A : α
  S : α
  ν : α
  E : α
  P : α
  Q : α

def Tg_params_d.map_l {α : Type u} {β : Type v} (p : Tg_params_d α) (f : α → β) : Tg_params_d β :=
  ⟨f p.ω, f p.e, f p.a, f p.b, f p.c, f p.δ, f p.A, f p.S, f p.ν, f p.E, f p.P, f p.Q⟩

def Tg_params_d.closed_l {d} (p : Tg_params_d (Term d)) : Prop :=
  p.ω.freeSupport = [] ∧ p.e.freeSupport = [] ∧ p.a.freeSupport = [] ∧ p.b.freeSupport = [] ∧
  p.c.freeSupport = [] ∧ p.δ.freeSupport = [] ∧ p.A.freeSupport = [] ∧ p.S.freeSupport = [] ∧
  p.ν.freeSupport = [] ∧ p.E.freeSupport = [] ∧ p.P.freeSupport = [] ∧ p.Q.freeSupport = []

@[simp] theorem Tg_params_d.weaken_closed_l {d} (p : Tg_params_d (Term d)) (h : p.closed_l) :
    (p.map_l Term.weaken).closed_l := by
  simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using h

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 规则 (4)–(6)：域增长、重置与较早轮的继续

较早轮通过三阶段历史中的原位置读取。继续分支明确要求 tℓ=pred(t)，
并按原方向检查新 u 超过旧 w；重置分支要求原树和固定低不可分辨点的完整类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_reset_d (ω e δ S ν l n U D u : M.Domain) : Prop := ∃ η Y c R s,
  M.SuccessorOf η ν ∧ V_d I η Y ∧ Smem_d I c Y R ∧ Tt_realized_d I ω c Y R n s δ U D u ∧
    Rd_entry_d e S s ∧ Rd_entry_d l ν s

def tg_reset_m {d} (ω e δ S ν l n U D u : Term d) : Formula 1 d := set[d] ⟪∃ η Y c R s,
  ⌜Formula.isSuccessor⌝ₚ(η, ⌜ν⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(η, Y) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, c, Y, R, ⌜n⌝ₛ, s, ⌜δ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, ⌜S⌝ₛ, s) ∧ ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜ν⌝ₛ, s)⟫
derive_free_closed tg_reset_m

theorem tg_reset_sat_l {d} (ρ : Env M d) (ω e δ S ν l n U D u : Term d) :
    Formula.satisfies ρ (tg_reset_m ω e δ S ν l n U D u) ↔ Tg_reset_d hZF
      (ω.eval ρ) (e.eval ρ) (δ.eval ρ) (S.eval ρ) (ν.eval ρ) (l.eval ρ) (n.eval ρ) (U.eval ρ) (D.eval ρ) (u.eval ρ) := by
  simp only [tg_reset_m, Tg_reset_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, v_sat_l I hZF.1, smem_sat_l I, tt_realized_sat_l I (ZF.modelsKP hZF),
    rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def Tg_growth_d (e c A n h κ B : M.Domain) : Prop :=
  (n = e ∧ M.mem A B) ∨ ∃ j a ℓ t τ u, M.SuccessorOf n j ∧ Tg_event_d I c j e h a ∧
    Tg_aux_data_d a ℓ t τ u ∧ M.mem τ κ

def tg_growth_m {d} (e c A n h κ B : Term d) : Formula 1 d := set[d] ⟪
  (⌜n⌝ₛ = ⌜e⌝ₛ ∧ ⌜A⌝ₛ ∈ ⌜B⌝ₛ) ∨ (∃ j a ℓ t τ u,
    ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ, j) ∧ ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, j, ⌜e⌝ₛ, ⌜h⌝ₛ, a) ∧
    ⌜tg_aux_data_m⌝ₚ(a, ℓ, t, τ, u) ∧ τ ∈ ⌜κ⌝ₛ)⟫
derive_free_closed tg_growth_m

theorem tg_growth_sat_l {d} (ρ : Env M d) (e c A n h κ B : Term d) :
    Formula.satisfies ρ (tg_growth_m e c A n h κ B) ↔
      Tg_growth_d hZF (e.eval ρ) (c.eval ρ) (A.eval ρ) (n.eval ρ) (h.eval ρ) (κ.eval ρ) (B.eval ρ) := by
  simp only [tg_growth_m, Tg_growth_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hZF.1, tg_aux_data_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def Tg_continue_d (ω e a c δ n h ℓ t κ k N U D u : M.Domain) : Prop :=
  M.mem ℓ n ∧ ∃ v w ℓ₀ t₀ κ₀ u₀ τ T j l m B V W,
    Tg_event_d I c ℓ e h v ∧ Tg_aux_data_d v ℓ₀ t₀ κ₀ u₀ ∧ Tg_event_d I c ℓ a h w ∧ KPair_d M w τ T ∧
    Fn0_d j ω t₀ ∧ M.SuccessorOf k j ∧ M.IsRestrictionOf I t₀ t j ∧ M.SuccessorOf l j ∧ M.SuccessorOf m l ∧
    M.IsLimitOrdinal τ ∧ V_d I τ B ∧ (∀ x, M.mem x V ↔ M.mem x B ∨ x = τ) ∧ Tt_pool_d I ω m V W ∧
    Tx_exceeds_d hZF ω δ τ m V W T κ N U D u

def tg_continue0_m : Formula 1 15 :=
  let ω : Term 15 := .bound 0; let e : Term 15 := .bound 1; let a : Term 15 := .bound 2
  let c : Term 15 := .bound 3; let δ : Term 15 := .bound 4; let n : Term 15 := .bound 5
  let h : Term 15 := .bound 6; let ℓ : Term 15 := .bound 7; let t : Term 15 := .bound 8
  let κ : Term 15 := .bound 9; let k : Term 15 := .bound 10; let N : Term 15 := .bound 11
  let U : Term 15 := .bound 12; let D : Term 15 := .bound 13; let u : Term 15 := .bound 14
  set[15] ⟪⌜ℓ⌝ₛ ∈ ⌜n⌝ₛ ∧
  (∃ v w ℓ₀ t₀ κ₀ u₀ τ T j l m B V W,
    ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, ⌜ℓ⌝ₛ, ⌜e⌝ₛ, ⌜h⌝ₛ, v) ∧ ⌜tg_aux_data_m⌝ₚ(v, ℓ₀, t₀, κ₀, u₀) ∧
    ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, ⌜ℓ⌝ₛ, ⌜a⌝ₛ, ⌜h⌝ₛ, w) ∧ ⌜kpair0_m⌝ₚ(w, τ, T) ∧
    ⌜fn0_m⌝ₚ(j, ⌜ω⌝ₛ, t₀) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜k⌝ₛ, j) ∧
    ⌜Formula.isRestriction kpair_convention_l⌝ₚ(t₀, ⌜t⌝ₛ, j) ∧
    ⌜Formula.isSuccessor⌝ₚ(l, j) ∧ ⌜Formula.isSuccessor⌝ₚ(m, l) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(τ) ∧
    ⌜v_sigma_m⌝ₚ(τ, B) ∧ ⌜tt_constants0_m⌝ₚ(τ, B, V) ∧ ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, m, V, W) ∧
    ⌜tx_exceeds_m⌝ₚ(⌜ω⌝ₛ, ⌜δ⌝ₛ, τ, m, V, W, T, ⌜κ⌝ₛ, ⌜N⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ))⟫
theorem tg_continue0_closed_l : tg_continue0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_continue0_m, Definitional.Formula.FreeClosed]

def tg_continue_m {d} (ω e a c δ n h ℓ t κ k N U D u : Term d) : Formula 1 d :=
  tg_continue0_m.bind (fun i => [ω, e, a, c, δ, n, h, ℓ, t, κ, k, N, U, D, u].get i)

@[simp] theorem tg_continue_m_freeClosed {d} (ω e a c δ n h ℓ t κ k N U D u : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (ha : a.freeSupport = [])
    (hc : c.freeSupport = []) (hd : δ.freeSupport = []) (hn : n.freeSupport = [])
    (hh : h.freeSupport = []) (hl : ℓ.freeSupport = []) (ht : t.freeSupport = [])
    (hk : κ.freeSupport = []) (hj : k.freeSupport = []) (hN : N.freeSupport = [])
    (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hu : u.freeSupport = []) :
    (tg_continue_m ω e a c δ n h ℓ t κ k N U D u).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_continue0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, he, ha, hc, hd, hn, hh, hl, ht, hk, hj, hN, hU, hD, hu, fun i => Fin.elim0 i⟩

theorem tg_continue_sat_l {d} (ρ : Env M d) (ω e a c δ n h ℓ t κ k N U D u : Term d) :
    Formula.satisfies ρ (tg_continue_m ω e a c δ n h ℓ t κ k N U D u) ↔ Tg_continue_d hZF
      (ω.eval ρ) (e.eval ρ) (a.eval ρ) (c.eval ρ) (δ.eval ρ) (n.eval ρ) (h.eval ρ) (ℓ.eval ρ) (t.eval ρ)
      (κ.eval ρ) (k.eval ρ) (N.eval ρ) (U.eval ρ) (D.eval ρ) (u.eval ρ) := by
  simp only [tg_continue_m, Formula.satisfies_bind, tg_continue0_m, Tg_continue_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, tg_event_sat_l I hZF.1, tg_aux_data_sat_l hZF.1, kpair0_sat_l hZF.1,
    fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_isLimitOrdinal_iff, v_sigma_sat_l (ZF.modelsKP hZF), tt_constants0_sat_l hZF.1,
    tt_pool_sat_l I (ZF.modelsKP hZF), tx_exceeds_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 第二方辅助走法：原规则 (2)–(6)

节点常量取自已经落下的实数前缀。dcp 弹性和节点条件均检查固定查询的
字面成员性；末位最大序数没有作为新规则加入，而留给原刚性引理推导。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_aux_d (p : Tg_params_d M.Domain) (n h v : M.Domain) : Prop :=
  ∃ ℓ t κ u k l N x s B U D r m b q f C V W g₀ g₁ g₂ g₃,
    Tg_aux_data_d v ℓ t κ u ∧ M.mem κ p.δ ∧ Fn0_d k p.ω t ∧ M.SuccessorOf l k ∧ M.SuccessorOf N l ∧
    Tg_digits_d hZF p.c p.b n p.A h x ∧ M.IsRestrictionOf I s x k ∧ Tg_query_request_d hZF p.ω κ k s t ∧
    Tg_query_data_d p.Q κ k s t B U D r m b q f ∧ M.MemberSubset u D ∧
    Tg_ee_data_d p.E κ l C V W ⟨g₀, g₁, g₂, g₃⟩ ∧ Tg_elastic_d I l N W ⟨g₀, g₁, g₂, g₃⟩ u ∧ M.mem f u ∧
    Tg_growth_d hZF p.e p.c p.A n h κ B ∧
    ((t = p.e ∧ Tg_reset_d hZF p.ω p.e p.δ p.S p.ν l N U D u) ∨
      (t ≠ p.e ∧ Tg_continue_d hZF p.ω p.e p.a p.c p.δ n h ℓ t κ k N U D u))

def tg_aux0_m : Formula 1 15 :=
  let p : Tg_params_d (Term 15) := ⟨.bound 0, .bound 1, .bound 2, .bound 3, .bound 4, .bound 5,
    .bound 6, .bound 7, .bound 8, .bound 9, .bound 10, .bound 11⟩
  let n : Term 15 := .bound 12; let h : Term 15 := .bound 13; let v : Term 15 := .bound 14
  set[15] ⟪
  ∃ ℓ t κ u k l N x s B U D r m b q f C V W g₀ g₁ g₂ g₃,
  ⌜tg_aux_data_m⌝ₚ(⌜v⌝ₛ, ℓ, t, κ, u) ∧ κ ∈ ⌜p.δ⌝ₛ ∧ ⌜fn0_m⌝ₚ(k, ⌜p.ω⌝ₛ, t) ∧
  ⌜Formula.isSuccessor⌝ₚ(l, k) ∧ ⌜Formula.isSuccessor⌝ₚ(N, l) ∧
  ⌜tg_digits_m⌝ₚ(⌜p.c⌝ₛ, ⌜p.b⌝ₛ, ⌜n⌝ₛ, ⌜p.A⌝ₛ, ⌜h⌝ₛ, x) ∧
  ⌜Formula.isRestriction kpair_convention_l⌝ₚ(s, x, k) ∧ ⌜tg_query_request_m⌝ₚ(⌜p.ω⌝ₛ, κ, k, s, t) ∧
  ⌜tg_query_data_m⌝ₚ(⌜p.Q⌝ₛ, κ, k, s, t, B, U, D, r, m, b, q, f) ∧ u ⊆ D ∧
  ⌜tg_ee_data_m⌝ₚ(⌜p.E⌝ₛ, κ, l, C, V, W, g₀, g₁, g₂, g₃) ∧ ⌜tg_elastic_m⌝ₚ(l, N, W, g₀, g₁, g₂, g₃, u) ∧ f ∈ u ∧
  ⌜tg_growth_m⌝ₚ(⌜p.e⌝ₛ, ⌜p.c⌝ₛ, ⌜p.A⌝ₛ, ⌜n⌝ₛ, ⌜h⌝ₛ, κ, B) ∧
  ((t = ⌜p.e⌝ₛ ∧ ⌜tg_reset_m⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.δ⌝ₛ, ⌜p.S⌝ₛ, ⌜p.ν⌝ₛ, l, N, U, D, u)) ∨
    (¬ (t = ⌜p.e⌝ₛ) ∧ ⌜tg_continue_m⌝ₚ(⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.a⌝ₛ, ⌜p.c⌝ₛ, ⌜p.δ⌝ₛ,
      ⌜n⌝ₛ, ⌜h⌝ₛ, ℓ, t, κ, k, N, U, D, u)))⟫

theorem tg_aux0_closed_l : tg_aux0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_aux0_m, Definitional.Formula.FreeClosed]

def tg_aux_m {d} (p : Tg_params_d (Term d)) (n h v : Term d) : Formula 1 d :=
  tg_aux0_m.bind (fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, n, h, v].get i)

@[simp] theorem tg_aux_closed_l {d} (p : Tg_params_d (Term d)) (n h v : Term d)
    (hp : p.closed_l) (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (tg_aux_m p n h v).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_aux0_closed_l
  rcases hp with ⟨hω, he, ha, hb, hc, hδ, hA, hS, hν, hE, hP, hQ⟩
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, he, ha, hb, hc, hδ, hA, hS, hν, hE, hP, hQ, hn, hh, hv, fun i => Fin.elim0 i⟩

theorem tg_aux_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (n h v : Term d) :
    Formula.satisfies ρ (tg_aux_m p n h v) ↔ Tg_aux_d hZF (p.map_l (fun t => t.eval ρ)) (n.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [tg_aux_m, Formula.satisfies_bind, tg_aux0_m, Tg_aux_d, Tg_params_d.map_l, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_aux_data_sat_l hZF.1, Formula.satisfies_mem_iff, fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff,
    tg_digits_sat_l hZF, Formula.satisfies_isRestriction_iff I, tg_query_request_sat_l hZF,
    tg_query_data_sat_l hZF.1, Formula.satisfies_subset_iff, tg_ee_data_sat_l hZF.1, tg_elastic_sat_l I hZF.1,
    tg_growth_sat_l hZF, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    tg_reset_sat_l hZF, Formula.satisfies_neg_iff, tg_continue_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 玩家 I 的回答：原规则 (7) 及唯一新增的空根条件

回答读取固定的子类型程序、源 dcp 查询域及目标端点查询。这里没有把
可实现性列为额外规则；原定义的子类型查询为真时，已有读取定理自行恢复实际实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def tg_reply0_m : Formula 1 22 :=
  let ω := Term.bound 0; let l := Term.bound 1; let n := Term.bound 2; let κ := Term.bound 3
  let τ := Term.bound 4; let U := Term.bound 5; let D := Term.bound 6; let W := Term.bound 7
  let u := Term.bound 8; let w := Term.bound 9; let b := Term.bound 10; let z := Term.bound 11
  let r := Term.bound 12; let q := Term.bound 13; let h := Term.bound 14
  let σ : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  .conj (Formula.subset w W) (.existsE (.conj (td_dcp_m l.weaken n.weaken D.weaken u.weaken .newest)
    (.conj (ts_subtype_m ω.weaken l.weaken κ.weaken τ.weaken n.weaken U.weaken w.weaken b.weaken z.weaken .newest
      (fun j => (σ j).weaken)) (.conj (.mem r.weaken w.weaken) (.conj (.mem q.weaken w.weaken) (.mem h.weaken w.weaken))))))

theorem tg_reply0_closed_l : tg_reply0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reply0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]

def tg_reply_m {d} (ω l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  tg_reply0_m.bind (fun i => [ω, l, n, κ, τ, U, D, W, u, w, b, z, r, q, h,
    σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)

@[simp] theorem tg_reply_closed_l {d} (ω l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hl : l.freeSupport = []) (hn : n.freeSupport = []) (hk : κ.freeSupport = [])
    (ht : τ.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hW : W.freeSupport = [])
    (hu : u.freeSupport = []) (hv : w.freeSupport = []) (hb : b.freeSupport = []) (hz : z.freeSupport = [])
    (hr : r.freeSupport = []) (hq : q.freeSupport = []) (hh : h.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (tg_reply_m ω l n κ τ U D W u w b z r q h σ).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_reply0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hl, hn, hk, ht, hU, hD, hW, hu, hv, hb, hz, hr, hq, hh,
    hσ 0, hσ 1, hσ 2, hσ 3, hσ 4, hσ 5, hσ 6, fun i => Fin.elim0 i⟩

section ReplyRead
variable (hKP : M.Models KP)
local notation "J" => kp_pair_l hKP

theorem tg_reply_sat_l {d} (ρ : Env M d) (ω l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (tg_reply_m ω l n κ τ U D W u w b z r q h σ) ↔ Tg_reply_d J
      (ω.eval ρ) (l.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (U.eval ρ) (D.eval ρ) (W.eval ρ)
      (u.eval ρ) (w.eval ρ) (b.eval ρ) (fun j => (σ j).eval ρ) (z.eval ρ) ⟨r.eval ρ, q.eval ρ, h.eval ρ⟩ := by
  simp only [tg_reply_m, Formula.satisfies_bind, tg_reply0_m, Tg_reply_d,
    Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff, td_dcp_sat_l J hKP.1, ts_subtype_sat_l hKP,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  have eq : (fun i => (Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
      (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21)))))) i : Term 22).eval
      (Definitional.Env.substitute ρ (fun i => [ω, l, n, κ, τ, U, D, W, u, w, b, z, r, q, h,
        σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i))) = (fun i => (σ i).eval ρ) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  rw [eq]
  rfl
end ReplyRead

def Tg_answer_d (p : Tg_params_d M.Domain) (n h v : M.Domain) : Prop :=
  ∃ a ℓ t κ u τ w k l N B U D g₀ g₁ g₂ g₃ C V W r m q f j b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    Tg_event_d I p.c n p.e h a ∧ Tg_aux_data_d a ℓ t κ u ∧ KPair_d M v τ w ∧
    Fn0_d k p.ω t ∧ M.SuccessorOf l k ∧ M.SuccessorOf N l ∧
    Tg_ee_data_d p.E κ l B U D ⟨g₀, g₁, g₂, g₃⟩ ∧ M.mem τ p.δ ∧ Tg_query_request_d hZF p.ω τ k p.e p.e ∧
    Tg_query_data_d p.Q τ k p.e p.e C V W r m q f j ∧
    Tg_program_data_d p.P l b z (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃
      (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆))))))) ∧
    Tg_reply_d I p.ω l N κ τ U D W u w b (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂
      (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆))))))) z ⟨r, q, f⟩

def tg_answer0_m : Formula 1 15 :=
  let p : Tg_params_d (Term 15) := ⟨.bound 0, .bound 1, .bound 2, .bound 3, .bound 4, .bound 5,
    .bound 6, .bound 7, .bound 8, .bound 9, .bound 10, .bound 11⟩
  let n := Term.bound 12; let h := Term.bound 13; let v := Term.bound 14
  set[15] ⟪
  ∃ a ℓ t κ u τ w k l N B U D g₀ g₁ g₂ g₃ C V W r m q f j b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
  ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, ⌜n⌝ₛ, ⌜p.e⌝ₛ, ⌜h⌝ₛ, a) ∧ ⌜tg_aux_data_m⌝ₚ(a, ℓ, t, κ, u) ∧ ⌜kpair0_m⌝ₚ(⌜v⌝ₛ, τ, w) ∧
  ⌜fn0_m⌝ₚ(k, ⌜p.ω⌝ₛ, t) ∧ ⌜Formula.isSuccessor⌝ₚ(l, k) ∧ ⌜Formula.isSuccessor⌝ₚ(N, l) ∧
  ⌜tg_ee_data_m⌝ₚ(⌜p.E⌝ₛ, κ, l, B, U, D, g₀, g₁, g₂, g₃) ∧ τ ∈ ⌜p.δ⌝ₛ ∧
  ⌜tg_query_request_m⌝ₚ(⌜p.ω⌝ₛ, τ, k, ⌜p.e⌝ₛ, ⌜p.e⌝ₛ) ∧ ⌜tg_query_data_m⌝ₚ(⌜p.Q⌝ₛ, τ, k, ⌜p.e⌝ₛ, ⌜p.e⌝ₛ, C, V, W, r, m, q, f, j) ∧
  ⌜fun P l b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P l b z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜p.P⌝ₛ, l, b, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆) ∧
  ⌜fun ω l N κ τ U D W u w b z r q f s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_reply_m ω l N κ τ U D W u w b z r q f
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜p.ω⌝ₛ, l, N, κ, τ, U, D, W, u, w, b, z, r, q, f, s₀, s₁, s₂, s₃, s₄, s₅, s₆)⟫

@[simp] theorem tg_answer0_closed_l : tg_answer0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_answer0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]

def tg_answer_m {d} (p : Tg_params_d (Term d)) (n h v : Term d) : Formula 1 d :=
  tg_answer0_m.bind (fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, n, h, v].get i)

@[simp] theorem tg_answer_closed_l {d} (p : Tg_params_d (Term d)) (n h v : Term d)
    (hp : p.closed_l) (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (tg_answer_m p n h v).FreeClosed := by
  rcases hp with ⟨hω, he, ha, hb, hc, hδ, hA, hS, hν, hE, hP, hQ⟩
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_answer0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, he, ha, hb, hc, hδ, hA, hS, hν, hE, hP, hQ, hn, hh, hv, fun i => Fin.elim0 i⟩

theorem tg_answer_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (n h v : Term d) :
    Formula.satisfies ρ (tg_answer_m p n h v) ↔ Tg_answer_d hZF (p.map_l (fun t => t.eval ρ)) (n.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [tg_answer_m, Formula.satisfies_bind, tg_answer0_m, Tg_answer_d, Tg_params_d.map_l,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_event_sat_l I hZF.1, tg_aux_data_sat_l hZF.1, kpair0_sat_l hZF.1, fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff,
    tg_ee_data_sat_l hZF.1, Formula.satisfies_mem_iff, tg_query_request_sat_l hZF, tg_query_data_sat_l hZF.1,
    tg_program_data_sat_l hZF.1, tg_reply_sat_l (ZF.modelsKP hZF), tt_eval_cases_l, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 规则 (7) 从证书层读取为实际回答

原 dcp 由传递性和配对闭包绝对读取，子类型沿原存在见证向上读取。
所得回答仍是相同类型集合和相同查询码的字面成员判断。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
  (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
local notation "N" => rt_model_l X nx
include hX pair

theorem tg_reply_source_l {d} (ρ : Env N d) (ω l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d)
    (valid : Formula.satisfies ρ (tg_reply_m ω l n κ τ U D W u w b z r q h σ)) :
    Tg_reply_d (kp_pair_l hKP) (ω.eval ρ).val (l.eval ρ).val (n.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val
      (U.eval ρ).val (D.eval ρ).val (W.eval ρ).val (u.eval ρ).val (w.eval ρ).val (b.eval ρ).val
      (fun i => (σ i).eval ρ |>.val) (z.eval ρ).val ⟨(r.eval ρ).val, (q.eval ρ).val, (h.eval ρ).val⟩ := by
  let ε := Definitional.Env.substitute ρ (fun i => [ω, l, n, κ, τ, U, D, W, u, w, b, z, r, q, h,
    σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)
  let s : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  simp only [tg_reply_m, Formula.satisfies_bind, tg_reply0_m, Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken] at valid
  obtain ⟨sub, v, drop, code, root, bound, height⟩ := valid
  have subset : M.MemberSubset (w.eval ρ).val (W.eval ρ).val :=
    fun x hx => sub ⟨x, hX (w.eval ρ).val (w.eval ρ).property x hx⟩ hx
  have drop := (td_dcp_source_l hKP.1 (KP.exists_pair hKP) hX nx pair _ _ _ _ _ _).mp drop
  have code := ts_subtype_source_l hKP hX nx _ _ _ _ _ _ _ _ _ _ _ _ code
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at drop code
  have eq : (fun i => (s i).eval ε |>.val) = (fun i => (σ i).eval ρ |>.val) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have code : Ts_subtype_d (ω.eval ρ).val (l.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val
      (n.eval ρ).val (U.eval ρ).val (w.eval ρ).val (b.eval ρ).val (fun i => (s i).eval ε |>.val)
      (z.eval ρ).val v.val := code
  exact ⟨subset, v.val, drop, eq ▸ code, root, bound, height⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整回答沿同一个代表池进入实际原后继

完整值域与前驱图先搬运配对闭包，再搬运规则 (7) 的全部量词。
目标在自己的原关系中读出完整回答，不对原载体增加传递性或外部良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 请求的元数、临界点、两份域、类型及完整程序对应回答的同一批坐标。 -/
def Tg_reply_link_d {α β : Type u} (r : α → β → Prop) (v : Fin 46 → α) (p : Fin 22 → β) : Prop :=
  ∀ i : Fin 16, r (v ([0,27,28,24,30,31,25,36,37,38,39,40,41,42,43,44].get i))
    (p ([0,1,2,3,5,6,8,10,11,15,16,17,18,19,20,21].get i))

theorem tg_reply_raw_image_l {N R P S Γ t : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y P)
    (hP : (smdl_structure_l I (R := S) ny).Models KP)
    (B : (smdl_structure_l I (R := R) nx).Domain)
    (H : (smdl_structure_l I (R := S) ny).Domain)
    (pair : ∀ a b, (smdl_structure_l I (R := R) nx).mem a B →
      (smdl_structure_l I (R := R) nx).mem b B →
      ∃ p, (smdl_structure_l I (R := R) nx).mem p B ∧ Pair_d (smdl_structure_l I (R := R) nx) p a b)
    (nb : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x B})
    (ρ : Env (rt_model_l B nb) 22) (reply : Formula.satisfies ρ tg_reply0_m)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x B.val R)
    (ft : M.IsSetInjectionFromTo I t Γ P)
    (image : ∀ E, M.PairMember I E H.val S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x E t)
    (pred : ∀ x E, M.PairMember I x E t → ∀ y,
      M.PairMember I y E S ↔ ∃ a, M.PairMember I a x R ∧ M.PairMember I a y t) :
    ∃ η : Env (smdl_structure_l I (R := S) ny) 22,
      (∀ i, M.PairMember I (ρ.bound i).val.val (η.bound i).val t) ∧ Formula.satisfies η tg_reply0_m := by
  let P₀ := smdl_structure_l I (R := S) ny
  obtain ⟨ht,pairs⟩ := rr_native_pair_l I nx ny B H pair carrier ft image pred
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice (fun i : Fin 22 => ft.1.2.2 (ρ.bound i).val.val
    ((carrier _).mpr ⟨(ρ.bound i).val.property, (ρ.bound i).property⟩))
  have vh i : P₀.mem ⟨v i, (hv i).1⟩ H :=
    (image (v i)).mpr ⟨_, ft.1.input_mem_of_pairMember (hv i).2, (hv i).2⟩
  let nh : Nonempty {x : P₀.Domain // P₀.mem x H} := ⟨⟨⟨v 0, (hv 0).1⟩, vh 0⟩⟩
  let ε : Env (rt_model_l H nh) 22 :=
    ⟨fun i => ⟨⟨v i, (hv i).1⟩, vh i⟩, fun _ => ⟨⟨v 0, (hv 0).1⟩, vh 0⟩⟩
  have transferred := (rr_native_slice_l I nx ny B H nb nh carrier ft image pred
    tg_reply0_m tg_reply0_closed_l ρ ε (fun i => (hv i).2)).mp reply
  let slots : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  have actual := tg_reply_source_l hP ht nh pairs ε (.bound 0) (.bound 1) (.bound 2)
    (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9)
    (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) slots transferred
  let η := image_env_l Subtype.val ε
  refine ⟨η, fun i => (hv i).2, ?_⟩
  apply (tg_reply_sat_l hP η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11)
    (.bound 12) (.bound 13) (.bound 14) slots).mpr
  simpa only [η, @eval_image_env_l (rt_model_l H nh) P₀ Subtype.val] using actual

end YesMetaZFC.SetTheory.LargeCardinal

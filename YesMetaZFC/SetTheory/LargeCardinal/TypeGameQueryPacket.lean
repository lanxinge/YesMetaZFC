import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReply
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryBase
import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticCatalog

/-! # 一轮所需的固定节点与端点查询包

参数是 κ、历史长度 k 及两张已有坐标图。完整类型的元数为 k+2，
节点查询与根、末位、严格秩界及末位加二查询先在共同低参数基底构造，
再延伸到完整常量域；表项同时保留这份与 κ 无关的原查询证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_reply_language0_m : Formula 1 11 :=
  let ω := Term.bound 0; let e := Term.bound 1; let l := Term.bound 2; let n := Term.bound 3
  let κ := Term.bound 4; let B := Term.bound 5; let U := Term.bound 6; let D := Term.bound 7
  let r := Term.bound 8; let b := Term.bound 9; let h := Term.bound 10
  set[11] ⟪
  ⌜n⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜e⌝ₛ ∈ ⌜n⌝ₛ ∧ ⌜l⌝ₛ ∈ ⌜n⌝ₛ ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜κ⌝ₛ) ∧
  ⌜v_sigma_m⌝ₚ(⌜κ⌝ₛ, ⌜B⌝ₛ) ∧ ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ, ⌜B⌝ₛ, ⌜U⌝ₛ) ∧
  ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ) ∧
  ⌜tg_root_query_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜r⌝ₛ) ∧
  ⌜tg_bound_query_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜b⌝ₛ) ∧
  ⌜tg_height_query_m⌝ₚ(⌜ω⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜h⌝ₛ) ∧
  ⌜tg_reply_base_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, ⌜b⌝ₛ, ⌜h⌝ₛ)⟫

@[simp] theorem tg_reply_language0_closed_l : tg_reply_language0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reply_language0_m, Definitional.Formula.FreeClosed]

def tg_reply_language_m {d} (ω e l n κ B U D r b h : Term d) : Formula 1 d :=
  tg_reply_language0_m.bind (fun i => [ω, e, l, n, κ, B, U, D, r, b, h].get i)

@[simp] theorem tg_reply_language_m_freeClosed {d} (ω e l n κ B U D r b h : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hl : l.freeSupport = []) (hn : n.freeSupport = [])
    (hk : κ.freeSupport = []) (hB : B.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = [])
    (hr : r.freeSupport = []) (hb : b.freeSupport = []) (hh : h.freeSupport = []) :
    (tg_reply_language_m ω e l n κ B U D r b h).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_reply_language0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, he, hl, hn, hk, hB, hU, hD, hr, hb, hh, fun i => Fin.elim0 i⟩

theorem tg_reply_language_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω e l n κ B U D r b h : Term d) :
    Formula.satisfies ρ (tg_reply_language_m ω e l n κ B U D r b h) ↔ Tg_reply_language_d hZF
      (ω.eval ρ) (e.eval ρ) (l.eval ρ) (n.eval ρ) (κ.eval ρ) (B.eval ρ) (U.eval ρ) (D.eval ρ)
      ⟨r.eval ρ, b.eval ρ, h.eval ρ⟩ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [tg_reply_language_m, Formula.satisfies_bind, tg_reply_language0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isLimitOrdinal_iff, v_sigma_sat_l (ZF.modelsKP hZF), tt_constants0_sat_l hZF.1,
    tt_pool_sat_l I (ZF.modelsKP hZF), tg_root_query_sat_l I (ZF.modelsKP hZF),
    tg_bound_query_sat_l I (ZF.modelsKP hZF), tg_height_query_sat_l I (ZF.modelsKP hZF), tg_reply_base_sat_l I (ZF.modelsKP hZF)]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
    fun p => ⟨p.finite, p.root_slot, p.last_slot, p.limit, p.rank, p.constants, p.pool, p.root, p.bound, p.height, p.base⟩⟩

def Tg_query_request_d (hZF : M.Models ZF) (ω κ k s t : M.Domain) : Prop :=
  M.IsLimitOrdinal κ ∧ M.mem k ω ∧ ∃ B U, V_d (kp_pair_l (ZF.modelsKP hZF)) κ B ∧
    (∀ x, M.mem x U ↔ M.mem x B ∨ x = κ) ∧ M.mem s U ∧ M.mem t U

def tg_query_request0_m : Formula 1 5 :=
  let ω := Term.bound 0; let κ := Term.bound 1; let k := Term.bound 2
  let s := Term.bound 3; let t := Term.bound 4
  set[5] ⟪
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜κ⌝ₛ) ∧ ⌜k⌝ₛ ∈ ⌜ω⌝ₛ ∧ (∃ B U,
    ⌜v_sigma_m⌝ₚ(⌜κ⌝ₛ, B) ∧ ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ, B, U) ∧ ⌜s⌝ₛ ∈ U ∧ ⌜t⌝ₛ ∈ U)⟫

@[simp] theorem tg_query_request0_closed_l : tg_query_request0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_query_request0_m, Definitional.Formula.FreeClosed]

def tg_query_request_m {d} (ω κ k s t : Term d) : Formula 1 d :=
  tg_query_request0_m.bind (fun i => [ω, κ, k, s, t].get i)

@[simp] theorem tg_query_request_m_freeClosed {d} (ω κ k s t : Term d)
    (hw : ω.freeSupport = []) (hk : κ.freeSupport = []) (hn : k.freeSupport = [])
    (hs : s.freeSupport = []) (ht : t.freeSupport = []) : (tg_query_request_m ω κ k s t).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_query_request0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hk, hn, hs, ht, fun i => Fin.elim0 i⟩

theorem tg_query_request_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω κ k s t : Term d) :
    Formula.satisfies ρ (tg_query_request_m ω κ k s t) ↔
      Tg_query_request_d hZF (ω.eval ρ) (κ.eval ρ) (k.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [tg_query_request_m, Formula.satisfies_bind, tg_query_request0_m, Tg_query_request_d,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_exists_iff, v_sigma_sat_l (ZF.modelsKP hZF),
    tt_constants0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

def Tg_query_packet_d (hZF : M.Models ZF) (ω e κ k s t c : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ l n B U D r m b h q p a, M.SuccessorOf l k ∧ M.SuccessorOf n l ∧
    Rd_quad_d c B U D p ∧ Rd_quad_d p r m b a ∧ KPair_d M a h q ∧
    Tg_reply_language_d hZF ω e l n κ B U D ⟨r, b, h⟩ ∧
    Tg_max_query_d I ω l n U D m ∧ Tg_node_query_d I ω e n l U D s t k q ∧
    Tg_query_base_d I ω e l n k s t r m b h q

def tg_query_packet_m {d} (ω e κ k s t c : Term d) : Formula 1 d := set[d] ⟪∃ l n B U D r m b h q p a,
  ⌜Formula.isSuccessor⌝ₚ(l, ⌜k⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(n, l) ∧
  ⌜rd_quad_m⌝ₚ(⌜c⌝ₛ, B, U, D, p) ∧ ⌜rd_quad_m⌝ₚ(p, r, m, b, a) ∧ ⌜kpair0_m⌝ₚ(a, h, q) ∧
  ⌜tg_reply_language_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, l, n, ⌜κ⌝ₛ, B, U, D, r, b, h) ∧
  ⌜tg_max_query_m⌝ₚ(⌜ω⌝ₛ, l, n, U, D, m) ∧ ⌜tg_node_query_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, n, l, U, D, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜k⌝ₛ, q) ∧
  ⌜tg_query_base_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, l, n, ⌜k⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ, r, m, b, h, q)⟫
derive_free_closed tg_query_packet_m

theorem tg_query_packet_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω e κ k s t c : Term d) :
    Formula.satisfies ρ (tg_query_packet_m ω e κ k s t c) ↔ Tg_query_packet_d hZF
      (ω.eval ρ) (e.eval ρ) (κ.eval ρ) (k.eval ρ) (s.eval ρ) (t.eval ρ) (c.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [tg_query_packet_m, Tg_query_packet_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, rd_quad_sat_l hZF.1, kpair0_sat_l hZF.1, tg_reply_language_sat_l hZF,
    tg_max_query_sat_l I (ZF.modelsKP hZF), tg_node_query_sat_l I (ZF.modelsKP hZF),
    tg_query_base_sat_l I (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  rfl

theorem tg_query_packet_exists_l (hZFC : M.Models ZFC) {ω e δ X κ k s t : M.Domain}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hk : M.mem κ δ)
    (request : Tg_query_request_d (ZFC.models_zf_l hZFC) ω κ k s t) :
    ∃ c, M.mem c X ∧ Tg_query_packet_d (ZFC.models_zf_l hZFC) ω e κ k s t c := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨limit, finite, B, U, rank, constants, hs, ht⟩ := request
  obtain ⟨l, next, hl⟩ := hω.1.2 k finite
  obtain ⟨n, last, hn⟩ := hω.1.2 l hl
  have hel := (hω.members_areOrdinals hZF l hl).empty_mem_of_nonempty (ZF.modelsKP hZF) ⟨k, next.predecessor_mem⟩ he
  have hen := (hω.members_areOrdinals hZF n hn).transitive l last.predecessor_mem e hel
  obtain ⟨D, pool⟩ := tt_pool_exists_l I hZF hω n U
  obtain ⟨r, m, b, h, a, base⟩ := tg_query_base_l hZF hω he hn last.predecessor_mem hel
  have nat := tt_constants_finite_l hZF hω finite limit rank constants
  obtain ⟨root, max, bound, height, node⟩ := base.scope_l I (ZF.modelsKP hZF) pool nat.1 hs ht nat.2
  let q : Tg_reply_queries_d M := ⟨r, b, h⟩
  have language : Tg_reply_language_d hZF ω e l n κ B U D q :=
    ⟨hn, hen, last.predecessor_mem, limit, rank, constants, pool, root, bound, height, base.2⟩
  have algebra := sc_v_algebra_l hZFC hδ hX
  have trans := ZF.v_transitive_l I hZF hX
  have hB := ZF.v_mem_l I hZF language.rank hX hk
  have hU := tt_constants_rank_l hZF hX hδ hk language.rank language.constants
  have hD := language.pool.rank_mem_l hZF hω hX hδ (ZF.v_ordinal_mem_l I hZF hX hwδ) hn hU
  have hwX := ZF.v_ordinal_mem_l I hZF hX hwδ
  obtain ⟨hr, hm, hb, hh, ha⟩ := base.rank_l hZF hω hX hδ hwX hn
    (trans U hU s hs) (trans U hU t ht) (trans ω hwX k finite)
  obtain ⟨v, hv, cv⟩ := algebra.kpair_l hh ha
  obtain ⟨p, hp, cp⟩ := sc_quad_l algebra hr hm hb hv
  obtain ⟨c, hc, cc⟩ := sc_quad_l algebra hB hU hD hp
  exact ⟨c, hc, l, n, B, U, D, q.root, m, q.bound, q.height, a, p, v,
    next, last, cc, cp, cv, language, max, node, base⟩

end YesMetaZFC.SetTheory.LargeCardinal

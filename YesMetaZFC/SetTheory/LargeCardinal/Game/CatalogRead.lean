import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyDescent
import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax

/-! # 只按元数固定的子类型程序表

程序包只存自然数长度、七个自然数槽位和自然数程序码。整张函数图包含于
Vω，κ、较低域及候选类型不参与程序选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_program_packet_d (hZF : M.Models ZF) (ω n r : M.Domain) : Prop :=
  ∃ b z p q s₀ s₁ s₂ s₃ s₄ s₅ s₆ a,
    Rd_quad_d r b z p q ∧ Rd_quad_d p s₀ s₁ s₂ s₃ ∧ Rd_triple_d q s₄ s₅ s₆ ∧
    Ts_program_d hZF ω n b (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂
      (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆))))))) a z

def tg_program_packet_m {d} (ω n r : Term d) : Formula 1 d := set[d] ⟪∃ b z p q s₀ s₁ s₂ s₃ s₄ s₅ s₆ a,
  ⌜rd_quad_m⌝ₚ(⌜r⌝ₛ, b, z, p, q) ∧ ⌜rd_quad_m⌝ₚ(p, s₀, s₁, s₂, s₃) ∧ ⌜rd_triple0_m⌝ₚ(q, s₄, s₅, s₆) ∧
  ⌜fun ω n b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω n b a z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜ω⌝ₛ, ⌜n⌝ₛ, b, a, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆)⟫
@[simp] theorem tg_program_packet_closed_l {d} (ω n r : Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hr : r.freeSupport = []) :
    (tg_program_packet_m ω n r).FreeClosed := by
  simp -implicitDefEqProofs [tg_program_packet_m, Definitional.Formula.FreeClosed, hw, hn, hr, Fin.forall_fin_succ]

theorem tg_program_packet_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω n r : Term d) :
    Formula.satisfies ρ (tg_program_packet_m ω n r) ↔
      Tg_program_packet_d hZF (ω.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [tg_program_packet_m, Tg_program_packet_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_quad_sat_l hZF.1, rd_triple0_sat_l hZF.1, ts_program_sat_l hZF, tt_eval_cases_l, Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_program_packet_exists_l {ω H n : M.Domain} (hω : M.IsOmega ω) (hH : V_d I ω H) (hn : M.mem n ω) :
    ∃ r, M.mem r H ∧ Tg_program_packet_d hZF ω n r := by
  obtain ⟨b, σ, a, z, prog⟩ := ts_program_l hZF hω hn
  have algebra := sc_v_algebra_l hZFC (hω.isLimitOrdinal (ZF.modelsKP hZF)) hH
  have bound j := ZF.v_ordinal_mem_l I hZF hH (hω.transitive (ZF.modelsKP hZF) b prog.length (σ j) (prog.slots j))
  obtain ⟨p, hp, cp⟩ := sc_quad_l algebra (bound 0) (bound 1) (bound 2) (bound 3)
  obtain ⟨q', hq', cq'⟩ := algebra.kpair_l (bound 5) (bound 6)
  obtain ⟨q, hq, cq⟩ := algebra.kpair_l (bound 4) hq'
  obtain ⟨r, hr, cr⟩ := sc_quad_l algebra (ZF.v_ordinal_mem_l I hZF hH prog.length)
    (ZF.v_ordinal_mem_l I hZF hH prog.natural) hp hq
  refine ⟨r, hr, b, z, p, q, σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6, a, cr, cp, ⟨q', cq', cq⟩, ?_⟩
  have eq : (Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
      (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6))))))) = σ := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) j
  rw [eq]
  exact prog

def Tg_program_catalog_d (ω H Γ : M.Domain) : Prop := Fn0_d ω H Γ ∧
  ∀ n r, Rd_entry_d n r Γ → Tg_program_packet_d hZF ω n r

theorem tg_program_catalog_l {ω : M.Domain} (hω : M.IsOmega ω) :
    ∃ H Γ, V_d I ω H ∧ Tg_program_catalog_d hZFC ω H Γ ∧ M.MemberSubset Γ H := by
  obtain ⟨H, hH⟩ := ZF.v_exists_l I hZF (hω.isOrdinal (ZF.modelsKP hZF))
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : BinarySchema 1 := { body := tg_program_packet_m (.bound 2) (.bound 1) .newest }
  have sat n r : φ.denote ρ n r ↔ Tg_program_packet_d hZF ω n r := tg_program_packet_sat_l hZF ..
  obtain ⟨Γ, fn, all⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := ω) (Y := H) (fun n hn => by
    obtain ⟨r, hr, packet⟩ := tg_program_packet_exists_l hZFC hω hH hn
    exact ⟨r, hr, (sat n r).mpr packet⟩)
  refine ⟨H, Γ, hH, ⟨fn0_of_function_l (ZF.modelsKP hZF) fn, fun n r hr => (sat n r).mp (all n r hr)⟩, ?_⟩
  intro p hp
  obtain ⟨n, r, pair⟩ := fn.1.1 p hp
  have entry : Rd_entry_d n r Γ := ⟨p, pair, hp⟩
  obtain ⟨p', hp', pair'⟩ := (sc_v_algebra_l hZFC (hω.isLimitOrdinal (ZF.modelsKP hZF)) hH).kpair_l
    (ZF.v_ordinal_mem_l I hZF hH (fn.input_mem_of_pairMember entry)) (fn.output_mem_of_pairMember entry)
  exact kpair_unique_l M hZF.1 pair' pair ▸ hp'

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 一轮所需的固定节点与端点查询包

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
  have hel := (hω.members_areOrdinals (ZF.modelsKP hZF) l hl).empty_mem_of_nonempty (ZF.modelsKP hZF) ⟨k, next.predecessor_mem⟩ he
  have hen := (hω.members_areOrdinals (ZF.modelsKP hZF) n hn).transitive l last.predecessor_mem e hel
  obtain ⟨D, pool⟩ := tt_pool_exists_l I hZF hω n U
  obtain ⟨r, m, b, h, a, base⟩ := tg_query_base_l hZF hω he hn last.predecessor_mem hel
  have nat := tt_constants_finite_l hZF hω finite limit rank constants
  obtain ⟨root, max, bound, height, node⟩ := base.scope_l I (ZF.modelsKP hZF) pool nat.1 hs ht nat.2
  let q : Tg_reply_queries_d M := ⟨r, b, h⟩
  have language : Tg_reply_language_d hZF ω e l n κ B U D q :=
    ⟨hn, hen, last.predecessor_mem, limit, rank, constants, pool, root, bound, height, base.2⟩
  have algebra := sc_v_algebra_l hZFC hδ hX
  have trans := v_transitive_l I hX
  have hB := ZF.v_mem_l I hZF language.rank hX hk
  have hU := tt_constants_rank_l hZF hX hδ hk language.rank language.constants
  have hD := language.pool.rank_mem_l (ZF.modelsKP hZF) hω hX hδ (ZF.v_ordinal_mem_l I hZF hX hwδ) hn hU
  have hwX := ZF.v_ordinal_mem_l I hZF hX hwδ
  obtain ⟨hr, hm, hb, hh, ha⟩ := base.rank_l hZF hω hX hδ hwX hn
    (trans U hU s hs) (trans U hU t ht) (trans ω hwX k finite)
  obtain ⟨v, hv, cv⟩ := algebra.kpair_l hh ha
  obtain ⟨p, hp, cp⟩ := sc_quad_l algebra hr hm hb hv
  obtain ⟨c, hc, cc⟩ := sc_quad_l algebra hB hU hD hp
  exact ⟨c, hc, l, n, B, U, D, q.root, m, q.bound, q.height, a, p, v,
    next, last, cc, cp, cv, language, max, node, base⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 节点和端点查询的实际统一表

每个合法键 (κ,k,s,t) 恰查询同一行；整个表在任何局面出现前取定。
表的无关键取空值，游戏读取则必须先验证原参数域和合法键条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_query_key_d (hZF : M.Models ZF) (ω δ x : M.Domain) : Prop :=
  ∃ κ k s t, Rd_quad_d x κ k s t ∧ M.mem κ δ ∧ Tg_query_request_d hZF ω κ k s t

def tg_query_key_m {d} (ω δ x : Term d) : Formula 1 d := set[d] ⟪∃ κ k s t,
  ⌜rd_quad_m⌝ₚ(⌜x⌝ₛ, κ, k, s, t) ∧ κ ∈ ⌜δ⌝ₛ ∧ ⌜tg_query_request_m⌝ₚ(⌜ω⌝ₛ, κ, k, s, t)⟫
derive_free_closed tg_query_key_m

theorem tg_query_key_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω δ x : Term d) :
    Formula.satisfies ρ (tg_query_key_m ω δ x) ↔ Tg_query_key_d hZF (ω.eval ρ) (δ.eval ρ) (x.eval ρ) := by
  simp only [tg_query_key_m, Tg_query_key_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rd_quad_sat_l hZF.1, tg_query_request_sat_l hZF, Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_query_catalog_d (ω e δ X Γ : M.Domain) : Prop := Fn0_d X X Γ ∧
  ∀ κ k s t x c, Rd_quad_d x κ k s t → M.mem κ δ → Tg_query_request_d hZF ω κ k s t →
    Rd_entry_d x c Γ → Tg_query_packet_d hZF ω e κ k s t c

theorem tg_query_catalog_l {ω e δ X : M.Domain} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (hX : V_d I δ X) :
    ∃ Γ, Tg_query_catalog_d hZFC ω e δ X Γ ∧ M.MemberSubset Γ X := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push e).push δ
  let φ : BinarySchema 3 := { body := set[5] ⟪(∃ κ k s t,
    ⌜rd_quad_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, κ, k, s, t) ∧ κ ∈ ⌜(.bound 2 : Term 5)⌝ₛ ∧
    ⌜tg_query_request_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, κ, k, s, t) ∧
    ⌜tg_query_packet_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 3 : Term 5)⌝ₛ, κ, k, s, t, ⌜(.newest : Term 5)⌝ₛ)) ∨
    (¬ ⌜tg_query_key_m⌝ₚ(⌜(.bound 4 : Term 5)⌝ₛ, ⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 1 : Term 5)⌝ₛ) ∧
      ⌜(.newest : Term 5)⌝ₛ = ⌜(.bound 3 : Term 5)⌝ₛ)⟫ }
  have sat x c : φ.denote ρ x c ↔
      (∃ κ k s t, Rd_quad_d x κ k s t ∧ M.mem κ δ ∧ Tg_query_request_d hZF ω κ k s t ∧
        Tg_query_packet_d hZF ω e κ k s t c) ∨ (¬ Tg_query_key_d hZF ω δ x ∧ c = e) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, rd_quad_sat_l hZF.1, tg_query_request_sat_l hZF,
      tg_query_packet_sat_l hZF, tg_query_key_sat_l hZF, Definitional.Term.eval_weaken]
    rfl
  have heω := num_mem_l hZF.1 hω (show Num_d 0 e from he)
  have heX := v_transitive_l I hX ω (ZF.v_ordinal_mem_l I hZF hX hwδ) e heω
  obtain ⟨Γ, fn, all⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := X) (Y := X) (fun x _ => by
    by_cases key : Tg_query_key_d hZF ω δ x
    · obtain ⟨κ, k, s, t, code, hk, request⟩ := key
      obtain ⟨c, hc, packet⟩ := tg_query_packet_exists_l hZFC hω he hδ hwδ hX hk request
      exact ⟨c, hc, (sat x c).mpr (Or.inl ⟨κ, k, s, t, code, hk, request, packet⟩)⟩
    · exact ⟨e, heX, (sat x e).mpr (Or.inr ⟨key, rfl⟩)⟩)
  refine ⟨Γ, ⟨fn0_of_function_l (ZF.modelsKP hZF) fn, fun κ k s t x c code hk request entry => ?_⟩, ?_⟩
  · rcases (sat x c).mp (all x c entry) with ⟨κ', k', s', t', code', _, _, packet⟩ | invalid
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := code'.unique_l code
      exact packet
    · exact (invalid.1 ⟨κ, k, s, t, code, hk, request⟩).elim
  · intro p hp
    obtain ⟨x, c, pair⟩ := fn.1.1 p hp
    have entry : Rd_entry_d x c Γ := ⟨p, pair, hp⟩
    obtain ⟨p', hp', pair'⟩ := (sc_v_algebra_l hZFC hδ hX).kpair_l
      (fn.input_mem_of_pairMember entry) (fn.output_mem_of_pairMember entry)
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'

theorem Tg_query_catalog_d.get_l {ω e δ X Γ κ k s t : M.Domain} (table : Tg_query_catalog_d hZFC ω e δ X Γ)
    (hδ : M.IsLimitOrdinal δ) (hwδ : M.mem ω δ) (hX : V_d I δ X)
    (hk : M.mem κ δ) (request : Tg_query_request_d hZF ω κ k s t) :
    ∃ x c, Rd_quad_d x κ k s t ∧ Rd_entry_d x c Γ ∧ Tg_query_packet_d hZF ω e κ k s t c := by
  obtain ⟨limit, finite, B, U, rank, constants, hs, ht⟩ := request
  have trans := v_transitive_l I hX
  have hU := tt_constants_rank_l hZF hX hδ hk rank constants
  obtain ⟨x, hx, code⟩ := sc_quad_l (sc_v_algebra_l hZFC hδ hX) (ZF.v_ordinal_mem_l I hZF hX hk)
    (trans ω (ZF.v_ordinal_mem_l I hZF hX hwδ) k finite) (trans U hU s hs) (trans U hU t ht)
  obtain ⟨c, _, entry⟩ := table.1.2.1 x hx
  exact ⟨x, c, code, entry, table.2 κ k s t x c code hk ⟨limit, finite, B, U, rank, constants, hs, ht⟩ entry⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 类型游戏的实际走法与表项读取

辅助走法为 (ℓ,t,(κ,u))，回答为 (τ,w)。固定表项只按字面配对结构解包；
合法历史中不重复选择程序，不把语义证书当作额外走法。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_aux_data_d (a ℓ t κ u : M.Domain) : Prop := ∃ b, Rd_triple_d a ℓ t b ∧ KPair_d M b κ u
def tg_aux_data_m {d} (a ℓ t κ u : Term d) : Formula 1 d := set[d] ⟪∃ b,
  ⌜rd_triple0_m⌝ₚ(⌜a⌝ₛ, ⌜ℓ⌝ₛ, ⌜t⌝ₛ, b) ∧ ⌜kpair0_m⌝ₚ(b, ⌜κ⌝ₛ, ⌜u⌝ₛ)⟫
derive_free_closed tg_aux_data_m

theorem tg_aux_data_sat_l (hE : Extensional M) {d} (ρ : Env M d) (a ℓ t κ u : Term d) :
    Formula.satisfies ρ (tg_aux_data_m a ℓ t κ u) ↔
      Tg_aux_data_d (a.eval ρ) (ℓ.eval ρ) (t.eval ρ) (κ.eval ρ) (u.eval ρ) := by
  simp only [tg_aux_data_m, Tg_aux_data_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_triple0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

theorem Tg_aux_data_d.unique_l {a ℓ t κ u ℓ' t' κ' u' : M.Domain}
    (h : Tg_aux_data_d a ℓ t κ u) (h' : Tg_aux_data_d a ℓ' t' κ' u') :
    ℓ = ℓ' ∧ t = t' ∧ κ = κ' ∧ u = u' := by
  obtain ⟨b, head, tail⟩ := h
  obtain ⟨b', head', tail'⟩ := h'
  obtain ⟨rfl, rfl, rfl⟩ := head.unique_l head'
  exact ⟨rfl, rfl, kpair_injective_l M tail tail'⟩

def Tg_ee_data_d (Γ κ n B U D : M.Domain) (q : Ee_queries_d M) : Prop :=
  ∃ x c p, KPair_d M x κ n ∧ Rd_entry_d x c Γ ∧ Rd_quad_d c B U D p ∧
    Rd_quad_d p q.largest q.domain q.inaccessible q.stretch

def tg_ee_data_m {d} (Γ κ n B U D g h i e : Term d) : Formula 1 d := set[d] ⟪∃ x c p,
  ⌜kpair0_m⌝ₚ(x, ⌜κ⌝ₛ, ⌜n⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, c, ⌜Γ⌝ₛ) ∧
  ⌜rd_quad_m⌝ₚ(c, ⌜B⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, p) ∧ ⌜rd_quad_m⌝ₚ(p, ⌜g⌝ₛ, ⌜h⌝ₛ, ⌜i⌝ₛ, ⌜e⌝ₛ)⟫
derive_free_closed tg_ee_data_m

/-- 同一实际函数表的同一个键只能读出同一整行。 -/
theorem Tg_ee_data_d.unique_l {I : kpair_convention_l.Interpretation M} (hE : Extensional M)
    {Γ κ n B U D B' U' D' : M.Domain} {q q' : Ee_queries_d M}
    (fn : M.IsSetFunction I Γ) (h : Tg_ee_data_d Γ κ n B U D q) (h' : Tg_ee_data_d Γ κ n B' U' D' q') :
    B = B' ∧ U = U' ∧ D = D' ∧ q = q' := by
  obtain ⟨x, c, p, key, entry, row, codes⟩ := h
  obtain ⟨x', c', p', key', entry', row', codes'⟩ := h'
  have ex := kpair_unique_l M hE key' key
  subst x'
  have read a b : Rd_entry_d a b Γ → M.PairMember I a b Γ := by
    let ρ : Env M 3 := ⟨fun i => [a, b, Γ].get i, fun _ => a⟩
    exact fun h => (Formula.satisfies_orderedPairMem_iff I ρ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rd_entry_sat_l hE ρ (.bound 0) (.bound 1) (.bound 2)).mpr h)
  have ec := fn.2 x c c' (read x c entry) (read x c' entry')
  subst c'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := row.unique_l row'
  obtain ⟨a, b, c, d⟩ := codes.unique_l codes'
  exact ⟨rfl, rfl, rfl, by cases q; cases q'; cases a; cases b; cases c; cases d; rfl⟩

theorem tg_ee_data_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Γ κ n B U D g h i e : Term d) :
    Formula.satisfies ρ (tg_ee_data_m Γ κ n B U D g h i e) ↔
      Tg_ee_data_d (Γ.eval ρ) (κ.eval ρ) (n.eval ρ) (B.eval ρ) (U.eval ρ) (D.eval ρ)
        ⟨g.eval ρ, h.eval ρ, i.eval ρ, e.eval ρ⟩ := by
  simp only [tg_ee_data_m, Tg_ee_data_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, rd_entry0_sat_l hE, rd_quad_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Tg_query_data_d (Γ κ k s t B U D r m b h q : M.Domain) : Prop :=
  ∃ x c p a, Rd_quad_d x κ k s t ∧ Rd_entry_d x c Γ ∧ Rd_quad_d c B U D p ∧
    Rd_quad_d p r m b a ∧ KPair_d M a h q

def tg_query_data_m {d} (Γ κ k s t B U D r m b h q : Term d) : Formula 1 d := set[d] ⟪∃ x c p a,
  ⌜rd_quad_m⌝ₚ(x, ⌜κ⌝ₛ, ⌜k⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, c, ⌜Γ⌝ₛ) ∧
  ⌜rd_quad_m⌝ₚ(c, ⌜B⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, p) ∧ ⌜rd_quad_m⌝ₚ(p, ⌜r⌝ₛ, ⌜m⌝ₛ, ⌜b⌝ₛ, a) ∧ ⌜kpair0_m⌝ₚ(a, ⌜h⌝ₛ, ⌜q⌝ₛ)⟫
derive_free_closed tg_query_data_m

theorem tg_query_data_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Γ κ k s t B U D r m b h q : Term d) :
    Formula.satisfies ρ (tg_query_data_m Γ κ k s t B U D r m b h q) ↔ Tg_query_data_d
      (Γ.eval ρ) (κ.eval ρ) (k.eval ρ) (s.eval ρ) (t.eval ρ) (B.eval ρ) (U.eval ρ) (D.eval ρ)
      (r.eval ρ) (m.eval ρ) (b.eval ρ) (h.eval ρ) (q.eval ρ) := by
  simp only [tg_query_data_m, Tg_query_data_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_quad_sat_l hE, rd_entry0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Tg_program_data_d (Γ n b z : M.Domain) (σ : Fin 7 → M.Domain) : Prop :=
  ∃ c p q, Rd_entry_d n c Γ ∧ Rd_quad_d c b z p q ∧
    Rd_quad_d p (σ 0) (σ 1) (σ 2) (σ 3) ∧ Rd_triple_d q (σ 4) (σ 5) (σ 6)

theorem Tg_program_data_d.unique_l {I : kpair_convention_l.Interpretation M} (hE : Extensional M)
    {Γ n b z b' z' : M.Domain} {σ σ' : Fin 7 → M.Domain} (fn : M.IsSetFunction I Γ)
    (h : Tg_program_data_d Γ n b z σ) (h' : Tg_program_data_d Γ n b' z' σ') : b = b' ∧ z = z' ∧ σ = σ' := by
  obtain ⟨c, p, q, entry, row, first, last⟩ := h
  obtain ⟨c', p', q', entry', row', first', last'⟩ := h'
  have read a b : Rd_entry_d a b Γ → M.PairMember I a b Γ := by
    let ρ : Env M 3 := ⟨fun i => [a, b, Γ].get i, fun _ => a⟩
    exact fun h => (Formula.satisfies_orderedPairMem_iff I ρ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rd_entry_sat_l hE ρ (.bound 0) (.bound 1) (.bound 2)).mpr h)
  have ec := fn.2 n c c' (read n c entry) (read n c' entry')
  subst c'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := row.unique_l row'
  obtain ⟨a, b, c, d⟩ := first.unique_l first'
  obtain ⟨e, f, g⟩ := last.unique_l last'
  refine ⟨rfl, rfl, funext ?_⟩
  exact Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e
    (Fin.cases f (Fin.cases g (fun i => Fin.elim0 i)))))))

def tg_program_data_m {d} (Γ n b z : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪∃ c p q,
  ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, c, ⌜Γ⌝ₛ) ∧ ⌜rd_quad_m⌝ₚ(c, ⌜b⌝ₛ, ⌜z⌝ₛ, p, q) ∧
  ⌜rd_quad_m⌝ₚ(p, ⌜σ 0⌝ₛ, ⌜σ 1⌝ₛ, ⌜σ 2⌝ₛ, ⌜σ 3⌝ₛ) ∧ ⌜rd_triple0_m⌝ₚ(q, ⌜σ 4⌝ₛ, ⌜σ 5⌝ₛ, ⌜σ 6⌝ₛ)⟫

@[simp] theorem tg_program_data_closed_l {d} (Γ n b z : Term d) (σ : Fin 7 → Term d)
    (hΓ : Γ.freeSupport = []) (hn : n.freeSupport = []) (hb : b.freeSupport = []) (hz : z.freeSupport = [])
    (hσ : ∀ j, (σ j).freeSupport = []) : (tg_program_data_m Γ n b z σ).FreeClosed := by
  simp -implicitDefEqProofs [tg_program_data_m, Definitional.Formula.FreeClosed, hΓ, hn, hb, hz, hσ]

theorem tg_program_data_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Γ n b z : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (tg_program_data_m Γ n b z σ) ↔
      Tg_program_data_d (Γ.eval ρ) (n.eval ρ) (b.eval ρ) (z.eval ρ) (fun j => (σ j).eval ρ) := by
  simp only [tg_program_data_m, Tg_program_data_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, rd_quad_sat_l hE, rd_triple0_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从固定表项自动回收原语义接口

表项的唯一坐标把字面读取与原编译证书连起来；调用者不用提供查询正确性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_catalog_d.read_l {ω δ X P Γ κ n B U D : M.Domain} {q : Ee_queries_d M}
    (table : Ee_catalog_d hZFC ω δ X P Γ) (hk : M.mem κ δ) (hn : M.mem n ω) (hκ : M.IsLimitOrdinal κ)
    (data : Tg_ee_data_d Γ κ n B U D q) : Ee_language_d hZF ω κ n B U D q := by
  rcases q with ⟨g, h, i, e⟩
  obtain ⟨x, c, p, key, entry, row, codes⟩ := data
  obtain ⟨B', U', D', g', h', i', e', p', row', codes', language⟩ := table.2.2 κ n x c hk hn hκ key entry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := row'.unique_l row
  obtain ⟨rfl, rfl, rfl, rfl⟩ := codes'.unique_l codes
  exact language

theorem Ee_catalog_d.get_l {ω δ X P Γ κ n : M.Domain} (table : Ee_catalog_d hZFC ω δ X P Γ)
    (hk : M.mem κ δ) (hn : M.mem n ω) (hκ : M.IsLimitOrdinal κ) :
    ∃ B U D, ∃ q : Ee_queries_d M, Tg_ee_data_d Γ κ n B U D q ∧ Ee_language_d hZF ω κ n B U D q := by
  obtain ⟨x, key⟩ := (I).total κ n
  obtain ⟨c, _, entry⟩ := table.2.1.2.1 x ((table.1 x).mpr ⟨κ, hk, n, hn, key⟩)
  obtain ⟨B, U, D, g, h, i, e, p, row, codes, language⟩ := table.2.2 κ n x c hk hn hκ key entry
  exact ⟨B, U, D, ⟨g, h, i, e⟩, ⟨x, c, p, key, entry, row, codes⟩, language⟩

theorem Tg_query_catalog_d.read_l {ω e δ X Γ κ k s t B U D r m b h q : M.Domain}
    (table : Tg_query_catalog_d hZFC ω e δ X Γ) (hk : M.mem κ δ)
    (request : Tg_query_request_d hZF ω κ k s t) (data : Tg_query_data_d Γ κ k s t B U D r m b h q) :
    ∃ l n, M.SuccessorOf l k ∧ M.SuccessorOf n l ∧ Tg_reply_language_d hZF ω e l n κ B U D ⟨r, b, h⟩ ∧
      Tg_max_query_d I ω l n U D m ∧ Tg_node_query_d I ω e n l U D s t k q ∧
      Formula.satisfies (⟨fun i => [ω, e, l, n, k, s, t, r, m, b, h, q].get i, fun _ => ω⟩ : Env M 12) tg_query_row0_m := by
  obtain ⟨x, c, p, a, key, entry, row, codes, tail⟩ := data
  obtain ⟨l, n, B', U', D', r', m', b', h', q', p', a', next, last, row', codes', tail', lang, max, node, base⟩ :=
    table.2 κ k s t x c key hk request entry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := row'.unique_l row
  obtain ⟨rfl, rfl, rfl, rfl⟩ := codes'.unique_l codes
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M tail' tail
  exact ⟨l, n, next, last, lang, max, node, (tg_query_row_sat_l I (ZF.modelsKP hZF) _).mpr ⟨base, next, last⟩⟩

theorem Tg_program_catalog_d.read_l {ω H Γ n b z : M.Domain} {σ : Fin 7 → M.Domain}
    (table : Tg_program_catalog_d hZFC ω H Γ) (data : Tg_program_data_d Γ n b z σ) :
    ∃ a, Ts_program_d hZF ω n b σ a z := by
  obtain ⟨c, p, q, entry, row, first, last⟩ := data
  obtain ⟨b', z', p', q', s₀, s₁, s₂, s₃, s₄, s₅, s₆, a, row', first', last', prog⟩ := table.2 n c entry
  obtain ⟨rfl, rfl, rfl, rfl⟩ := row'.unique_l row
  obtain ⟨rfl, rfl, rfl, rfl⟩ := first'.unique_l first
  obtain ⟨rfl, rfl, rfl⟩ := last'.unique_l last
  have eq : (Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
      (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6))))))) = σ := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) j
  exact ⟨a, eq ▸ prog⟩

theorem Tg_program_catalog_d.get_l {ω H Γ n : M.Domain} (table : Tg_program_catalog_d hZFC ω H Γ)
    (hn : M.mem n ω) : ∃ b z, ∃ σ : Fin 7 → M.Domain, ∃ a,
      Tg_program_data_d Γ n b z σ ∧ Ts_program_d hZF ω n b σ a z := by
  obtain ⟨c, _, entry⟩ := table.1.2.1 n hn
  obtain ⟨b, z, p, q, s₀, s₁, s₂, s₃, s₄, s₅, s₆, a, row, first, last, prog⟩ := table.2 n c entry
  exact ⟨b, z, _, a, ⟨c, p, q, entry, row, first, last⟩, prog⟩

end YesMetaZFC.SetTheory.LargeCardinal

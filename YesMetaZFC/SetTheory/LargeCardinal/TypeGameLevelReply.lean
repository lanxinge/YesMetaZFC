import YesMetaZFC.SetTheory.LargeCardinal.TypeGameLevel
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyDescent

/-! # 旧请求的实现高度沿实际回答严格下降

直接解包原走法和回答，以固定代码表恢复两侧语言及子类型程序。
完整实现的常数域由 Vκ 的唯一性对齐，任意原排列仍交给已证下降定理处理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_setup_d.level_reset_l {p : Tg_params_d M.Domain} {X n h a ℓ κ u : M.Domain}
    (setup : Tg_setup_d hZFC p X) (aux : Tg_aux_d hZF p n h a) (data : Tg_aux_data_d a ℓ p.e κ u) :
    Tg_level_d hZF p.ω p.e p.δ p.S p.a κ u p.ν p.e := by
  obtain ⟨ℓ₀, t, κ₀, u₀, k, l, N, x, s, B, U, D, r₀, m, b₀, q, f, C, V, W, g₀, g₁, g₂, g₃,
    parsed, hk, ft, hl, hN, _, _, request, query, _, _, _, _, _, branch⟩ := aux
  obtain ⟨rfl, rfl, rfl, rfl⟩ := parsed.unique_l data
  have eq : k = p.e := hZF.1.eq_of_same_members k p.e (fun i => iff_of_false
    (fun hi => (ft.2.1 i hi).elim fun y hy => hy.2.elim fun z hz => setup.empty z hz.2) (setup.empty i)); subst k
  have eq := hl.eq hZF.1 setup.one; subst l
  obtain ⟨η, Y, c, R, r, height, rank, model, full, first, last⟩ :=
    branch.elim And.right (fun no => (no.1 rfl).elim)
  obtain ⟨l, N', hl, hN', target, _⟩ := setup.queries.read_l hZFC hk request query
  have eq := hl.eq hZF.1 setup.one; subst l
  have eq := hN'.eq hZF.1 hN; subst N'
  refine ⟨η, Y, c, R, N, B, U, D, r, height, rank, model, hN, target.rank, target.constants, full, first, last, ?_⟩
  intro x
  refine iff_of_false (setup.empty x) ?_
  rintro ⟨i, hi, ne, _⟩
  exact ((setup.one i).mp hi).elim (setup.empty i) (fun eq => ne (hZF.1.eq_of_same_members i p.e eq))

theorem Tg_setup_d.level_reply_l {p : Tg_params_d M.Domain} {X n h h₁ a b ℓ t κ u k l α g : M.Domain}
    (setup : Tg_setup_d hZFC p X) (hn : M.mem n p.ω) (fh₁ : M.IsSetFunction I h₁)
    (event : Tg_event_d I p.c n p.e h₁ a) (aux : Tg_aux_d hZF p n h a) (answer : Tg_answer_d hZF p n h₁ b)
    (data : Tg_aux_data_d a ℓ t κ u) (ft : Fn0_d k p.ω t) (hl : M.SuccessorOf l k)
    (level : Tg_level_d hZF p.ω p.e p.δ p.S l κ u α g) (root : M.mem p.e p.S)
    (notOrd : ¬ M.IsOrdinal p.S) (labels : M.IsSetRelation I g) :
    ∃ τ B V D w N, ∃ q : Tg_reply_queries_d M, ∃ η Y d H r β,
      KPair_d M b τ w ∧ M.mem τ p.δ ∧ M.SuccessorOf N l ∧ Tg_reply_language_d hZF p.ω p.e l N τ B V D q ∧
      V_d I η Y ∧ Smem_d I d Y H ∧ Tt_realized_d I p.ω d Y H N r p.δ V D w ∧
      Rd_entry_d p.e p.S r ∧ Rd_entry_d l β r ∧ Sg_set_d I p.e l r g ∧
      Tg_bound_d I p.δ p.S β ∧ Tg_height_d β η ∧ M.mem β α := by
  obtain ⟨hc, _⟩ := tg_clock_l hZF setup.omega setup.empty setup.one setup.two setup.three hn
  obtain ⟨ℓ₀, t₀, κ₀, u₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    parsed, hκ, _, _, _, _, _, requestκ, _⟩ := aux
  obtain ⟨rfl, rfl, rfl, rfl⟩ := parsed.unique_l data
  obtain ⟨a', ℓ', t', κ', u', τ, w, k', l', N, B, U, D, g₀, g₁, g₂, g₃, C, V, W, r₀, m, q₀, f, j, b₀, z,
    s₀, s₁, s₂, s₃, s₄, s₅, s₆, event', parsed, pair, ft', hl', hN, ee, hτ, request, query, code, reply⟩ := answer
  have eq := event'.unique_l hZF (setup.omega.members_areOrdinals hZF p.c hc) fh₁ event; subst a'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := parsed.unique_l data
  have eq := ft'.domain_eq_l hZF.1 ft; subst k'
  have eq := hl'.eq hZF.1 hl; subst l'
  obtain ⟨μ, A, c, R, N', B', U', P, r, height, rank, model, hN', hB', constants, full, first, last, set⟩ := level
  have eq := hN'.eq hZF.1 hN; subst N'
  have hlω := setup.omega.transitive hZF N full.finite l hN.predecessor_mem
  have source := setup.elastic.elim fun _ table => table.read_l hZFC hκ hlω requestκ.1 ee
  have eq := ZF.v_unique_l I hZF hB' source.rank; subst B'
  have eq := hZF.1.eq_of_same_members U' U (fun x => (constants x).trans (source.constants x).symm); subst U'
  obtain ⟨l', N', hl', hN', target, _⟩ := setup.queries.read_l hZFC hτ request query
  have eq := hl'.eq hZF.1 hl; subst l'
  have eq := hN'.eq hZF.1 hN; subst N'
  obtain ⟨H₀, _, programs, _⟩ := setup.programs
  obtain ⟨v, program⟩ := programs.read_l hZFC code
  have hel := (setup.omega.members_areOrdinals hZF l hlω).empty_mem_of_nonempty
    (ZF.modelsKP hZF) ⟨k, hl.predecessor_mem⟩ setup.empty
  obtain ⟨η, Y, d, H, r', β, hY, lower, real, root', last', set', bound, gap, below⟩ :=
    reply.descend_l hZF setup.omega setup.empty hel program source target rank height model full first root notOrd set labels
  exact ⟨τ, C, V, W, w, N, ⟨r₀, q₀, f⟩, η, Y, d, H, r', β, pair, hτ, hN, target,
    hY, lower, real, root', last', set', bound, gap, below⟩

end YesMetaZFC.SetTheory.LargeCardinal

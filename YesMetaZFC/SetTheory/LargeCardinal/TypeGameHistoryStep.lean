import YesMetaZFC.SetTheory.LargeCardinal.TypeGameHistoryContinue
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssuedReset
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePadding

/-! # 全部内部轮号上的统一树后继

只按原请求的标签图是否为空分支。重置使用原表中的完整输入，继续使用
整份历史自动选择旧轮；两者都返回同一实际回答和两条树边。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.tree_successor_l {ω X R μ K η C c₀ α ξ T Q G E L H b c o π Cᵣ γ Z : M.Domain}
    (context : Tg_context_d ω X η C) (source : Ic_model_d hZF ω μ K X R)
    (nc : Nonempty {x // M.mem x C}) (ι : Env (rt_model_l C nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val = ω)
    (tree : It_pnice_d hZF ω c₀ α T Q G E L) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (mx : Smem_d I c X R) (ho : ∀ x, ¬ M.mem x o)
    (root : It_map_d G o ξ π) (image : Rd_entry_d Cᵣ C π) (anchor : Tg_anchor_d γ Z X π)
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z) (letters : M.mem (ι.bound 6).val Z)
    (lower : M.MemberSubset γ (ι.bound 24).val)
    (past : Tg_past_d hZF ω (ι.bound 19).val H X b) (links : Tg_past_links_d I H Q)
    (roots : Tg_past_roots_d ω H G o Cᵣ γ Z)
    (events : Tg_past_events_d ω H C (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val (ι.bound 20).val)
    (plays : Tg_past_play_d ω H Z C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val)
    (below : M.mem b (ι.bound 24).val) (bounds : ∀ i ν, Rd_entry_d i ν L → M.mem ν b ∨ ν = b) :
    Tg_tree_step_d hZF ω X η c₀ α ξ T Q G E c o Cᵣ γ Z H nc ι := by
  classical
  by_cases empty : ι.bound 23 = ι.bound 1
  · have fs := (context.read_l hZF source.source).1
    let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
    have ext := rt_model_ext_l hZF.1 fs.transitive nc
    obtain ⟨ε, seed, head, _, hb, digitZero, _, graph, move, _, _, _, matched⟩ := tg_issued_reset_l J ext ι issued empty
    have state := (tg_issued_sat_l J ext ι).mp issued
    have eκ : (ε.bound 5).val = (ι.bound 24).val := congrArg Subtype.val (move.unique_l state.move).2.2.1
    have hwε : (ε.bound 0).val = ω := (congrArg Subtype.val (head 0)).trans hw
    have lowerε : M.MemberSubset γ (ε.bound 5).val := eκ.symm ▸ lower
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, language⟩ :=
      tg_issued_query_l J ext ι issued
    simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at language
    have κlimit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ι.bound 24)).mp
      ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.2.2.1)
    have eb : (ε.bound 23).val = (ι.bound 24).val := (congrArg Subtype.val hb).trans eκ
    have above i ν (hn : Rd_entry_d i ν L) : M.mem ν (ε.bound 23).val ∨ ν = (ε.bound 23).val :=
      Or.inl (eb.symm ▸ (bounds i ν hn).elim (κlimit.1.transitive b below ν) (fun eq => eq.symm ▸ below))
    obtain ⟨v, round, β, T₁, Q₁, G₁, E₁, id, π₁, padded, pad, node₁, padEdge, identity, padEmpty, root₁, image₁, anchor₁,
      β₂, T₂, Q₂, G₂, E₂, L₂, d, j, N, R₂, K₂, ℓ, F, κ, U, D, u, η₂, C₂, W,
      next, extend, node₂, edge, mn, ready, ultra, critical, payload, limit, bound, subset, heights,
      iU, iD, iu, reply, iη, iC, context₂, _, hW, _, common, level, _, _, _, _, π₂, root₂, image₂, anchor₂, update⟩ :=
      context.pad_round_l hZFC nc ε source tree succ hc mx hwε ho root image anchor lowerε above seed
    let ρ := tg_round_env_d ε v
    have sameS : (ρ.bound 19).val = (ι.bound 7).val := congrArg Subtype.val (head 3)
    have padMap := padded.tree.diagram.elementary ξ α id c X R c X R padEdge
      (pad.2.2.1 ξ c hc) node₁ mx.1 mx.1
    obtain ⟨S', _, hS⟩ := padMap.1.1.2.2 (ι.bound 7).val
      (source.source.transitive C context.member _ (ι.bound 7).property)
    have hS : Rd_entry_d (ι.bound 7).val (ρ.bound 19).val id :=
      sameS.symm ▸ (identity _ _ hS).symm ▸ hS
    have request : Tg_request_d (fun i => (ι.bound i).val) (fun i => (ρ.bound i).val) :=
      fun i => congrArg Subtype.val (matched v i)
    have body := (Formula.satisfies_conj_iff ..).mp round |>.2
    simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at body
    have high : M.MemberSubset γ (v 15).val := fun x hx => (limit.1.mem bound).transitive _ body.2.1 x (lowerε x hx)
    have eU : (ε.bound 15).val = (ι.bound 30).val := request 15
    have eD : (ε.bound 16).val = (ι.bound 31).val := request 16
    have eu : (ε.bound 18).val = (ι.bound 25).val := request 17
    have digitZero : (ρ.bound 40).val = (ι.bound 1).val := congrArg Subtype.val digitZero
    have rules := (Formula.satisfies_conj_iff ..).mp state.control |>.2.2.1
    simp only [tg_rules_m] at rules
    have empty₀ := (Formula.satisfies_isEmpty_iff ..).mp rules.2.1
    have he : ∀ z, ¬ M.mem z (ι.bound 1).val := fun z hz => empty₀ ⟨z,fs.transitive _ (ι.bound 1).property z hz⟩ hz
    have lowS : M.mem (ρ.bound 40).val Z := digitZero.symm ▸
      anchor.rank.transitive_l hZF source.source.transitive anchor.member ω hωZ _
        (num_mem_l hZF.1 source.source.omega (show Num_d 0 (ι.bound 1).val from he))
    have play : Tg_play_d C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ.bound 40).val := by
      rw [digitZero]
      apply (tg_play_read_l hZF fs.transitive nc J (ι.bound 4) (ι.bound 3) (ι.bound 20) (ι.bound 1)).mpr
      rintro i x ⟨p, _, hp⟩
      exact (empty₀ p hp).elim
    have padLower : ∀ p κ L F, Rd_entry_d ξ p E₁ → It_payload_d p κ L F → M.MemberSubset γ κ := by
      rintro p κ L F hp ⟨r, ⟨a, b, _, _, pair⟩, _⟩
      exact (padEmpty p hp a ((pair a).mpr (Or.inl rfl))).elim
    exact ⟨ξ, β, T₁, Q₁, G₁, E₁, L, c, X, R, μ, K, η, C, π₁,
      padded, pad, node₁, mx, source, context, root₁, image₁, anchor₁, padLower, nc, ρ, round, request, high,
      Or.inl ⟨congrArg Subtype.val empty, rfl, congrArg Subtype.val graph, id, padEdge, hS⟩,
      ⟨lowS, play⟩,
      β₂, T₂, Q₂, G₂, E₂, L₂, d, j, N, R₂, K₂, ℓ, F, κ, U, D, u, η₂, C₂, W, π₂,
      next, extend, node₂, edge, mn, ready, eκ ▸ ultra, eκ ▸ critical, eκ ▸ payload, limit, bound, subset, heights,
      eU ▸ iU, eD ▸ iD, eu ▸ iu, reply, iη, iC, context₂, hW, common, level,
      root₂, image₂, anchor₂, eκ ▸ update⟩
  · exact events.continue_tree_l hZFC context source nc ι issued hw empty tree succ hc mx ho root image
      anchor hγ hωZ letters past links roots plays below bounds

end YesMetaZFC.SetTheory.LargeCardinal

import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlQuery
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContext
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryTransfer

/-! # 实际后继层中的原回答查询

回答的合法键由已有相对秩层和有限闭性构造，再直接读取搬运后的原表。
跨根查询的真值由完整回答所在的较早层核验。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.query_request_l {ω κ K X R η C : M.Domain}
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω κ K X R) (hierarchy : Sc_hierarchy_d X)
    (nc : Nonempty {x // M.mem x C}) (τ k e : (rt_model_l C nc).Domain)
    (limit : M.IsLimitOrdinal τ.val) (finite : M.mem k.val ω) (empty : ∀ x, ¬ M.mem x e.val) :
    Formula.satisfies (⟨fun i => [⟨ω, context.omega⟩, τ, k, e, e].get i,
      fun _ => ⟨ω, context.omega⟩⟩ : Env (rt_model_l C nc) 5) tg_query_request0_m := by
  have fs := (context.read_l hZF source).1
  have hτ := source.transitive C context.member τ.val τ.property
  obtain ⟨B, hB, rank⟩ := hierarchy τ.val hτ limit.1
  obtain ⟨hBC, vr⟩ := context.rank.rank_l hZF source.transitive context.member context.limit τ.property hB rank
  obtain ⟨c, S, code⟩ := smdl_membership_l I hZF ⟨ω, context.omega⟩
  have theory := source.rank_theory_l hZF context.member context.rank context.limit code
  obtain ⟨U, hU, constants⟩ := theory.algebra.insert_l hBC τ.property
  have he := num_mem_l hZF.1 source.omega (show Num_d 0 e.val from empty)
  have heB := vr.ordinal_subset_l hZF fs.transitive hBC e.val (source.omega.subset_limitOrdinal hZF limit e.val he)
  let ρ : Env (rt_model_l C nc) 5 := ⟨fun i => [⟨ω, context.omega⟩, τ, k, e, e].get i, fun _ => ⟨ω, context.omega⟩⟩
  simp only [tg_query_request0_m, Formula.satisfies_conj_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff]
  refine ⟨(rt_limit_l fs.transitive nc (ZF.modelsKP hZF) τ).mpr limit, finite, ⟨B, hBC⟩, ⟨U, hU⟩, ?_, ?_,
    (constants e.val).mpr (Or.inl heB), (constants e.val).mpr (Or.inl heB)⟩
  · exact (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ((ρ.push ⟨B, hBC⟩).push ⟨U, hU⟩)
      (.bound 3) (.bound 1)).mpr vr
  · apply (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 3) (.bound 1) (.bound 0))
      ((ρ.push ⟨B, hBC⟩).push ⟨U, hU⟩)).mpr
    exact (tt_constants0_sat_l hZF.1 ..).mpr constants

theorem Tg_context_d.answer_query_l {ω κ K X R η C : M.Domain}
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω κ K X R) (hierarchy : Sc_hierarchy_d X)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 19)
    (valid : Formula.satisfies ρ tg_control0_m) (hw : (ρ.bound 0).val = ω)
    (empty : ∀ x, ¬ M.mem x (ρ.bound 1).val) (τ k : (rt_model_l C nc).Domain)
    (limit : M.IsLimitOrdinal τ.val) (finite : M.mem k.val ω) (below : M.mem τ.val (ρ.bound 5).val) :
    ∃ B U D r m b h q l n : (rt_model_l C nc).Domain,
      Tg_query_data_d (ρ.bound 11) τ k (ρ.bound 1) (ρ.bound 1) B U D r m b h q ∧
      (rt_model_l C nc).SuccessorOf l k ∧ (rt_model_l C nc).SuccessorOf n l ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, l, n, τ, B, U, D, r, b, h].get i,
        ρ.free⟩ : Env (rt_model_l C nc) 11) tg_reply_language0_m ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, l, n, k, ρ.bound 1, ρ.bound 1, r, m, b, h, q].get i,
        ρ.free⟩ : Env (rt_model_l C nc) 12) tg_query_row0_m := by
  let ε : Env (rt_model_l C nc) 5 := ⟨fun i => [⟨ω, context.omega⟩, τ, k, ρ.bound 1, ρ.bound 1].get i,
    fun _ => ⟨ω, context.omega⟩⟩
  exact tg_control_query_l (rt_model_ext_l hZF.1 (context.read_l hZF source).1.transitive nc) ρ ε valid
    (Subtype.ext hw.symm) below (context.query_request_l hZF source hierarchy nc τ k (ρ.bound 1) limit finite empty)

/-- 当前表的查询回到回答的实际实现所在层；只搬运共同低秩参数。 -/
theorem Tg_context_d.answer_members_l {ω X R μ K η C Y S μ' K' η' D B T r c d π σ C₀ γ Z : M.Domain}
    (context : Tg_context_d ω X η C) (current : Tg_context_d ω Y η' D)
    (owner : Ep_source_d hZF ω μ K X R) (source : Ep_source_d hZF ω μ' K' Y S)
    (bt : M.TransitiveSet B) (mb : Smem_d I r B T) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (j : Smap_d I ω r c B X π) (k : Smap_d I ω r d B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (anchor : Tg_anchor_d γ Z X π) (target : Tg_anchor_d γ Z Y σ)
    (limit : M.IsLimitOrdinal γ) (hwZ : M.mem ω Z)
    (nc : Nonempty {x // M.mem x C}) (nd : Nonempty {x // M.mem x D})
    (ρ : Env (rt_model_l C nc) 54) (θ : Env (rt_model_l D nd) 7)
    (hw : (ρ.bound 16).val = ω) (round : Formula.satisfies ρ tg_round0_m)
    (same : ∀ i : Fin 4, (θ.bound (i.castAdd 3)).val =
      [(ρ.bound 16).val, (ρ.bound 17).val, (ρ.bound 23).val, (ρ.bound 24).val].get i)
    (base : Formula.satisfies θ tg_reply_base0_m) :
    M.mem (θ.bound 4).val (ρ.bound 11).val ∧ M.mem (θ.bound 5).val (ρ.bound 11).val ∧
      M.mem (θ.bound 6).val (ρ.bound 11).val := by
  obtain ⟨seed, data⟩ := (Formula.satisfies_conj_iff ..).mp round
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at seed
  have he : M.mem (ρ.bound 17).val ω := hw ▸ seed.2.2.1
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, _, _, _, _, language, _⟩ := data
  simp only [tg_reply_language_m, Formula.satisfies_bind, tg_reply_language0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  have hn : M.mem (ρ.bound 24).val ω := hw ▸ language.1
  have hl := owner.omega.transitive hZF (ρ.bound 24).val hn (ρ.bound 23).val language.2.2.1
  have zt := anchor.rank.transitive_l hZF owner.transitive anchor.member
  have low : ∀ i : Fin 4, M.mem (θ.bound (i.castAdd 3)).val Z := by
    intro i
    rw [same i]
    exact Fin.cases (hw.symm ▸ hwZ) (Fin.cases (zt ω hwZ _ he)
      (Fin.cases (zt ω hwZ _ hl) (Fin.cases (zt ω hwZ _ hn) (fun a => Fin.elim0 a)))) i
  have ωθ : (θ.bound 0).val = ω := (same 0).trans hw
  obtain ⟨_, ψ, eqψ, valid⟩ := target.reply_peer_l hZF nd θ anchor nc source current.member
    (current.read_l hZF source).1 bt owner.transitive (context.read_l hZF owner).1.transitive
    mb my mx k j iD iC limit ωθ low base
  have links (i : Fin 4) : (ψ.bound (i.castAdd 3)).val =
      [(ρ.bound 16).val, (ρ.bound 17).val, (ρ.bound 23).val, (ρ.bound 24).val].get i :=
    (eqψ (i.castAdd 3)).trans (same i)
  have compare := context.reply_queries_l hZF owner nc ρ round
  simp only [tg_reply_compare0_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at compare
  have facts := compare (ψ.bound 4) (ψ.bound 5) (ψ.bound 6) (by
    unfold tg_reply_base_m
    apply (Formula.satisfies_bind ..).mpr
    apply (Formula.closed_env_l tg_reply_base0_m tg_reply_base0_closed_l (ρ := ψ) (η := _) ?_).mp valid
    funext i
    exact Fin.cases (Subtype.ext (links 0)) (Fin.cases (Subtype.ext (links 1))
      (Fin.cases (Subtype.ext (links 2)) (Fin.cases (Subtype.ext (links 3))
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))))))) i)
  exact ⟨eqψ 4 ▸ facts.1, eqψ 5 ▸ facts.2.1, eqψ 6 ▸ facts.2.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

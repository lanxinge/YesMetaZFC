import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Game.QueryTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerAdvance
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyReflect
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.OddBranch
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.FiniteArithmeticSource
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

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
    (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hierarchy : Sc_hierarchy_d X)
    (nc : Nonempty {x // M.mem x C}) (τ k e : (rt_model_l C nc).Domain)
    (limit : M.IsLimitOrdinal τ.val) (finite : M.mem k.val ω) (empty : ∀ x, ¬ M.mem x e.val) :
    Formula.satisfies (⟨fun i => [⟨ω, (context.omega_l source.code)⟩, τ, k, e, e].get i,
      fun _ => ⟨ω, (context.omega_l source.code)⟩⟩ : Env (rt_model_l C nc) 5) tg_query_request0_m := by
  have fs := (context.read_l hZF source).1
  have hτ := source.transitive C context.member τ.val τ.property
  obtain ⟨B, hB, rank⟩ := hierarchy τ.val hτ limit.1
  obtain ⟨hBC, vr⟩ := (context.rank_l (ZF.modelsKP hZF) source.transitive source.code).rank_l hZF source.transitive context.member (context.limit_l (ZF.modelsKP hZF) source.transitive source.code) τ.property hB rank
  obtain ⟨c, S, code⟩ := smdl_membership_l I hZF ⟨ω, (context.omega_l source.code)⟩
  have theory := source.rank_theory_l hZF context.member (context.rank_l (ZF.modelsKP hZF) source.transitive source.code) (context.limit_l (ZF.modelsKP hZF) source.transitive source.code) code
  obtain ⟨U, hU, constants⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) fs.transitive code).insert_l hBC τ.property
  have he := num_mem_l hZF.1 source.omega (show Num_d 0 e.val from empty)
  have heB := vr.ordinal_subset_l hZF fs.transitive hBC e.val (source.omega.subset_limitOrdinal (ZF.modelsKP hZF) limit e.val he)
  let ρ : Env (rt_model_l C nc) 5 := ⟨fun i => [⟨ω, (context.omega_l source.code)⟩, τ, k, e, e].get i, fun _ => ⟨ω, (context.omega_l source.code)⟩⟩
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
    (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hierarchy : Sc_hierarchy_d X)
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
  let ε : Env (rt_model_l C nc) 5 := ⟨fun i => [⟨ω, (context.omega_l source.code)⟩, τ, k, ρ.bound 1, ρ.bound 1].get i,
    fun _ => ⟨ω, (context.omega_l source.code)⟩⟩
  exact tg_control_query_l (rt_model_ext_l hZF.1 (context.read_l hZF source).1.transitive nc) ρ ε valid
    (Subtype.ext hw.symm) below (context.query_request_l hZF source hierarchy nc τ k (ρ.bound 1) limit finite empty)

/-- 当前表的查询回到回答的实际实现所在层；只搬运共同低秩参数。 -/
theorem Tg_context_d.answer_members_l {ω X R μ K η C Y S μ' K' η' D B T r c d π σ C₀ γ Z : M.Domain}
    (context : Tg_context_d I ω X R η C) (current : Tg_context_d I ω Y S η' D)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ' K' Y S)
    (mb : Smdl_d I r B T) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (j : Smap_d I ω r c B X π) (k : Smap_d I ω r d B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (anchor : Tg_anchor_d I γ Z X R π) (target : Tg_anchor_d I γ Z Y S σ)
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
  have hl := owner.omega.transitive (ZF.modelsKP hZF) (ρ.bound 24).val hn (ρ.bound 23).val language.2.2.1
  obtain ⟨_, hZ, rank, _⟩ := anchor.read_l (ZF.modelsKP hZF) owner.transitive mx
  have zt := rank.transitive_l owner.transitive hZ
  have low : ∀ i : Fin 4, M.mem (θ.bound (i.castAdd 3)).val Z := by
    intro i
    rw [same i]
    exact Fin.cases (hw.symm ▸ hwZ) (Fin.cases (zt ω hwZ _ he)
      (Fin.cases (zt ω hwZ _ hl) (Fin.cases (zt ω hwZ _ hn) (fun a => Fin.elim0 a)))) i
  have ωθ : (θ.bound 0).val = ω := (same 0).trans hw
  obtain ⟨_, ψ, eqψ, valid⟩ := target.reply_peer_l hZF nd θ anchor nc source current.member
    (current.read_l hZF source).1 owner.transitive (context.read_l hZF owner).1.transitive
    mb my mx k j iD iC limit ωθ low base
  have links (i : Fin 4) : (ψ.bound (i.castAdd 3)).val =
      [(ρ.bound 16).val, (ρ.bound 17).val, (ρ.bound 23).val, (ρ.bound 24).val].get i :=
    (eqψ (i.castAdd 3)).trans (same i)
  have compare := (context.kernel_mem_l owner.transitive owner.code (context.read_l hZF owner).1.transitive nc).reply_queries_l ρ round
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

/-! ## 实际超幂回答通过原游戏的查询表

先读取目标层的原表，再在共同秩段识别查询域。三条查询沿共同树根回到
完整回答所在层核验，最后将同一个回答装配到原表项上。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X R μ K η C : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 54)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))
local notation "slots" => (Fin.cases (p 47) (Fin.cases (p 48) (Fin.cases (p 49)
  (Fin.cases (p 50) (Fin.cases (p 51) (Fin.cases (p 52) (fun _ => p 53)))))))

theorem Tg_context_d.answer_table_l {Y S μ' K' η' D B T r c d π σ C₀ γ Z L W κ U V u : M.Domain}
    (context : Tg_context_d I ω X R η C) (current : Tg_context_d I ω Y S η' D)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ' K' Y S)
    (hierarchy : Sc_hierarchy_d Y)
    (mb : Smdl_d I r B T) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (j : Smap_d I ω r c B X π) (k : Smap_d I ω r d B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (anchor : Tg_anchor_d I γ Z X R π) (target : Tg_anchor_d I γ Z Y S σ)
    (hγ : M.IsLimitOrdinal γ) (hwZ : M.mem ω Z)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hτW : M.mem (p 15) W)
    (nd : Nonempty {x // M.mem x D}) (θ : Env (rt_model_l D nd) 19)
    (control : Formula.satisfies θ tg_control0_m) (hw : p 16 = ω) (hw' : (θ.bound 0).val = ω)
    (he : (θ.bound 1).val = p 17) (τ t : (rt_model_l D nd).Domain)
    (ht : τ.val = p 15) (hk : t.val = p 22) (below : M.mem τ.val (θ.bound 5).val)
    (round : Formula.satisfies ρ tg_round0_m)
    (reply : Tg_reply_d I ω (p 23) (p 24) κ (p 15) U V (p 12) u (p 11) (p 36) slots
      (p 38) ⟨p 2, p 1, p 0⟩) :
    ∃ B' U' D' r' m' b' h' q' l n : (rt_model_l D nd).Domain,
      Tg_query_data_d (θ.bound 11) τ t (θ.bound 1) (θ.bound 1) B' U' D' r' m' b' h' q' ∧
      l.val = p 23 ∧ n.val = p 24 ∧ D'.val = p 12 ∧
      Formula.satisfies (⟨fun i => [θ.bound 0, θ.bound 1, l, n, τ, B', U', D', r', b', h'].get i,
        θ.free⟩ : Env (rt_model_l D nd) 11) tg_reply_language0_m ∧
      Formula.satisfies (⟨fun i => [θ.bound 0, θ.bound 1, l, n, t, θ.bound 1, θ.bound 1, r', m', b', h', q'].get i,
        θ.free⟩ : Env (rt_model_l D nd) 12) tg_query_row0_m ∧
      Tg_reply_d I ω (p 23) (p 24) κ (p 15) U V D'.val u (p 11) (p 36) slots
        (p 38) ⟨r'.val, b'.val, h'.val⟩ := by
  have fs := (context.read_l hZF owner).1
  have ft := (current.read_l hZF source).1
  obtain ⟨seed, data⟩ := (Formula.satisfies_conj_iff ..).mp round
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨_, empty, _, _, _, _, _, succ, succ', _⟩ := seed
  have empty := (Formula.satisfies_isEmpty_iff ..).mp empty
  have zero (x : M.Domain) (hx : M.mem x (p 17)) : False :=
    empty ⟨x, fs.transitive (p 17) (ρ.bound 17).property x hx⟩ hx
  have succ := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp succ)
  have succ' := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 24) (ρ.bound 23)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp succ')
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, _, _, _, _, language, _⟩ := data
  let f : Fin 11 → Term 54 := fun i => [.bound 16, .bound 17, .bound 23, .bound 24, .bound 15,
    .bound 14, .bound 13, .bound 12, .bound 2, .bound 1, .bound 0].get i
  let ε := Definitional.Env.substitute ρ f
  have language : Formula.satisfies ε tg_reply_language0_m := (Formula.satisfies_bind ρ f tg_reply_language0_m).mp language
  have facts := language
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at facts
  have hn : M.mem (p 24) ω := hw ▸ facts.1
  have hl := owner.omega.transitive (ZF.modelsKP hZF) (p 24) hn (p 23) succ'.predecessor_mem
  have finite : M.mem t.val ω := hk.symm ▸ owner.omega.transitive (ZF.modelsKP hZF) (p 23) hl (p 22) succ.predecessor_mem
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp facts.2.2.2.1)
  obtain ⟨B', U', D', r', m', b', h', q', l, n, row, sl, sn, language', queries⟩ :=
    current.answer_query_l hZF source hierarchy nd θ control hw' (he.symm ▸ zero) τ t (ht.symm ▸ limit) finite below
  have hk₀ : t.val = (ρ.bound 22).val := hk
  have el := ((rt_successor_l ft.transitive nd hZF.1 l t).mp sl).eq hZF.1 (hk₀.symm ▸ succ)
  have en := ((rt_successor_l ft.transitive nd hZF.1 n l).mp sn).eq hZF.1 (el.symm ▸ succ')
  let ε' : Env (rt_model_l D nd) 11 := ⟨fun i => [θ.bound 0, θ.bound 1, l, n, τ, B', U', D', r', b', h'].get i, θ.free⟩
  obtain ⟨_, _, eqD⟩ := context.reply_domain_l hZF current owner source hW rank hW' rank' hL nc nd ε ε'
    hw hw' en ht hτW language language'
  have eqD : p 12 = D'.val := eqD
  let ψ : Env (rt_model_l D nd) 12 := ⟨fun i => [θ.bound 0, θ.bound 1, l, n, t, θ.bound 1, θ.bound 1, r', m', b', h', q'].get i, θ.free⟩
  let g : Fin 7 → Term 12 := fun i => [.bound 0, .bound 1, .bound 2, .bound 3, .bound 7, .bound 9, .bound 10].get i
  let ζ := Definitional.Env.substitute ψ g
  have base : Formula.satisfies ζ tg_reply_base0_m := (Formula.satisfies_bind ψ g tg_reply_base0_m).mp
    ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp queries).1).2
  have same : ∀ i : Fin 4, (ζ.bound (i.castAdd 3)).val = [p 16, p 17, p 23, p 24].get i := by
    intro i
    exact Fin.cases (hw'.trans hw.symm) (Fin.cases he (Fin.cases el (Fin.cases en (fun a => Fin.elim0 a)))) i
  obtain ⟨hr, hb, hh⟩ := context.answer_members_l hZF current owner source mb mx my j k iC iD anchor target
    hγ hwZ nc nd ρ ζ hw round same base
  obtain ⟨sub, v, drop, subtype, _⟩ := reply
  exact ⟨B', U', D', r', m', b', h', q', l, n, row, el, en, eqD.symm, language', queries,
    eqD ▸ sub, v, drop, subtype, hr, hb, hh⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 跨模型回答实际推进原策略历史

完整回答保留在产生它的模型中，历史保留在施加扩展器后的模型中。
共同秩段和共同根图核对后继模型的原查询表，随后在该模型内构造回答的
有序对并追加历史。原控制记录随后处理实数落子、增加轮号并给出下一辅助
记录；工作模型的 ZF 模型性和新回答的合法性均由已有证书取代。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X R μ K η C : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 54)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))
local notation "slots" => (Fin.cases (p 47) (Fin.cases (p 48) (Fin.cases (p 49)
  (Fin.cases (p 50) (Fin.cases (p 51) (Fin.cases (p 52) (fun _ => p 53)))))))

theorem Tg_context_d.answer_history_l {Y S μ' K' η' D B T r c d π σ C₀ γ Z L W : M.Domain}
    (context : Tg_context_d I ω X R η C) (current : Tg_context_d I ω Y S η' D)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ' K' Y S)
    (hierarchy : Sc_hierarchy_d Y)
    (mb : Smdl_d I r B T) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (j : Smap_d I ω r c B X π) (k : Smap_d I ω r d B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (anchor : Tg_anchor_d I γ Z X R π) (target : Tg_anchor_d I γ Z Y S σ)
    (hγ : M.IsLimitOrdinal γ) (hwZ : M.mem ω Z)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hτW : M.mem (p 15) W)
    (nd : Nonempty {x // M.mem x D}) (θ : Env (rt_model_l D nd) 46)
    (issued : Formula.satisfies θ tg_issued0_m) (hw : p 16 = ω)
    (same : ∀ i : Fin 14, (θ.bound ([0, 1, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44].get i)).val =
      p ([16, 17, 22, 23, 24, 36, 38, 47, 48, 49, 50, 51, 52, 53].get i))
    (below : M.mem (p 15) (θ.bound 5).val) (round : Formula.satisfies ρ tg_round0_m)
    (reply : Tg_reply_d I ω (p 23) (p 24) (θ.bound 24).val (p 15) (θ.bound 30).val (θ.bound 31).val
      (p 12) (θ.bound 25).val (p 11) (p 36) slots (p 38) ⟨p 2, p 1, p 0⟩) :
    ∃ v t q : (rt_model_l D nd).Domain, KPair_d M v.val (p 15) (p 11) ∧
      Formula.satisfies (tg_position_env_d
        ⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ (θ.bound 19) t q) (tg_position0_m 2) ∧
      Formula.satisfies (⟨fun i => [θ.bound 0, t, θ.bound 20, v].get i, fun _ => v⟩ :
        Env (rt_model_l D nd) 4) (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
      Tg_trace_d I Y S ω D (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val (θ.bound 19).val t.val (θ.bound 23).val (p 15) (p 11) ∧
      let ψ := tg_position_env_d
        (⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩ : Env (rt_model_l D nd) 19) (θ.bound 19) t q
      ∀ x, (rt_model_l D nd).mem x (ψ.bound 6) → ∃ v' t' j' n',
        (rt_model_l D nd).mem v' (ψ.bound 6) ∧
        (Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) → v' = x) ∧
        (¬ Formula.satisfies ψ (Descriptive.gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 19)) →
          Rd_entry_d (ψ.bound 20) v' (ψ.bound 17)) ∧
        Formula.satisfies (⟨fun i => [ψ.bound 0, t', ψ.bound 20, v'].get i, fun _ => v'⟩ : Env (rt_model_l D nd) 4)
          (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
        (rt_model_l D nd).SuccessorOf n' (ψ.bound 19) ∧
        Formula.satisfies (tg_position_env_d ⟨fun i => ψ.bound (i.castAdd 3), fun _ => ψ.bound 0⟩ n' t' j')
          (tg_position0_m 0) ∧
        ∃ ε : Env (rt_model_l D nd) 46, (∀ i : Fin 19, ε.bound (i.castAdd 27) = ψ.bound (i.castAdd 3)) ∧
          ε.bound 19 = n' ∧ Formula.satisfies ε tg_issued0_m ∧ Rd_entry_d t' (ε.bound 21) (ψ.bound 17) ∧
          Formula.satisfies (⟨fun i => [ψ.bound 0, ε.bound 20, t', ε.bound 21].get i, fun _ => ε.bound 21⟩ :
            Env (rt_model_l D nd) 4)
            (fseq_end_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1) (.bound 2) (.bound 3)) ∧
          (rt_model_l D nd).mem (θ.bound 24) (ε.bound 24) ∧
          M.MemberSubset (θ.bound 20).val (ε.bound 20).val ∧
          (θ.bound 20).val ≠ (ε.bound 20).val ∧
          Tg_trace_d I Y S ω D (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val (θ.bound 19).val
            (ε.bound 20).val (θ.bound 23).val (p 15) (p 11) := by
  have fs := (current.read_l hZF source).1
  let J := rt_pair_l fs.transitive nd hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nd
  have state := (tg_issued_sat_l J ext θ).mp issued
  let χ : Env (rt_model_l D nd) 19 := ⟨fun i => θ.bound (i.castAdd 27), fun _ => θ.bound 0⟩
  have ωθ : (θ.bound 0).val = ω := (same 0).trans hw
  have copy := reply
  obtain ⟨_, u, _, sub, _⟩ := copy
  obtain ⟨hτκ, _, z, query, _⟩ := sub
  let τ : (rt_model_l D nd).Domain := ⟨p 15, fs.transitive _ (θ.bound 24).property _ hτκ⟩
  let w : (rt_model_l D nd).Domain := ⟨p 11, fs.transitive _ (θ.bound 30).property _ query.constants.1⟩
  obtain ⟨B', U', D', r', m', b', f', q', _, _, row, _, _, _, _, _, valid⟩ :=
    context.answer_table_l hZF nc ρ current owner source hierarchy mb mx my j k iC iD anchor target
      hγ hwZ hW rank hW' rank' hL hτW nd χ state.control hw ωθ (same 1) τ (θ.bound 26)
      rfl (same 2) below round reply
  let ε : Env (rt_model_l D nd) 22 := ⟨fun i => [θ.bound 0, θ.bound 27, θ.bound 28, θ.bound 24, τ,
    θ.bound 30, θ.bound 31, D', θ.bound 25, w, θ.bound 36, θ.bound 37, r', b', f',
    θ.bound 38, θ.bound 39, θ.bound 40, θ.bound 41, θ.bound 42, θ.bound 43, θ.bound 44].get i,
    fun _ => θ.bound 0⟩
  let s : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  have slotEq : (fun i => ((s i).eval ε).val) = slots := by
    funext i
    exact Fin.cases (same 7) (Fin.cases (same 8) (Fin.cases (same 9) (Fin.cases (same 10)
      (Fin.cases (same 11) (Fin.cases (same 12) (Fin.cases (same 13) (fun a => Fin.elim0 a))))))) i
  have legal : Formula.satisfies ε tg_reply0_m := by
    apply current.reply_l hZF source nd ε (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
      (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12)
      (.bound 13) (.bound 14) s
    rw [slotEq]
    change Tg_reply_d I (θ.bound 0).val (θ.bound 27).val (θ.bound 28).val (θ.bound 24).val (p 15)
      (θ.bound 30).val (θ.bound 31).val D'.val (θ.bound 25).val (p 11) (θ.bound 36).val slots
      (θ.bound 37).val ⟨r'.val, b'.val, f'.val⟩
    rw [ωθ, (show (θ.bound 27).val = p 23 from same 3),
      (show (θ.bound 28).val = p 24 from same 4), (show (θ.bound 36).val = p 36 from same 5),
      (show (θ.bound 37).val = p 38 from same 6)]
    exact valid
  -- 同一请求在后继层有实际秩层见证；由原表项得到完整回答并追加策略历史。
  have seed := (Formula.satisfies_conj_iff ..).mp round |>.1
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_rename, Formula.satisfies_conj_iff] at seed
  have empty := (Formula.satisfies_isEmpty_iff ..).mp seed.2.1
  have zero (x : M.Domain) (hx : M.mem x (θ.bound 1).val) : False := by
    have hx' : M.mem x (p 17) := same 1 ▸ hx
    exact empty ⟨x, (context.read_l hZF owner).1.transitive _ (ρ.bound 17).property x hx'⟩ hx'
  have data := (Formula.satisfies_conj_iff ..).mp round |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, _, _, _, _, language, _⟩ := data
  simp only [tg_reply_language_m, Formula.satisfies_bind, tg_reply_language0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  have limit := (rt_limit_l (context.read_l hZF owner).1.transitive nc (ZF.modelsKP hZF) (ρ.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.2.2.1)
  have hn : M.mem (p 24) ω := hw ▸ language.1
  have hlast := (rt_successor_l fs.transitive nd hZF.1 (θ.bound 28) (θ.bound 27)).mp state.last
  have hfirst := (rt_successor_l fs.transitive nd hZF.1 (θ.bound 27) (θ.bound 26)).mp state.first
  have finite : M.mem (θ.bound 26).val ω := source.omega.transitive (ZF.modelsKP hZF) _
    (source.omega.transitive (ZF.modelsKP hZF) _ ((same 4).symm ▸ hn) _ hlast.predecessor_mem) _ hfirst.predecessor_mem
  have request := current.query_request_l hZF source hierarchy nd τ (θ.bound 26) (θ.bound 1) limit finite zero
  have request : Formula.satisfies (⟨fun i => [θ.bound 0, τ, θ.bound 26, θ.bound 1, θ.bound 1].get i,
      fun _ => θ.bound 0⟩ : Env (rt_model_l D nd) 5) tg_query_request0_m := by
    apply (Formula.closed_env_l tg_query_request0_m tg_query_request0_closed_l (ρ := _) (η := _) ?_).mp request
    funext i
    exact Fin.cases (Subtype.ext ωθ.symm) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun a => Fin.elim0 a))))) i
  obtain ⟨v, t, q, pair, next, endt, trace, advance⟩ :=
    tg_answer_advance_l (ZF.modelsKP hZF) fs nd θ issued below request row legal
  have labels : Fn0_d (θ.bound 26).val ω (θ.bound 23).val := ωθ ▸
    (fn0_sat_l hZF.1 ..).mp ((rt_model_delta_l fs.transitive nd (fn0_delta_l (.bound 0) (.bound 1) (.bound 2))
      (⟨fun i => [θ.bound 26, θ.bound 0, θ.bound 23].get i, fun _ => θ.bound 0⟩ : Env (rt_model_l D nd) 3)).mp
        ((fn0_sat_l ext ..).mpr state.labels))
  have record (h : (rt_model_l D nd).Domain)
      (event : Tg_round_event_d J (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) h (θ.bound 23) v) :
      Tg_trace_d I Y S ω D (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val (θ.bound 19).val h.val
        (θ.bound 23).val (p 15) (p 11) :=
    tg_trace_build_l I hZF.1 my source.transitive current.member source.omega_mem fs.transitive nd
      (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 19) h (θ.bound 23) v finite labels pair
      ((tg_round_event_sat_l J ext ..).mpr event)
  refine ⟨v, t, q, pair, next, endt, record t trace, ?_⟩
  dsimp only
  intro x hx
  obtain ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε, head, num, issued', value, aux,
    growth, keep, proper, trace⟩ := advance x hx
  exact ⟨v', t', j', n', hv, even, odd, digit, succ, start, ε, head, num, issued', value, aux,
    growth, keep, proper, record (ε.bound 20) trace⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 当前辅助历史唯一确定完整原实数前缀

前缀函数图仍以背景轮号及字母表为定义域、值域；事件证书解释在当前原关系中。
实际隶属实例将该证书读为逐点对应，完整前缀与存档中的短前缀由同一历史比较。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

variable (I : kpair_convention_l.Interpretation M)

def Tg_real_d (X R A C c b n h s : M.Domain) : Prop := Fn0_d n A s ∧ Tg_play_d I X R C c b h s

def tg_real_m {d} (X R A C c b n h s : Term d) : Formula 1 d :=
  .conj (fn0_m n A s) (tg_play_m X R C c b h s)
@[simp] theorem tg_real_closed_l {d} (X R A C c b n h s : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hA : A.freeSupport = [])
    (hC : C.freeSupport = []) (hc : c.freeSupport = []) (hb : b.freeSupport = [])
    (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hs : s.freeSupport = []) :
    (tg_real_m X R A C c b n h s).FreeClosed := by
  simp -implicitDefEqProofs [tg_real_m, Definitional.Formula.FreeClosed,hX,hR,hA,hC,hc,hb,hn,hh,hs]
theorem tg_real_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R A C c b n h s : Term d) :
    Formula.satisfies ρ (tg_real_m X R A C c b n h s) ↔ Tg_real_d I (X.eval ρ) (R.eval ρ)
      (A.eval ρ) (C.eval ρ) (c.eval ρ) (b.eval ρ) (n.eval ρ) (h.eval ρ) (s.eval ρ) := by
  simp only [tg_real_m,Tg_real_d,Formula.satisfies_conj_iff,fn0_sat_l hE,tg_play_sat_l I]

def Tg_turn_move_d (ω A X R C c b n h Y S C' c' b' m h' x : M.Domain) : Prop :=
  ∃ s t y, Tg_real_d I X R A C c b n h s ∧ Tg_real_d I Y S A C' c' b' m h' t ∧
    Fseq_end_d I ω t s y ∧ (Gm_even_d I ω n → y = x)
def tg_turn_move_m {d} (ω A X R C c b n h Y S C' c' b' m h' x : Term d) : Formula 1 d := set[d] ⟪∃ s t y,
  ⌜tg_real_m⌝ₚ(⌜X⌝ₛ,⌜R⌝ₛ,⌜A⌝ₛ,⌜C⌝ₛ,⌜c⌝ₛ,⌜b⌝ₛ,⌜n⌝ₛ,⌜h⌝ₛ,s) ∧
  ⌜tg_real_m⌝ₚ(⌜Y⌝ₛ,⌜S⌝ₛ,⌜A⌝ₛ,⌜C'⌝ₛ,⌜c'⌝ₛ,⌜b'⌝ₛ,⌜m⌝ₛ,⌜h'⌝ₛ,t) ∧
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,t,s,y) ∧ (⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜n⌝ₛ) → y = ⌜x⌝ₛ)⟫
derive_free_closed tg_turn_move_m

theorem tg_turn_move_sat_l (hE : Extensional M) {d} (ρ : Env M d)
    (ω A X R C c b n h Y S C' c' b' m h' x : Term d) :
    Formula.satisfies ρ (tg_turn_move_m ω A X R C c b n h Y S C' c' b' m h' x) ↔
    Tg_turn_move_d I (ω.eval ρ) (A.eval ρ) (X.eval ρ) (R.eval ρ) (C.eval ρ) (c.eval ρ) (b.eval ρ) (n.eval ρ) (h.eval ρ)
      (Y.eval ρ) (S.eval ρ) (C'.eval ρ) (c'.eval ρ) (b'.eval ρ) (m.eval ρ) (h'.eval ρ) (x.eval ρ) := by
  simp only [tg_turn_move_m,Tg_turn_move_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,tg_real_sat_l I hE,
    fseq_end_sat_l I hE,gm_even_sat_l I hE,Formula.satisfies_imp_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]; rfl

theorem tg_issued_real_l (hE : Extensional M) {a X R ω C : M.Domain} (model : Smem_d I a X R) (xt : M.TransitiveSet X) (hC : M.mem C X)
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 46) (valid : Formula.satisfies ρ tg_issued0_m) :
    ∃ s, Tg_real_d I X R (ρ.bound 6).val C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 19).val (ρ.bound 20).val s := by
  let J := rt_pair_l fs.transitive nc hE fs.pair
  obtain ⟨h,x,_,_,_,_,_,_,_,_,_,endt,digits,_⟩ := tg_issued_query_l J (rt_model_ext_l hE fs.transitive nc) ρ valid
  refine ⟨x.val,(rt_fn_l fs.transitive nc hE _ _ _).mp digits.1,?_⟩
  apply (tg_play_read_l I hE model xt hC fs.transitive nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) x).mpr
  intro i v hi
  exact ((digits.2 i v (digits.1.bound_l hi).1).mp hi).end_l endt

theorem Tg_real_d.unique_l (hE : Extensional M) {a X R ω C s t : M.Domain} (model : Smem_d I a X R) (xt : M.TransitiveSet X) (hC : M.mem C X)
    (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 46) (valid : Formula.satisfies ρ tg_issued0_m)
    (hs : Tg_real_d I X R (ρ.bound 6).val C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 19).val (ρ.bound 20).val s)
    (ht : Tg_real_d I X R (ρ.bound 6).val C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 19).val (ρ.bound 20).val t) : s = t := by
  let J := rt_pair_l fs.transitive nc hE fs.pair
  apply hs.1.ext_l hE ht.1
  intro i hi
  obtain ⟨x,_,hx⟩ := hs.1.2.1 i hi
  obtain ⟨y,_,hy⟩ := ht.1.2.1 i hi
  have eq := hs.2.entry_eq_l I hE model xt hC fs.transitive nc J ρ valid ht.2 hx hy
  exact ⟨x,hx,eq.symm ▸ hy⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 两条树边之后闭合整份递归历史

原请求沿偶数嵌入搬运；完整回答仍在实际奇数源核验。旧行的低参数固定，
新回答、实数落子和下一请求均由同一控制记录产生，最后恢复原递归不变量。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_d.advance_l {ω c₀ o Cᵣ γ Z A x : M.Domain} {v : Fin 18 → M.Domain} {u : Fin 46 → M.Domain}
    (h : Tg_run_d hZF ω c₀ o Cᵣ γ Z A v u) (ho : ∀ z, ¬ M.mem z o)
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z) (hAZ : M.mem A Z) (hx : M.mem x A) :
    ∃ w t, Tg_run_d hZF ω c₀ o Cᵣ γ Z A w t ∧ Tg_run_next_d hZF ω c₀ v u w t ∧
      Tg_turn_move_d I ω A (v 0) (v 1) (v 5) (u 4) (u 3) (u 19) (u 20) (w 0) (w 1) (w 5) (t 4) (t 3) (t 19) (t 20) x := by
  obtain ⟨_, hZ, rankZ, fixedRoot⟩ := h.anchor.read_l (ZF.modelsKP hZF) h.source.source.transitive h.model
  let nc : Nonempty {z // M.mem z (v 5)} := ⟨⟨ω, (h.context.omega_l h.source.source.code)⟩⟩
  obtain ⟨nd₀, ι₀, eu, issued⟩ := h.read_l hZF
  let ι := h.model.slice_env_d I ⟨v 5, h.context.member⟩ nd₀ nc ι₀
  have issued : Formula.satisfies ι tg_issued0_m :=
    (h.model.slice_formula_l I ⟨v 5, h.context.member⟩ (h.source.source.transitive (v 5) h.context.member)
      nd₀ nc tg_issued0_m ι₀).mp issued
  have eq : (fun i => (ι.bound i).val) = u := funext eu
  rw [← eq]
  have h : Tg_run_d hZF ω c₀ o Cᵣ γ Z A v (fun i => (ι.bound i).val) := eq.symm ▸ h
  have fs := (h.context.read_l hZF h.source.source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ι).mp issued
  have hn : M.mem (ι.bound 19).val ω := Eq.mp (congrArg (fun w => M.mem (ι.bound 19).val w) h.omega) state.round
  obtain ⟨s, real⟩ := tg_issued_real_l I hZF.1 h.model h.source.source.transitive h.context.member fs nc ι issued
  have real : Tg_real_d I (v 0) (v 1) A (v 5) (ι.bound 4).val (ι.bound 3).val (ι.bound 19).val (ι.bound 20).val s :=
    Eq.mp (congrArg (fun B => Tg_real_d I (v 0) (v 1) B (v 5) (ι.bound 4).val (ι.bound 3).val (ι.bound 19).val (ι.bound 20).val s)
      h.alphabet) real
  have lowReal : M.mem s Z := rankZ.relation_mem_l h.source.source.transitive hZ hγ hωZ hAZ
    (h.source.source.transitive _ h.context.member s (real.2.mem_l I h.model)) (by
      intro p hp
      obtain ⟨i,hi,y,hy,pair⟩ := real.1.1 p hp
      exact ⟨i,h.source.source.omega.transitive (ZF.modelsKP hZF) _ hn i hi,y,hy,pair⟩)
  -- 记录已给出全部树参数；显式传入，避免从展开的长记录反推这些参数。
  have step := h.context.tree_successor_l hZFC
      (ω := ω) (X := v 0) (R := v 1) (μ := v 2) (K := v 3) (η := v 4) (C := v 5)
      (c₀ := c₀) (α := v 6) (ξ := v 7) (T := v 8) (Q := v 9) (G := v 10) (E := v 11) (L := v 12)
      (H := v 13) (b := v 14) (c := v 15) (o := o) (π := v 16) (Cᵣ := Cᵣ) (γ := γ) (Z := Z)
      h.source nc ι issued h.omega h.tree h.successor h.node h.model ho
      h.root h.image h.anchor hγ hωZ (h.alphabet.symm ▸ hAZ) h.lower h.past h.links h.roots h.events h.play h.below h.bounds
  obtain ⟨k, β, T₁, Q₁, G₁, E₁, H₁, a, Y, R, μ, K, η₁, C₁, π₁,
    nice₁, ext₁, node₁, my, sy, cy, root₁, image₁, anchor₁, lower₁, n₁, ρ, round, request, high, odd, ⟨lowS, played⟩, step⟩ := step
  obtain ⟨β₂, T₂, Q₂, G₂, E₂, H₂, d, j, N, R₂, K₂, L, F, κ, U, D, u₀, η₂, C₂, W, π₂,
    nice₂, ext₂, node₂, edge, mn, sn, ultra, crit, payload₂, limit, bound, subset, heights,
    iU, iD, iu, reply, iη, iC, cn, hW, common, level, root₂, image₂, anchor₂, update⟩ := step
  obtain ⟨_, _, _, fixedZ₂⟩ := anchor₂.read_l (ZF.modelsKP hZF) sn.source.transitive mn
  obtain ⟨p₂, entry₂, pay₂⟩ := payload₂
  have requestκ : (ρ.bound 21).val = (ι.bound 24).val := request 14
  have hκY : M.mem (ι.bound 24).val Y := requestκ ▸
    sy.source.transitive C₁ cy.member (ρ.bound 21).val (ρ.bound 21).property
  have lo := It_lower_d.mem_l I hZF my sy.source.transitive (anchor₁.read_l (ZF.modelsKP hZF) sy.source.transitive my).1 hγ.1 hκY h.lower
  have critical := ext₂.critical_bound_l I (ext₁.critical_bound_l I h.critical lower₁)
    (it_payload_bound_l I (ZF.modelsKP hZF) nice₂.tree.move_function entry₂ pay₂
      (ext₂.2.2.1 (v 6) a node₁) my.1 lo)
  have hj := ultra.elementary_l hZF h.model.1 mn.1
  have fn := hj.1.1.1.2
  have natural := hj.natural_l hZF h.source.source.omega h.source.source.transitive sn.source.transitive
    h.model mn h.source.source.omega_mem
  have fixed {z z'} (hz : M.mem z ω) (hz' : Rd_entry_d z z' j) : z' = z := fn z z' z hz' (natural z hz)
  let n₂ : Nonempty {z // M.mem z C₂} := ⟨⟨ω, cn.omega_l sn.source.code⟩⟩
  have ft := (cn.read_l hZF sn.source).1
  let P := rt_pair_l ft.transitive n₂ hZF.1 ft.pair
  -- 原关系边直接恢复完整目标记录；以下逐项解码仅服务于尚待迁移的隶属树不变量。
  let N₀ := smdl_structure_l I (R := R₂) mn.1.2.1
  let C' : N₀.Domain := ⟨C₂, cn.member⟩
  have inside := sn.source.transitive C₂ cn.member
  have extN := smem_ext_l I mn.1 mn.2 sn.source.transitive hZF.1
  have nativeFinite := cn.finite_l mn.1.2.1 extN
  let nd : Nonempty {z : N₀.Domain // N₀.mem z C'} :=
    ⟨⟨⟨ω, cn.omega_mem⟩, nativeFinite.omega_mem⟩⟩
  obtain ⟨_, θ₀, _, images, _, _, valid⟩ := hj.record_image_l I hZF h.source.source.omega h.model.1 mn.1 extN
    C' iC nativeFinite.transitive nd tg_issued0_m tg_issued0_closed_l h.record h.values
  let θ := mn.slice_env_d I C' nd n₂ θ₀
  have valid : Formula.satisfies θ tg_issued0_m :=
    (mn.slice_formula_l I C' inside nd n₂ tg_issued0_m θ₀).mp valid
  have images (i) : Rd_entry_d (ι.bound i).val (θ.bound i).val j := images i
  have ωθ : (θ.bound 0).val = ω := fn ω _ ω (h.omega ▸ images 0)
    (hj.omega_l I hZF h.source.source.omega h.source.source.transitive sn.source.transitive h.model mn h.source.source.omega_mem)
  have seed := (Formula.satisfies_conj_iff ..).mp round |>.1
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  have data := (Formula.satisfies_conj_iff ..).mp round |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, _, _, _, _, language, _, _, _, hb, hz, h₀, h₁, h₂, h₃, h₄, h₅, h₆, _⟩ := data
  simp only [tg_reply_language_m, Formula.satisfies_bind, tg_reply_language0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at language
  have hw : (ρ.bound 16).val = ω := (request 0).trans h.omega
  have hm : M.mem (ρ.bound 24).val ω := hw ▸ language.1
  have hl := sy.source.omega.transitive (ZF.modelsKP hZF) _ hm _ language.2.2.1
  have first := (rt_successor_l (cy.read_l hZF sy.source).1.transitive n₁ hZF.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp seed.2.2.2.2.2.2.2.1)
  have hk := sy.source.omega.transitive (ZF.modelsKP hZF) _ hl _ first.predecessor_mem
  have he : M.mem (ρ.bound 17).val ω := hw ▸ seed.2.2.1
  have fixedRequest (i : Fin 19)
      (hi : M.mem (ρ.bound ([16, 17, 22, 23, 24, 36, 38, 47, 48, 49, 50, 51, 52, 53, 21, 31, 32, 34, 41].get i)).val ω) :
      (θ.bound ([0, 1, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44, 24, 30, 31, 25, 23].get i)).val =
      (ρ.bound ([16, 17, 22, 23, 24, 36, 38, 47, 48, 49, 50, 51, 52, 53, 21, 31, 32, 34, 41].get i)).val := by
    apply fixed hi
    exact Eq.mpr (congrArg (fun z => Rd_entry_d z
      (θ.bound ([0, 1, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44, 24, 30, 31, 25, 23].get i)).val j)
        (request i)) (images _)
  have same : ∀ i : Fin 14, (θ.bound ([0, 1, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44].get i)).val =
      (ρ.bound ([16, 17, 22, 23, 24, 36, 38, 47, 48, 49, 50, 51, 52, 53].get i)).val := by
    intro i
    exact Fin.cases (ωθ.trans hw.symm)
      (Fin.cases (fixedRequest 1 he)
      (Fin.cases (fixedRequest 2 hk)
      (Fin.cases (fixedRequest 3 hl)
      (Fin.cases (fixedRequest 4 hm)
      (Fin.cases (fixedRequest 5 (hw ▸ hb))
      (Fin.cases (fixedRequest 6 (hw ▸ hz))
      (Fin.cases (fixedRequest 7 (hw ▸ h₀))
      (Fin.cases (fixedRequest 8 (hw ▸ h₁))
      (Fin.cases (fixedRequest 9 (hw ▸ h₂))
      (Fin.cases (fixedRequest 10 (hw ▸ h₃))
      (Fin.cases (fixedRequest 11 (hw ▸ h₄))
      (Fin.cases (fixedRequest 12 (hw ▸ h₅))
      (Fin.cases (fixedRequest 13 (hw ▸ h₆)) (fun i => Fin.elim0 i)))))))))))))) i
  have eκ := fn _ _ _ (images 24) crit.image
  have eU := fn _ _ _ (images 30) iU
  have eD := fn _ _ _ (images 31) iD
  have eu := fn _ _ _ (images 25) iu
  have state' := (tg_issued_sat_l P (rt_model_ext_l hZF.1 ft.transitive n₂) θ).mp valid
  have δ := cn.control_card_l hZF sn.source n₂ _ state'.control ωθ
  have δlimit := δ.limit_l (ZF.modelsKP hZF) sn.source.transitive (sn.source.algebra_l (ZF.modelsKP hZF)).pair
  have below := δlimit.1.transitive κ (eκ ▸ state'.bound) (ρ.bound 15).val (subset _ bound)
  obtain ⟨B, S, _, _, _, mb, _⟩ := (h.tree.tree.sources o c₀ (h.tree.tree.root o ho)).objects
  have jy := nice₁.tree.diagram.elementary o (v 6) π₁ c₀ B S a Y R root₁ (nice₁.tree.root o ho) node₁ mb my.1
  have jn := nice₂.tree.diagram.elementary o β π₂ c₀ B S d N R₂ root₂ (nice₂.tree.root o ho) node₂ mb mn.1
  obtain ⟨rₛ, _, _, _⟩ := sn.read_l hZF
  have answer := cy.answer_history_l hZF n₁ ρ cn sy.source sn.source rₛ mb my mn
    jy jn image₁ image₂ anchor₁ anchor₂ hγ hωZ hW common level.member level.hierarchy limit
    (common.ordinal_subset_l hZF sy.source.transitive hW _ bound) n₂ θ valid hw same below round (by
      rw [eκ, eU, eD, eu]; exact reply)
  obtain ⟨n, H, q, hn', ns, past, _, code, newest, entries, fixedPast, links⟩ :=
    update _ _ _ hn h.past h.below h.links
  have keepRoot i f (hf : It_map_d (v 10) o i f) :=
    (ext₂.2.2.2.1 o i f ((nice₁.tree.diagram.model_domain i).mpr
      ((h.tree.tree.diagram.model_domain i).mp (h.tree.tree.diagram.order.bound o i
        (h.tree.tree.diagram.map_bound_l hZF hf)).2 |>.imp fun a ha => ext₁.2.2.1 i a ha))).mpr
      ((ext₁.2.2.2.1 o i f (h.tree.tree.diagram.order.bound o i (h.tree.tree.diagram.map_bound_l hZF hf)).2).mpr hf)
  have roots := Tg_past_roots_d.push_l I hZF past ns newest entries (h.roots.extend_l I keepRoot)
    ((ext₂.2.2.2.1 o (v 6) π₁ ext₁.1.predecessor_mem).mpr root₁) image₁ anchor₁ ⟨_, code, high⟩
  obtain ⟨S₀, treeImage, treeNames⟩ := h.tree_name
  have keep₁ i f (hf : It_map_d (v 10) o i f) :=
    (ext₁.2.2.2.1 o i f (h.tree.tree.diagram.order.bound o i (h.tree.tree.diagram.map_bound_l hZF hf)).2).mpr hf
  have oddTree := treeNames.odd_l hZF keep₁ nice₁.tree.diagram (keep₁ _ _ h.root) treeImage root₁ odd
  have treeNames := Tg_root_tree_d.push_l hZF past ns newest entries (treeNames.extend_l keepRoot)
    ⟨_, code, rfl, rfl, rfl, rfl, rfl⟩ ((ext₂.2.2.2.1 o (v 6) π₁ ext₁.1.predecessor_mem).mpr root₁) oddTree
  have succω {a b : M.Domain} (ha : M.mem a ω) (hs : M.SuccessorOf b a) : M.mem b ω := by
    obtain ⟨b', hs', hb'⟩ := h.source.source.omega.1.2 a ha
    exact hs'.eq hZF.1 hs ▸ hb'
  have en := fixed hn (images 19)
  -- 每个旧轮的轮号、有限标签与共同层回答均由已有记录构造固定像。
  have events := h.events.map_l I hZF h.source.source.omega h.model.1 mn.1 hj
    (hj.omega_l I hZF h.source.source.omega h.source.source.transitive sn.source.transitive
      h.model mn h.source.source.omega_mem) iC (images 4) (images 1) (images 2) (images 20) (by
    intro m i U T μ K η D ℓ V q row s code trace
    obtain ⟨source, saved, _⟩ := h.past.read_l hZF row
    obtain ⟨d, model⟩ := source.source.code
    obtain ⟨ρ, code', _, _, hτ, _, _, hw⟩ := saved.membership_l I hZF.1 model
      (source.source.transitive D saved.context.member) ⟨⟨ω, saved.context.omega_l ⟨d, model⟩⟩⟩
    have eq := code.inj_l I hZF.1 code'
    have eτ : s 15 = (ρ.bound 15).val := congrFun eq 17
    have ew : s 11 = (ρ.bound 11).val := congrFun eq 13
    obtain ⟨k, hk, labels, _, t, _, _, et, _, _⟩ :=
      trace.read_l I hZF.1 h.model h.source.source.transitive fs.transitive nc
        (ι.bound 4) (ι.bound 1) (ι.bound 2) (ι.bound 20)
    have ht : M.mem (s 41) (v 5) := et ▸ t.property
    have hm := row.elim fun r hr => h.source.source.omega.transitive (ZF.modelsKP hZF) _ hn m
      ((h.past.sequence.2.2 m).mpr ⟨r, hr.1⟩)
    exact ⟨natural m hm,
      hj.finite_fixed_l hZF h.source.source.omega h.source.source.transitive sn.source.transitive h.model mn
        h.source.source.omega_mem hk (h.source.source.transitive _ h.context.member _ ht) labels,
      fixedPast m i U T μ K η D ℓ V q row _ (eτ.symm ▸ hτ),
      fixedPast m i U T μ K η D ℓ V q row _ (ew.symm ▸ hw)⟩)
  have labels : Fn0_d (ι.bound 26).val ω (ι.bound 23).val :=
    Eq.mp (congrArg (fun w => Fn0_d (ι.bound 26).val w (ι.bound 23).val) h.omega)
      ((fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2))
        (⟨fun i => [ι.bound 26, ι.bound 0, ι.bound 23].get i, fun _ => ι.bound 0⟩ : Env (rt_model_l (v 5) nc) 3)).mp
          ((fn0_sat_l ext _ (.bound 0) (.bound 1) (.bound 2)).mpr state.labels)))
  have et := fn _ _ _ (images 23) (hj.finite_fixed_l hZF h.source.source.omega h.source.source.transitive
    sn.source.transitive h.model mn h.source.source.omega_mem (Eq.mp (congrArg (fun z => M.mem z ω) (request 2)) hk)
      (h.source.source.transitive _ h.context.member _ (ι.bound 23).property) labels)
  have et : (θ.bound 23).val = (ρ.bound 41).val := et.trans (request 18).symm
  have oldRoot := keepRoot (v 7) (v 16) h.root
  have fixedZ z (hz : M.mem z Z) : Rd_entry_d z z j := by
    obtain ⟨z', _, iz⟩ := hj.1.1.2.2 z (h.source.source.transitive Z hZ z hz)
    have eq := jn.1.1.1.2 z z' z (nice₂.tree.diagram.comp o (v 7) β (v 16) j π₂ oldRoot edge root₂
      z z z' (fixedRoot z hz) iz) (fixedZ₂ z hz)
    exact eq ▸ iz
  have plays := h.play.map_l I hZF h.source.source.omega h.model.1 mn.1 hj iC (images 4) (images 3) (images 20) fixedZ
  have played := played.map_l I hZF h.source.source.omega h.model.1 mn.1 hj iC (images 4) (images 3) (images 20) (fixedZ _ lowS)
  have eA := (nice₂.tree.diagram.elementary o β π₂ c₀ B S d N R₂ root₂ (nice₂.tree.root o ho) node₂ mb mn.1).1.1.1.2
    A (θ.bound 6).val A (nice₂.tree.diagram.comp o (v 7) β (v 16) j π₂ oldRoot edge root₂
      A A (θ.bound 6).val (fixedRoot A hAZ) (h.alphabet ▸ images 6)) (fixedZ₂ A hAZ)
  obtain ⟨_, t₀, j₀, _, position, _, _, advance⟩ := answer
  have xC : M.mem x C₂ := ft.transitive _ (θ.bound 6).property x (eA.symm ▸ hx)
  have hxθ : M.mem x (θ.bound 6).val := eA.symm ▸ hx
  obtain ⟨y, t, _, m, _, even, _, digit, next, _, ε, head, num, legal, _, aux, growth, keep, proper, trace⟩ :=
    advance ⟨x, xC⟩ hxθ
  have control (i : Fin 19) : ε.bound (i.castAdd 27) = θ.bound (i.castAdd 27) :=
    (head i).trans (by simp only [tg_position_env_d, Fin.addCases_left])
  have sm := (rt_successor_l ft.transitive n₂ hZF.1 (ε.bound 19) (θ.bound 19)).mp (num.symm ▸ next)
  have sm : M.SuccessorOf (ε.bound 19).val (ι.bound 19).val := en ▸ sm
  have em : (ε.bound 19).val = n := sm.eq hZF.1 ns
  have events := events.mono_l I hZF.1 mn sn.source.transitive ft.transitive n₂ P (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 20) (ε.bound 20) keep
  have trace : Tg_trace_d I N R₂ ω C₂ (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val
      (ι.bound 19).val (ε.bound 20).val (ρ.bound 41).val (ρ.bound 15).val (ρ.bound 11).val := en ▸ et ▸ trace
  have events := Tg_past_events_d.push_l I hZF past ns newest entries events _ code trace
  have events : Tg_past_events_d I ω H N R₂ C₂ (ε.bound 4).val (ε.bound 1).val (ε.bound 2).val (ε.bound 20).val :=
    (congrArg Subtype.val (control 4)).symm ▸ (congrArg Subtype.val (control 1)).symm ▸
      (congrArg Subtype.val (control 2)).symm ▸ events
  have plays := plays.mono_l I hZF.1 mn sn.source.transitive cn.member ft.transitive n₂ P (θ.bound 4) (θ.bound 3) (θ.bound 20) (ε.bound 20) keep
  have played := played.mono_l I hZF.1 mn sn.source.transitive cn.member ft.transitive n₂ P (θ.bound 4) (θ.bound 3) (θ.bound 20) (ε.bound 20) keep
  have plays := Tg_past_play_d.push_l I hZF past ns newest entries plays _ code lowS played
  have plays : Tg_past_play_d I ω H Z N R₂ C₂ (ε.bound 4).val (ε.bound 3).val (ε.bound 20).val :=
    (congrArg Subtype.val (control 4)).symm ▸ (congrArg Subtype.val (control 3)).symm ▸ plays
  have oldPlay := real.2.map_l I hZF h.source.source.omega h.model.1 mn.1 hj
    iC (images 4) (images 3) (images 20) (fixedZ _ lowReal)
  have oldPlay := oldPlay.mono_l I hZF.1 mn sn.source.transitive cn.member ft.transitive n₂ P (θ.bound 4) (θ.bound 3) (θ.bound 20) (ε.bound 20) keep
  have oldPlay : Tg_play_d I N R₂ C₂ (ε.bound 4).val (ε.bound 3).val (ε.bound 20).val s :=
    (congrArg Subtype.val (control 4)).symm ▸ (congrArg Subtype.val (control 3)).symm ▸ oldPlay
  obtain ⟨r₁, real₁⟩ := tg_issued_real_l I hZF.1 mn sn.source.transitive cn.member ft n₂ ε legal
  have Aε : (ε.bound 6).val = A := (congrArg Subtype.val (control 6)).trans eA
  have real₁ : Tg_real_d I N R₂ A C₂ (ε.bound 4).val (ε.bound 3).val (ε.bound 19).val (ε.bound 20).val r₁ := Aε ▸ real₁
  have fn := fn0_function_l (ZF.modelsKP hZF) real.1
  have fn₁ := fn0_function_l (ZF.modelsKP hZF) real₁.1
  have sub := oldPlay.subset_l I hZF.1 mn sn.source.transitive cn.member ft.transitive n₂ P ε legal real₁.2 ⟨fn.1,fn.2.1⟩ ⟨fn₁.1,fn₁.2.1⟩
    (fun i hi => (sm i).mpr (Or.inl hi))
  let ψ := tg_position_env_d (⟨fun i => θ.bound (i.castAdd 27),fun _ => θ.bound 0⟩ : Env (rt_model_l C₂ n₂) 19)
    (θ.bound 19) t₀ j₀
  have event := tg_position_digit_event_l P (rt_model_ext_l hZF.1 ft.transitive n₂) ψ position
    ((fseq_end_sat_l P (rt_model_ext_l hZF.1 ft.transitive n₂) ..).mp digit)
    ((fseq_end_sat_l P (rt_model_ext_l hZF.1 ft.transitive n₂) ..).mp aux)
  have qC : M.mem r₁ C₂ := real₁.2.mem_l I mn
  obtain ⟨z, _, hz⟩ := real₁.1.2.1 _ sm.predecessor_mem
  have zC := (rd_entry_transitive_l ft.transitive qC hz).2
  have ev := (tg_play_read_l I hZF.1 mn sn.source.transitive cn.member ft.transitive n₂ P (ε.bound 4) (ε.bound 3) (ε.bound 20) ⟨r₁,qC⟩).mp real₁.2
    (θ.bound 19) ⟨z,zC⟩ ((rt_entry_l ft.transitive n₂ hZF.1 ..).mpr (en.symm ▸ hz))
  have event : Tg_event_d P (ε.bound 4) (θ.bound 19) (ε.bound 3) (ε.bound 20) y :=
    (control 4).symm ▸ (control 3).symm ▸ event
  have zy : z = y.val := congrArg Subtype.val (tg_control_event_unique_l P (rt_model_ext_l hZF.1 ft.transitive n₂)
    _ (tg_issued_sat_l P (rt_model_ext_l hZF.1 ft.transitive n₂) ε |>.mp legal).control
    (tg_issued_sat_l P (rt_model_ext_l hZF.1 ft.transitive n₂) ε |>.mp legal).history ev event)
  have hmω := (h.source.source.omega.1.2 _ hn).elim fun k hk => hk.1.eq hZF.1 sm ▸ hk.2
  have move : Tg_turn_move_d I ω A (v 0) (v 1) (v 5) (ι.bound 4).val (ι.bound 3).val (ι.bound 19).val (ι.bound 20).val
      N R₂ C₂ (ε.bound 4).val (ε.bound 3).val (ε.bound 19).val (ε.bound 20).val x := by
    refine ⟨s,r₁,y.val,real,real₁,?_,?_⟩
    · exact ⟨(ε.bound 19).val,(ι.bound 19).val,
        ⟨⟨hmω,h.source.source.omega.members_areOrdinals (ZF.modelsKP hZF) _ hmω,fn₁.1,fn₁.2.1⟩,hn,sm,
          ⟨hn,h.source.source.omega.members_areOrdinals (ZF.modelsKP hZF) _ hn,fn.1,fn.2.1⟩,
          (Descriptive.ds_restrict_iff_l I fn fn₁.1).mpr sub,zy ▸ hz⟩⟩
    · intro he
      have he := (fs_even_l hZF h.source.source.omega ft n₂ (θ.bound 0) (θ.bound 19) ωθ).mpr (en.symm ▸ he)
      exact congrArg Subtype.val (even ((Descriptive.gm_even_sat_l P (rt_model_ext_l hZF.1 ft.transitive n₂) ψ (.bound 0) (.bound 19)).mpr he))
  let ε₀ := mn.native_env_d I C' inside nd n₂ ε
  obtain ⟨r₀, record, values⟩ := rf_record_save_l I mn.1.2.1 extN tg_issued0_m tg_issued0_closed_l C'
    nativeFinite.transitive nativeFinite.pair nd ε₀ ((mn.native_formula_l I C' inside nd n₂ tg_issued0_m ε).mp legal)
  let r := r₀.val
  let w : Fin 18 → M.Domain := fun i => [N, R₂, L, K₂, η₂, C₂, β₂, β, T₂, Q₂, G₂, E₂, H₂, H, κ, d, π₂, r].get i
  have growing : M.mem κ (ε.bound 24).val := eκ ▸ growth
  have highκ : M.MemberSubset γ κ := fun z hz => subset z (limit.1.transitive _ bound z (high z hz))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, lang⟩ := tg_issued_query_l P (rt_model_ext_l hZF.1 ft.transitive n₂) ε legal
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at lang
  have κlimit := (rt_limit_l ft.transitive n₂ (ZF.modelsKP hZF) (ε.bound 24)).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp lang.2.2.2.1)
  have images' (i : Fin 19) : Rd_entry_d (ι.bound (i.castAdd 27)).val (ε.bound (i.castAdd 27)).val j :=
    Eq.mpr (congrArg (fun z => Rd_entry_d (ι.bound (i.castAdd 27)).val z j)
      (congrArg Subtype.val (control i))) (images (i.castAdd 27))
  have treeImage := nice₂.tree.diagram.comp o (v 7) β (v 16) j π₂ oldRoot edge root₂
    S₀ (ι.bound 7).val (ε.bound 7).val treeImage (images' 7)
  have historyKeep : M.MemberSubset (v 13) H := by
    intro p hp
    obtain ⟨a, b, pair⟩ := h.past.sequence.2.1.1 p hp
    have old : Rd_entry_d a b (v 13) := ⟨p, pair, hp⟩
    obtain ⟨r, rp, hr⟩ := (entries a b ((h.past.sequence.2.2 a).mpr ⟨b, old⟩)).mpr old
    exact kpair_unique_l M hZF.1 rp pair ▸ hr
  have span : M.mem (ε.bound 19).val β₂ := ordinal_down_l (ZF.modelsKP hZF)
    (KP.successor_isOrdinal (ZF.modelsKP hZF) (h.source.source.omega.members_areOrdinals (ZF.modelsKP hZF) _ hn) sm)
    nice₂.tree.diagram.order.ordinal (fun z hz => ((sm z).mp hz).elim
      (h.tree.tree.diagram.order.ordinal.transitive _ h.span z)
      (fun eq => (hZF.1.eq_of_same_members z _ eq).symm ▸ h.span))
    (nice₂.tree.diagram.order.ordinal.transitive β ext₂.1.predecessor_mem _ ext₁.1.predecessor_mem)
  refine ⟨w, (fun i => (ε.bound i).val), ⟨sn, cn, succω (succω h.finite h.successor) ext₁.1,
    ext₂.1, nice₂, node₂, mn, root₂, image₂, anchor₂, record, values,
    (congrArg Subtype.val (control 0)).trans ωθ, (congrArg Subtype.val (control 6)).trans eA,
    fun z hz => κlimit.1.transitive κ growing z (highκ z hz), em.symm ▸ past, links, roots, events, growing, heights, span,
    ⟨S₀, treeImage, treeNames⟩, plays, critical⟩,
    ⟨k, β, T₁, Q₁, G₁, E₁, H₁, j, (θ.bound 20).val, nice₁, ext₁, ext₂, rfl, sm, edge,
    images', images 20, keep, proper, historyKeep, Y, R, μ, K, η₁, C₁, L, W, q,
    (ρ.bound 19).val, (ρ.bound 22).val, (ρ.bound 40).val, (ρ.bound 42).val, newest, ⟨_, code, rfl, rfl, rfl, request 18, rfl⟩, odd⟩, move⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 统一状态码中的原局前缀与带输入的实际后继

状态仍使用原 64 元组；原局前缀同时投影载体、关系及四个控制坐标。
后继同时保留原树边及一次真实落子，供全体有限原局共享同一选择函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

section Prefix
variable (I : kpair_convention_l.Interpretation M)

def Tg_run_real_d (A n r s : M.Domain) : Prop := ∃ X R C c b h,
  Rt_coord_d (0 : Fin 64) r X ∧ Rt_coord_d (1 : Fin 64) r R ∧
  Rt_coord_d (5 : Fin 64) r C ∧ Rt_coord_d (22 : Fin 64) r c ∧
  Rt_coord_d (21 : Fin 64) r b ∧ Rt_coord_d (38 : Fin 64) r h ∧ Tg_real_d I X R A C c b n h s
def tg_run_real_m {d} (A n r s : Term d) : Formula 1 d := set[d] ⟪∃ X R C c b h,
  ⌜rt_coord_m (0 : Fin 64)⌝ₚ(⌜r⌝ₛ,X) ∧ ⌜rt_coord_m (1 : Fin 64)⌝ₚ(⌜r⌝ₛ,R) ∧
  ⌜rt_coord_m (5 : Fin 64)⌝ₚ(⌜r⌝ₛ,C) ∧ ⌜rt_coord_m (22 : Fin 64)⌝ₚ(⌜r⌝ₛ,c) ∧
  ⌜rt_coord_m (21 : Fin 64)⌝ₚ(⌜r⌝ₛ,b) ∧ ⌜rt_coord_m (38 : Fin 64)⌝ₚ(⌜r⌝ₛ,h) ∧
  ⌜tg_real_m⌝ₚ(X,R,⌜A⌝ₛ,C,c,b,⌜n⌝ₛ,h,⌜s⌝ₛ)⟫
derive_free_closed tg_run_real_m
theorem tg_run_real_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A n r s : Term d) :
    Formula.satisfies ρ (tg_run_real_m A n r s) ↔ Tg_run_real_d I (A.eval ρ) (n.eval ρ) (r.eval ρ) (s.eval ρ) := by
  simp only [tg_run_real_m,Tg_run_real_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rt_coord_sat_l hE,tg_real_sat_l I hE,Definitional.Term.eval_weaken]; rfl

theorem Tg_run_real_d.read_l {A n r s : M.Domain} {q : Fin 64 → M.Domain}
    (h : Tg_run_real_d I A n r s) (code : Rt_tuple_d q r) : Tg_real_d I (q 0) (q 1) A (q 5) (q 22) (q 21) n (q 38) s := by
  obtain ⟨X,R,C,c,b,h,hX,hR,hC,hc,hb,hh,real⟩ := h
  have coord {i x} (h : Rt_coord_d i r x) : q i = x := by
    obtain ⟨v,p,e⟩ := h
    exact (congrFun (rt_tuple_inj_l code p) i).trans e
  exact (coord hX).symm ▸ (coord hR).symm ▸ (coord hC).symm ▸
    (coord hc).symm ▸ (coord hb).symm ▸ (coord hh).symm ▸ real

theorem Tg_run_real_d.function_l {A n r s : M.Domain} (h : Tg_run_real_d I A n r s) : Fn0_d n A s := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,real⟩ := h
  exact real.1
end Prefix

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_run_move_d (ω A n m r t x : M.Domain) : Prop := ∃ s q y,
  Tg_run_real_d I A n r s ∧ Tg_run_real_d I A m t q ∧ Fseq_end_d I ω q s y ∧ (Gm_even_d I ω n → y = x)
def tg_run_move_m {d} (ω A n m r t x : Term d) : Formula 1 d := set[d] ⟪∃ s q y,
  ⌜tg_run_real_m⌝ₚ(⌜A⌝ₛ,⌜n⌝ₛ,⌜r⌝ₛ,s) ∧ ⌜tg_run_real_m⌝ₚ(⌜A⌝ₛ,⌜m⌝ₛ,⌜t⌝ₛ,q) ∧
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,q,s,y) ∧
  (⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜n⌝ₛ) → y = ⌜x⌝ₛ)⟫
derive_free_closed tg_run_move_m
theorem tg_run_move_sat_l {d} (ρ : Env M d) (ω A n m r t x : Term d) :
    Formula.satisfies ρ (tg_run_move_m ω A n m r t x) ↔ Tg_run_move_d hZF
      (ω.eval ρ) (A.eval ρ) (n.eval ρ) (m.eval ρ) (r.eval ρ) (t.eval ρ) (x.eval ρ) := by
  simp only [tg_run_move_m,Tg_run_move_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    tg_run_real_sat_l I hZF.1,fseq_end_sat_l I hZF.1,gm_even_sat_l I hZF.1,Formula.satisfies_imp_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Definitional.Term.eval_weaken]; rfl

theorem Tg_run_code_d.real_l {ω c o C γ Z A n r : M.Domain} (h : Tg_run_code_d hZF ω c o C γ Z A n r) :
    ∃ s, Tg_run_real_d I A n r s := by
  obtain ⟨q,code,run,num⟩ := h
  let nc : Nonempty {z // M.mem z (q 5)} := ⟨⟨ω,(run.context.omega_l run.source.source.code)⟩⟩
  obtain ⟨nd,σ,eq,valid⟩ := run.read_l hZF
  let ρ := run.model.slice_env_d I ⟨q 5, run.context.member⟩ nd nc σ
  have valid : Formula.satisfies ρ tg_issued0_m :=
    (run.model.slice_formula_l I ⟨q 5, run.context.member⟩ (run.source.source.transitive (q 5) run.context.member)
      nd nc tg_issued0_m σ).mp valid
  have fs := (run.context.read_l hZF run.source.source).1
  obtain ⟨s,real⟩ := tg_issued_real_l I hZF.1 run.model run.source.source.transitive run.context.member fs nc ρ valid
  have real : Tg_real_d I (q 0) (q 1) A (q 5) (q 22) (q 21) n (q 38) s :=
    run.alphabet ▸ num ▸ eq 6 ▸ eq 4 ▸ eq 3 ▸ eq 19 ▸ eq 20 ▸ real
  exact ⟨s,q 0,q 1,q 5,q 22,q 21,q 38,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,real⟩

theorem Tg_run_code_d.real_unique_l {ω c o C γ Z A n r s t : M.Domain}
    (h : Tg_run_code_d hZF ω c o C γ Z A n r) (hs : Tg_run_real_d I A n r s) (ht : Tg_run_real_d I A n r t) : s = t := by
  obtain ⟨q,code,run,num⟩ := h
  let nc : Nonempty {z // M.mem z (q 5)} := ⟨⟨ω,(run.context.omega_l run.source.source.code)⟩⟩
  obtain ⟨nd,σ,eq,valid⟩ := run.read_l hZF
  let ρ := run.model.slice_env_d I ⟨q 5, run.context.member⟩ nd nc σ
  have valid : Formula.satisfies ρ tg_issued0_m :=
    (run.model.slice_formula_l I ⟨q 5, run.context.member⟩ (run.source.source.transitive (q 5) run.context.member)
      nd nc tg_issued0_m σ).mp valid
  have fs := (run.context.read_l hZF run.source.source).1
  have ea := (eq 6).trans run.alphabet
  have en := (eq 19).trans num
  exact Tg_real_d.unique_l I hZF.1 run.model run.source.source.transitive run.context.member fs nc ρ valid
    (ea.symm ▸ (eq 4).symm ▸ (eq 3).symm ▸ en.symm ▸ (eq 20).symm ▸ hs.read_l I code)
    (ea.symm ▸ (eq 4).symm ▸ (eq 3).symm ▸ en.symm ▸ (eq 20).symm ▸ ht.read_l I code)

theorem Tg_run_move_d.last_l {ω A n m r t x : M.Domain} (h : Tg_run_move_d hZF ω A n m r t x) :
    ∃ s q y, Tg_run_real_d I A n r s ∧ Tg_run_real_d I A m t q ∧ Fseq_end_d I ω q s y ∧
      Rd_entry_d n y q ∧ (Gm_even_d I ω n → y = x) := by
  obtain ⟨s,q,y,hs,hq,endt,even⟩ := h
  obtain ⟨l,k,d⟩ := endt
  have kn := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) (hs.function_l I)).2.1
  exact ⟨s,q,y,hs,hq,⟨l,k,d⟩,kn ▸ d.last_value,even⟩

theorem Tg_run_code_d.advance_l (hZFC : M.Models ZFC) {ω c₀ o C γ Z A n s x : M.Domain}
    (h : Tg_run_code_d (ZFC.models_zf_l hZFC) ω c₀ o C γ Z A n s) (ho : ∀ z, ¬ M.mem z o)
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z) (hAZ : M.mem A Z) (hx : M.mem x A) :
    ∃ m t, M.SuccessorOf m n ∧ Tg_run_code_d (ZFC.models_zf_l hZFC) ω c₀ o C γ Z A m t ∧
      Tg_run_edge_d (ZFC.models_zf_l hZFC) ω c₀ s t ∧ Tg_run_move_d (ZFC.models_zf_l hZFC) ω A n m s t x := by
  obtain ⟨q,code,run,num⟩ := h
  obtain ⟨v,u,next,edge,move⟩ := run.advance_l hZFC ho hγ hωZ hAZ hx
  have copy := edge
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,succ,_⟩ := copy
  let r : Fin 64 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v u
  obtain ⟨t,code'⟩ := rt_tuple_exists_l (ZF.modelsKP (ZFC.models_zf_l hZFC)) r
  have valid : Tg_run_code_d (ZFC.models_zf_l hZFC) ω c₀ o C γ Z A (u 19) t := by
    refine ⟨r,code',?_,rfl⟩
    simpa only [r,Fin.addCases_left,Fin.addCases_right] using next
  let z : Fin 128 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) q r
  refine ⟨u 19,t,num ▸ succ,valid,⟨z,?_,?_,?_⟩,?_⟩
  · simpa only [z,Fin.addCases_left] using code
  · simpa only [z,Fin.addCases_right] using code'
  · simpa only [z,r,Fin.addCases_left,Fin.addCases_right] using edge
  · obtain ⟨a,b,y,ha,hb,endt,even⟩ := move
    exact ⟨a,b,y,⟨q 0,q 1,q 5,q 22,q 21,q 38,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,⟨q,code,rfl⟩,num ▸ ha⟩,
      ⟨r 0,r 1,r 5,r 22,r 21,r 38,⟨r,code',rfl⟩,⟨r,code',rfl⟩,⟨r,code',rfl⟩,⟨r,code',rfl⟩,⟨r,code',rfl⟩,⟨r,code',rfl⟩,hb⟩,endt,num ▸ even⟩

end YesMetaZFC.SetTheory.LargeCardinal

import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswerQueries
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyDomain

/-! # 实际超幂回答通过原游戏的查询表

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
    (context : Tg_context_d ω X η C) (current : Tg_context_d ω Y η' D)
    (owner : Ep_source_d hZF ω μ K X R) (source : Ep_source_d hZF ω μ' K' Y S)
    (hierarchy : Sc_hierarchy_d Y)
    (bt : M.TransitiveSet B) (mb : Smem_d I r B T) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (j : Smap_d I ω r c B X π) (k : Smap_d I ω r d B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (anchor : Tg_anchor_d γ Z X π) (target : Tg_anchor_d γ Z Y σ)
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
  have hl := owner.omega.transitive hZF (p 24) hn (p 23) succ'.predecessor_mem
  have finite : M.mem t.val ω := hk.symm ▸ owner.omega.transitive hZF (p 23) hl (p 22) succ.predecessor_mem
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
  obtain ⟨hr, hb, hh⟩ := context.answer_members_l hZF current owner source bt mb mx my j k iC iD anchor target
    hγ hwZ nc nd ρ ζ hw round same base
  obtain ⟨sub, v, drop, subtype, _⟩ := reply
  exact ⟨B', U', D', r', m', b', h', q', l, n, row, el, en, eqD.symm, language', queries,
    eqD ▸ sub, v, drop, subtype, hr, hb, hh⟩

end YesMetaZFC.SetTheory.LargeCardinal

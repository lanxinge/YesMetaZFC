import YesMetaZFC.SetTheory.LargeCardinal.Game.PastEvents
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Game.ContinueAssemble
import YesMetaZFC.SetTheory.LargeCardinal.Game.Continue
import YesMetaZFC.SetTheory.LargeCardinal.Game.ControlCard
import YesMetaZFC.SetTheory.LargeCardinal.Game.PastRoots
import YesMetaZFC.SetTheory.LargeCardinal.Game.IssuedReset
import YesMetaZFC.SetTheory.LargeCardinal.Game.Padding
import YesMetaZFC.Model.SetTheory.Internal.MembershipSlice
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyQuality
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameStage
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail

/-! # 规则 (6) 实际选中同一旧轮

非空请求自身给出较早轮号。按该轮号读取完整存档，再由原时钟的事件单值性
识别规则 (6) 中的旧标签、旧域和旧类型；原超过公式保留在当前反射层内。
这里不假定新类型有额外实现，也不对当前层附加 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原合法请求自动选择旧完整源，历史中的旧回答与该源的存档逐字相同。 -/
theorem Tg_past_events_d.continue_l {ω H X R₀ b₀ b Q C : M.Domain}
    (model₀ : Smem_d I b₀ X R₀) (xt : M.TransitiveSet X)
    (trans : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (ρ : Env (rt_model_l C nc) 46)
    (valid : Formula.satisfies ρ tg_issued0_m) (ne : ρ.bound 23 ≠ ρ.bound 1)
    (past : Tg_past_d hZF ω (ρ.bound 19).val H X b) (links : Tg_past_links_d I H Q)
    (events : Tg_past_events_d I ω H X R₀ C (ρ.bound 4).val (ρ.bound 1).val (ρ.bound 2).val (ρ.bound 20).val) :
    ∃ h U D : (rt_model_l C nc).Domain,
      Fseq_end_d J (ρ.bound 0) (ρ.bound 20) h (ρ.bound 21) ∧
      Formula.satisfies (⟨fun i => [ρ.bound 0, ρ.bound 1, ρ.bound 2, ρ.bound 4, ρ.bound 5,
        ρ.bound 19, h, ρ.bound 22, ρ.bound 23, ρ.bound 24, ρ.bound 26, ρ.bound 28, U, D, ρ.bound 25].get i,
        ρ.free⟩ : Env (rt_model_l C nc) 15) tg_continue0_m ∧
      ∃ i Y R μ K η C₀ L V q d,
        Tg_past_at_d H (ρ.bound 22).val i Y R μ K η C₀ L V q ∧ Rd_entry_d i d Q ∧ Smem_d I d Y R ∧
        Tg_saved_d I ω Y R η C₀ L V q ∧ M.mem V X ∧ Vr_d X L V ∧ M.MemberSubset L b ∧
        ∃ nc₀ : Nonempty {x // M.mem x C₀}, ∃ σ : Env (rt_model_l C₀ nc₀) 54,
          Tg_saved_code_d Y R ω V q (fun j => (σ.bound j).val) ∧ Formula.satisfies σ tg_round0_m ∧
          (σ.bound 16).val = ω ∧
          ∀ v l t κ u z τ w : (rt_model_l C nc).Domain,
            Tg_event_d J (ρ.bound 4) (ρ.bound 22) (ρ.bound 1) h v → Tg_aux_data_d v l t κ u →
            Tg_event_d J (ρ.bound 4) (ρ.bound 22) (ρ.bound 2) h z → KPair_d (rt_model_l C nc) z τ w →
            t.val = (σ.bound 41).val ∧ τ.val = (σ.bound 15).val ∧ w.val = (σ.bound 11).val := by
  have ext := rt_model_ext_l hZF.1 trans nc
  have state := (tg_issued_sat_l J ext ρ).mp valid
  obtain ⟨h, _, _, _, U, D, _, _, _, _, _, endt, _, _, _, _, _, _, _, fork, _⟩ := tg_issued_query_l J ext ρ valid
  have cont := fork ne
  have index : M.mem (ρ.bound 22).val (ρ.bound 19).val := ((Formula.satisfies_conj_iff ..).mp cont).1
  obtain ⟨i, Y, R, μ, K, η, C₀, L, V, q, d, row, node, model, source, saved, member, rank, bound⟩ := past.select_l hZF links index
  let nc₀ : Nonempty {x // M.mem x C₀} := ⟨⟨ω, saved.context.omega_l ⟨d, model⟩⟩⟩
  obtain ⟨σ, code, round, sameω, _⟩ := saved.membership_l I hZF.1 model
    (source.source.transitive C₀ saved.context.member) nc₀
  obtain ⟨s, code', trace⟩ := events _ _ _ _ _ _ _ _ _ _ _ row
  have eq := code'.inj_l I hZF.1 code
  have et : s 41 = (σ.bound 41).val := congrFun eq 43
  have eτ : s 15 = (σ.bound 15).val := congrFun eq 17
  have ew : s 11 = (σ.bound 11).val := congrFun eq 13
  obtain ⟨_, _, _, n', t', z', en, ht, pair, traced⟩ :=
    trace.read_l I hZF.1 model₀ xt trans nc (ρ.bound 4) (ρ.bound 1) (ρ.bound 2) (ρ.bound 20)
  have en : n' = ρ.bound 22 := Subtype.ext en
  subst n'
  have traced := (tg_round_event_sat_l J ext ..).mp traced
  obtain ⟨⟨v', l', κ', u', aux, data⟩, answer⟩ := traced
  refine ⟨h, U, D, endt, cont, i, Y, R, μ, K, η, C₀, L, V, q, d, row, node, model,
    saved, member, rank, bound, nc₀, σ, code, round, sameω, ?_⟩
  intro v l t κ u z τ w oldAux oldData oldAnswer oldPair
  have ev := tg_control_event_unique_l J ext _ state.control state.history (oldAux.end_l endt) aux
  have label : t = t' := (oldData.unique_l (ev.symm ▸ data)).2.1
  have ez := tg_control_event_unique_l J ext _ state.control state.history (oldAnswer.end_l endt) answer
  have oldPair := (kpair0_sat_l hZF.1 ..).mp
    ((rt_model_delta_l trans nc (kpair0_delta_l (.bound 0) (.bound 1) (.bound 2))
      (⟨fun j => [z, τ, w].get j, fun _ => z⟩ : Env (rt_model_l C nc) 3)).mp ((kpair0_sat_l ext ..).mpr oldPair))
  have domains := kpair_injective_l M oldPair ((congrArg Subtype.val ez).symm ▸ pair)
  exact ⟨(congrArg Subtype.val label).trans (ht.trans et), domains.1.trans eτ, domains.2.trans ew⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从同一旧轮和原继续规则装配伸展输入

标签图的定义域确定旧长度；两次后继确定旧回答元数，并与当前原程序元数相等。
共同秩段搬运完整弹性语言，秩层、常量域和查询域的唯一性识别原超过关系的
低端。末项保存当前模型内给定的历史界；最终输入来自实际记录、原策略表及原继续规则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X R μ K η C Y S μ' K' η' D : M.Domain}
  (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
  (nd : Nonempty {x // M.mem x D}) (ι : Env (rt_model_l D nd) 46)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem Tg_context_d.continue_seed_l {B T w z r c d π σ C₀ L W : M.Domain}
    (context : Tg_context_d I ω X R η C) (current : Tg_context_d I ω Y S η' D)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ' K' Y S)
    (numbers : Rr_layer_d I ω B T w z) (rootExt : Rf_ext_d I B T)
    (mb : Smdl_d I r B T) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (j : Smap_d I ω r c B X π) (k : Smap_d I ω r d B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (hW : M.mem W X) (rank : Vr_d X L W) (hW' : M.mem W Y) (rank' : Vr_d Y L W)
    (hL : M.IsLimitOrdinal L) (hwW : M.mem ω W) (hτW : M.mem (p 15) W) (hWD : M.mem W D)
    (hw : p 16 = ω) (round : Formula.satisfies ρ tg_round0_m)
    (hw' : (ι.bound 0).val = ω) (issued : Formula.satisfies ι tg_issued0_m) (ne : ι.bound 23 ≠ ι.bound 1)
    (trace : Tg_trace_d I Y S ω D (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val
      (ι.bound 22).val (ι.bound 20).val (p 41) (p 15) (p 11))
    (χ₀ : (rt_model_l D nd).Domain) (hχ : M.mem χ₀.val (ι.bound 5).val) :
    ∃ ε : Env (rt_model_l D nd) 29, Formula.satisfies ε tc_seed0_m ∧
      (∀ i : Fin 10, (ε.bound ([0, 1, 3, 4, 5, 6, 17, 18, 19, 20].get i)).val =
        p ([16, 15, 24, 14, 13, 12, 6, 5, 4, 3].get i)) ∧
      (ε.bound 7).val = p 11 ∧ ε.bound 3 = ι.bound 27 ∧
      (∀ i : Fin 14, ε.bound ([0, 2, 8, 9, 13, 14, 16, 21, 22, 23, 24, 25, 26, 27].get i) =
        ι.bound ([0, 5, 24, 28, 25, 36, 37, 38, 39, 40, 41, 42, 43, 44].get i)) ∧
      M.MemberSubset (p 41) (ι.bound 23).val ∧ ε.bound 28 = χ₀ := by
  have fs := (context.read_l hZF owner).1
  have ft := (current.read_l hZF source).1
  let J := rt_pair_l ft.transitive nd hZF.1 ft.pair
  have ext := rt_model_ext_l hZF.1 ft.transitive nd
  obtain ⟨seed, data⟩ := (Formula.satisfies_conj_iff ..).mp round
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨_, _, _, _, _, _, _, first₀, last₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, labels₀⟩ := seed
  have first₀ := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp first₀)
  have last₀ := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 24) (ρ.bound 23)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp last₀)
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, _, language, _, elastic, _⟩ := data
  let f : Fin 10 → Term 54 := fun i => [.bound 16, .bound 15, .bound 24, .bound 14, .bound 13,
    .bound 12, .bound 6, .bound 5, .bound 4, .bound 3].get i
  have language : Formula.satisfies (Definitional.Env.substitute ρ f) ee_language0_m :=
    (Formula.satisfies_bind ρ f ee_language0_m).mp language
  obtain ⟨_, _, nd', θ, same, language⟩ := context.language_peer_l hZF nc _ current owner source numbers rootExt mb mx my
    j k iC iD hW rank hW' rank' hL hwW hτW hWD hw language
  have θω : θ.bound 0 = ι.bound 0 := Subtype.ext ((same 0).trans (hw.trans hw'.symm))
  let ξ : Env (rt_model_l C nc) 3 := ⟨fun i => [ρ.bound 22, ρ.bound 16, ρ.bound 41].get i, ρ.free⟩
  have labels : Fn0_d (p 22) ω (p 41) := hw ▸ (fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
    ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ξ).mp
      ((fn0_sat_l (rt_model_ext_l hZF.1 fs.transitive nc) ξ (.bound 0) (.bound 1) (.bound 2)).mpr
        ((fn0_sat_l (rt_model_ext_l hZF.1 fs.transitive nc) _ (.bound 6) (.bound 0) (.bound 25)).mp labels₀)))
  obtain ⟨_, _, _, n', t', z', en, ht, oldPair, traced⟩ :=
    trace.read_l I hZF.1 my source.transitive ft.transitive nd (ι.bound 4) (ι.bound 1) (ι.bound 2) (ι.bound 20)
  have en : n' = ι.bound 22 := Subtype.ext en
  subst n'
  let u : (rt_model_l D nd).Domain := ⟨p 11, (oldPair.mem_l M ft.transitive z'.property).2⟩
  have elastic' : Formula.satisfies (θ.push u)
      (ee_elastic_m (.bound 7) (.bound 8) (.bound 9) (.bound 10) .newest) := by
    simp only [ee_elastic_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at elastic ⊢
    change (M.mem (θ.bound 6).val (p 11) ∧ M.mem (θ.bound 7).val (p 11)) ∧
      M.mem (θ.bound 8).val (p 11) ∧ M.mem (θ.bound 9).val (p 11)
    rw [same 6, same 7, same 8, same 9]
    exact elastic
  have pair : KPair_d M z'.val (θ.bound 1).val u.val := (same 1).symm ▸ oldPair
  have last : M.SuccessorOf (θ.bound 2).val (p 23) := (same 2).symm ▸ last₀
  obtain ⟨ε, seed, oldEq, typeEq, arity, newEq, sub, boundEq⟩ :=
    tg_continue_assemble_l hZF ft nd ι issued hw' ne θ language θω u t' z' χ₀ elastic'
      (ht.symm ▸ labels) first₀ last ((tg_round_event_sat_l J ext ..).mp traced) pair hχ
  have coords (i : Fin 10) : ((Definitional.Env.substitute ρ f).bound i).val =
      p ([16,15,24,14,13,12,6,5,4,3].get i) := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))) i
  exact ⟨ε, seed, fun i => (congrArg Subtype.val (oldEq i)).trans ((same i).trans (coords i)),
    congrArg Subtype.val typeEq, arity, newEq, ht ▸ sub, boundEq⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原已发出请求自动完成继续轮

旧轮和当前请求确定完整伸展输入。实际源按旧回答域重定基，原武丁公式给出
当前正则性；给定历史界进入同一原生伸展输入，随后构造两条真实树边。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.continue_tree_l {ω X η C Y η₀ C₀ μ μ₀ K K₀ R S c₀ α ξ T J G E H
    k c d o π π₀ Cᵣ γ Z₀ ζ V H₀ Lᵣ Vᵣ qᵣ : M.Domain}
    (context : Tg_context_d I ω X R η C) (prior : Tg_context_d I ω Y S η₀ C₀)
    (owner : Ic_model_d hZF ω μ K X R) (source : Ic_model_d hZF ω μ₀ K₀ Y S)
    (nc : Nonempty {x // M.mem x C}) (nc₀ : Nonempty {x // M.mem x C₀})
    (ρ₀ : Env (rt_model_l C₀ nc₀) 54) (old : Formula.satisfies ρ₀ tg_round0_m) (hw₀ : (ρ₀.bound 16).val = ω)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (hd : Rd_entry_d k d J) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (ho : ∀ x, ¬ M.mem x o) (root : It_map_d G o ξ π) (root₀ : It_map_d G o k π₀)
    (iRoot : Rd_entry_d Cᵣ C π) (iRoot₀ : Rd_entry_d Cᵣ C₀ π₀)
    (anchor : Tg_anchor_d I γ Z₀ X R π) (priorAnchor : Tg_anchor_d I γ Z₀ Y S π₀)
    (lower : M.MemberSubset γ (ρ₀.bound 15).val) (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z₀)
    (ι : Env (rt_model_l C nc) 46) (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val = ω)
    (ne : ι.bound 23 ≠ ι.bound 1) (letters : M.mem (ι.bound 6).val Z₀)
    (row : Tg_past_at_d H₀ (ι.bound 22).val k Y S μ₀ K₀ η₀ C₀ Lᵣ Vᵣ qᵣ)
    (code : Tg_saved_code_d Y S ω Vᵣ qᵣ (fun i => (ρ₀.bound i).val))
    (lowS : M.mem (ρ₀.bound 40).val Z₀)
    (played : Tg_play_d I X R C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ₀.bound 40).val)
    (trace : Tg_trace_d I X R ω C (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val (ι.bound 22).val
      (ι.bound 20).val (ρ₀.bound 41).val (ρ₀.bound 15).val (ρ₀.bound 11).val)
    (hV : M.mem V X) (rank : Vr_d X ζ V) (hV' : M.mem V Y) (rank' : Vr_d Y ζ V)
    (hζ : M.IsLimitOrdinal ζ) (hVC : M.mem V C₀) (hζδ : M.mem ζ (ι.bound 5).val)
    (hκV : M.mem (ρ₀.bound 15).val V) (hU : M.mem (ρ₀.bound 13).val V)
    (hD : M.mem (ρ₀.bound 12).val V) (hu : M.mem (ρ₀.bound 11).val V)
    (χ : (rt_model_l C nc).Domain) (hχ : M.mem χ.val (ι.bound 5).val)
    (above : ∀ i ν, Rd_entry_d i ν H → M.mem ν χ.val ∨ ν = χ.val) :
    ∃ ρ : Env (rt_model_l C nc) 29, Formula.satisfies ρ tc_seed0_m ∧
      (∀ i : Fin 10, (ρ.bound ([0, 1, 3, 4, 5, 6, 17, 18, 19, 20].get i)).val =
        (ρ₀.bound ([16, 15, 24, 14, 13, 12, 6, 5, 4, 3].get i)).val) ∧
      (ρ.bound 7).val = (ρ₀.bound 11).val ∧ ρ.bound 3 = ι.bound 27 ∧
      (∀ i : Fin 14, ρ.bound ([0, 2, 8, 9, 13, 14, 16, 21, 22, 23, 24, 25, 26, 27].get i) =
        ι.bound ([0, 5, 24, 28, 25, 36, 37, 38, 39, 40, 41, 42, 43, 44].get i)) ∧
      Tg_tree_step_d hZF ω X R η c₀ α ξ T J G E c o Cᵣ γ Z₀ H₀ nc ι := by
  have fs := (context.read_l hZF owner.source).1
  have ft := (prior.read_l hZF source.source).1
  let P := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l P ext ι).mp issued
  have control := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  have card : Sc_inaccessible_d ω X (ι.bound 5).val :=
    context.control_card_l hZF owner.source nc _ state.control hw
  have δlimit := card.limit_l (ZF.modelsKP hZF) owner.source.transitive (owner.source.algebra_l (ZF.modelsKP hZF)).pair
  obtain ⟨_, _, _, iₛ⟩ := owner.read_l hZF
  have δregular := (iₛ _ card).1
  obtain ⟨oldSeed, oldBody⟩ := (Formula.satisfies_conj_iff ..).mp old
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at oldSeed
  have empty₀ := (Formula.satisfies_isEmpty_iff ..).mp oldSeed.2.1
  have empty := (Formula.satisfies_isEmpty_iff ..).mp rules.2.1
  have he : (ι.bound 1).val = (ρ₀.bound 17).val := hZF.1.eq_of_same_members _ _ (fun x =>
    iff_of_false (fun hx => empty ⟨x, fs.transitive _ (ι.bound 1).property x hx⟩ hx)
      (fun hx => empty₀ ⟨x, ft.transitive _ (ρ₀.bound 17).property x hx⟩ hx))
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at oldBody
  have language := oldBody.2.2.2.2.2.2.1
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m, Formula.satisfies_conj_iff] at language
  have τlimit := (rt_limit_l ft.transitive nc₀ (ZF.modelsKP hZF) (ρ₀.bound 15)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have ωτ := owner.source.omega.subset_limitOrdinal (ZF.modelsKP hZF) τlimit
  have hτX := owner.source.transitive V hV _ hκV
  have hτY := source.source.transitive V hV' _ hκV
  obtain ⟨K', owner'⟩ := owner.rebase_l hZF hτX ωτ
    (sc_ordinal_small_l hZF owner.source.omega owner.source.transitive mx owner.source.theory hτX τlimit.1)
  obtain ⟨K₁, source'⟩ := source.rebase_l hZF hτY ωτ
    (sc_ordinal_small_l hZF source.source.omega source.source.transitive my source.source.theory hτY τlimit.1)
  have hωV := rank.subset_mem_l owner.source.transitive hV hκV owner.source.omega_mem ωτ
  have hζC := fs.transitive _ (ι.bound 5).property ζ hζδ
  have hVC' := ((context.rank_l (ZF.modelsKP hZF) owner.source.transitive owner.source.code).rank_l hZF owner.source.transitive context.member (context.limit_l (ZF.modelsKP hZF) owner.source.transitive owner.source.code) hζC hV rank).1
  obtain ⟨B, R₀, wᵣ, Kᵣ, zᵣ, mb, rootSource, numbers⟩ := (tree.tree.sources o c₀ (tree.tree.root o ho)).objects
  have j := tree.tree.diagram.elementary o k π₀ c₀ B R₀ d Y S root₀ (tree.tree.root o ho) hd mb my.1
  have k' := tree.tree.diagram.elementary o ξ π c₀ B R₀ c X R root (tree.tree.root o ho) hc mb mx.1
  obtain ⟨ρ, seed, oldEq, typeEq, arity, newEq, labelSub, boundEq⟩ := prior.continue_seed_l hZF nc₀ ρ₀ nc ι context source.source owner.source
    numbers rootSource.ext mb my mx j k' iRoot₀ iRoot
    hV' rank' hV rank hζ hωV hκV hVC' hw₀ old hw issued ne trace χ hχ
  have h0 : (ρ.bound 0).val = ω := (oldEq 0).trans hw₀
  have h1 : (ρ.bound 1).val = (ρ₀.bound 15).val := oldEq 1
  have h3 : (ρ.bound 3).val = (ρ₀.bound 24).val := oldEq 2
  have h5 : (ρ.bound 5).val = (ρ₀.bound 13).val := oldEq 4
  have h6 : (ρ.bound 6).val = (ρ₀.bound 12).val := oldEq 5
  have h2 : (ρ.bound 2).val = (ι.bound 5).val := congrArg Subtype.val (newEq 1)
  have h8 : (ρ.bound 8).val = (ι.bound 24).val := congrArg Subtype.val (newEq 2)
  have links : ∀ i : Fin 6, (ι.bound ([0, 1, 27, 28, 24, 25].get i)).val =
      [ω, (ρ₀.bound 17).val, (ρ.bound 3).val, (ρ.bound 9).val, (ρ.bound 8).val, (ρ.bound 13).val].get i := by
    intro i
    exact Fin.cases hw (Fin.cases he (Fin.cases (congrArg Subtype.val arity.symm)
      (Fin.cases (congrArg Subtype.val (newEq 3).symm) (Fin.cases h8.symm
        (Fin.cases (congrArg Subtype.val (newEq 4).symm) (fun j => Fin.elim0 j)))))) i
  have lower' : M.MemberSubset γ (ρ.bound 1).val := h1.symm ▸ lower
  have δlimit' : M.IsLimitOrdinal (ρ.bound 2).val := h2.symm ▸ δlimit
  have δregular' : Sc_regular_d X (ρ.bound 2).val := h2.symm ▸ δregular
  have hζδ' : M.mem ζ (ρ.bound 2).val := h2.symm ▸ hζδ
  have hκV' : M.mem (ρ.bound 1).val V := h1.symm ▸ hκV
  have hU' : M.mem (ρ.bound 5).val V := h5.symm ▸ hU
  have hD' : M.mem (ρ.bound 6).val V := h6.symm ▸ hD
  have hu' : M.mem (ρ.bound 7).val V := typeEq.symm ▸ hu
  have above' : ∀ i ν, Rd_entry_d i ν H → M.mem ν (ρ.bound 28).val ∨ ν = (ρ.bound 28).val :=
    fun i ν hn => (congrArg Subtype.val boundEq).symm ▸ above i ν hn
  have codes : ∀ i : Fin 9, (ρ.bound ([14, 16, 21, 22, 23, 24, 25, 26, 27].get i)).val =
      (ι.bound ([36, 37, 38, 39, 40, 41, 42, 43, 44].get i)).val := by
    intro i
    exact Fin.cases (congrArg Subtype.val (newEq 5)) (Fin.cases (congrArg Subtype.val (newEq 6))
      (Fin.cases (congrArg Subtype.val (newEq 7)) (Fin.cases (congrArg Subtype.val (newEq 8))
        (Fin.cases (congrArg Subtype.val (newEq 9)) (Fin.cases (congrArg Subtype.val (newEq 10))
          (Fin.cases (congrArg Subtype.val (newEq 11)) (Fin.cases (congrArg Subtype.val (newEq 12))
            (Fin.cases (congrArg Subtype.val (newEq 13)) (fun j => Fin.elim0 j))))))))) i
  exact ⟨ρ, seed, oldEq, typeEq, arity, newEq,
    context.continue_image_tree_l hZFC nc ρ prior nc₀ ρ₀ old typeEq.symm h1.symm h3.symm h5.symm
      (h1.symm ▸ owner') (h1.symm ▸ source') tree succ hc hd mx my ho root root₀ iRoot iRoot₀ anchor priorAnchor
      lower' hγ hωZ ι issued ne row code lowS played labelSub links codes letters h0 δlimit' δregular'
      hV rank hV' rank' hζ hVC hζδ' hκV' hU' hD' hu' above' seed⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 统一历史自动驱动非空继续分支

轮号由原规则读取；旧完整源、根图、固定锚点、共同层及下界均从同一历史行
取得。增长规则给出的当前界足以覆盖整列支撑，调用方不再选择旧源或构造 seed。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_past_events_d.continue_tree_l {ω X R μ K η C c₀ α ξ T Q G E L H b c o π Cᵣ γ Z : M.Domain}
    (context : Tg_context_d I ω X R η C) (source : Ic_model_d hZF ω μ K X R)
    (nc : Nonempty {x // M.mem x C}) (ι : Env (rt_model_l C nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val = ω) (ne : ι.bound 23 ≠ ι.bound 1)
    (tree : It_pnice_d hZF ω c₀ α T Q G E L) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (mx : Smem_d I c X R) (ho : ∀ x, ¬ M.mem x o)
    (root : It_map_d G o ξ π) (image : Rd_entry_d Cᵣ C π) (anchor : Tg_anchor_d I γ Z X R π)
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z) (letters : M.mem (ι.bound 6).val Z)
    (past : Tg_past_d hZF ω (ι.bound 19).val H X b) (links : Tg_past_links_d I H Q)
    (roots : Tg_past_roots_d I ω H G o Cᵣ γ Z)
    (events : Tg_past_events_d I ω H X R C (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val (ι.bound 20).val)
    (plays : Tg_past_play_d I ω H Z X R C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val)
    (below : M.mem b (ι.bound 24).val) (bounds : ∀ i ν, Rd_entry_d i ν L → M.mem ν b ∨ ν = b) :
    Tg_tree_step_d hZF ω X R η c₀ α ξ T Q G E c o Cᵣ γ Z H nc ι := by
  have fs := (context.read_l hZF source.source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ι).mp issued
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, fork, _, _, _, _, _, _, language⟩ :=
    tg_issued_query_l J ext ι issued
  have index : M.mem (ι.bound 22).val (ι.bound 19).val := ((Formula.satisfies_conj_iff ..).mp (fork ne)).1
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at language
  have κlimit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ι.bound 24)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.2.2.1)
  have card : Sc_inaccessible_d ω X (ι.bound 5).val :=
    context.control_card_l hZF source.source nc _ state.control hw
  have δlimit := card.limit_l (ZF.modelsKP hZF) source.source.transitive (source.source.algebra_l (ZF.modelsKP hZF)).pair
  obtain ⟨k, Y, S, μ₀, K₀, η₀, C₀, ℓ, V, q, d, row, node, model, sy, saved, member, rank, bound⟩ :=
    past.select_l hZF links index
  let nc₀ : Nonempty {x // M.mem x C₀} := ⟨⟨ω, saved.context.omega_l ⟨d, model⟩⟩⟩
  obtain ⟨ρ₀, code, round, hw₀, hκV, hU, hD, hu⟩ := saved.membership_l I hZF.1 model
    (sy.source.transitive C₀ saved.context.member) nc₀
  obtain ⟨⟨π₀, root₀, image₀, anchor₀⟩, v, code', high⟩ := roots _ _ _ _ _ _ _ _ _ _ _ row
  have eq : v 15 = (ρ₀.bound 15).val := congrFun (code'.inj_l I hZF.1 code) 17
  have high : M.MemberSubset γ (ρ₀.bound 15).val := eq ▸ high
  obtain ⟨v, code', traced⟩ := events _ _ _ _ _ _ _ _ _ _ _ row
  have eq := code'.inj_l I hZF.1 code
  have et : v 41 = (ρ₀.bound 41).val := congrFun eq 43
  have eτ : v 15 = (ρ₀.bound 15).val := congrFun eq 17
  have ew : v 11 = (ρ₀.bound 11).val := congrFun eq 13
  have trace : Tg_trace_d I X R ω C (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val (ι.bound 22).val
      (ι.bound 20).val (ρ₀.bound 41).val (ρ₀.bound 15).val (ρ₀.bound 11).val := et ▸ eτ ▸ ew ▸ traced
  obtain ⟨v, code', lowS, played⟩ := plays _ _ _ _ _ _ _ _ _ _ _ row
  have eq : v 40 = (ρ₀.bound 40).val := congrFun (code'.inj_l I hZF.1 code) 42
  have lowS := eq ▸ lowS
  have played := eq ▸ played
  have limitOld := saved.limit_l I (ZF.modelsKP hZF) sy.source.transitive model
  have rankOld := saved.rank_l I (ZF.modelsKP hZF) sy.source.transitive model
  have memOld := saved.member_l I model
  have hℓκ := ordinal_down_l (ZF.modelsKP hZF) limitOld.1 κlimit.1 bound below
  have hℓδ := δlimit.1.transitive (ι.bound 24).val state.bound ℓ hℓκ
  let χ : (rt_model_l C nc).Domain := ⟨b, fs.transitive _ (ι.bound 24).property b below⟩
  have hχ : M.mem χ.val (ι.bound 5).val := δlimit.1.transitive _ state.bound b below
  obtain ⟨_, _, _, _, _, _, step⟩ := context.continue_tree_l hZFC saved.context source sy nc nc₀ ρ₀ round hw₀ tree succ hc node mx model
    ho root root₀ image image₀ anchor anchor₀ high hγ hωZ ι issued hw ne letters row code lowS played trace member rank
    (sy.source.transitive C₀ saved.context.member V memOld) rankOld limitOld memOld
    hℓδ hκV hU hD hu χ hχ bounds
  exact step

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部内部轮号上的统一树后继

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
    (context : Tg_context_d I ω X R η C) (source : Ic_model_d hZF ω μ K X R)
    (nc : Nonempty {x // M.mem x C}) (ι : Env (rt_model_l C nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val = ω)
    (tree : It_pnice_d hZF ω c₀ α T Q G E L) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (mx : Smem_d I c X R) (ho : ∀ x, ¬ M.mem x o)
    (root : It_map_d G o ξ π) (image : Rd_entry_d Cᵣ C π) (anchor : Tg_anchor_d I γ Z X R π)
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z) (letters : M.mem (ι.bound 6).val Z)
    (lower : M.MemberSubset γ (ι.bound 24).val)
    (past : Tg_past_d hZF ω (ι.bound 19).val H X b) (links : Tg_past_links_d I H Q)
    (roots : Tg_past_roots_d I ω H G o Cᵣ γ Z)
    (events : Tg_past_events_d I ω H X R C (ι.bound 4).val (ι.bound 1).val (ι.bound 2).val (ι.bound 20).val)
    (plays : Tg_past_play_d I ω H Z X R C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val)
    (below : M.mem b (ι.bound 24).val) (bounds : ∀ i ν, Rd_entry_d i ν L → M.mem ν b ∨ ν = b) :
    Tg_tree_step_d hZF ω X R η c₀ α ξ T Q G E c o Cᵣ γ Z H nc ι := by
  classical
  obtain ⟨_, hZ, rankZ, _⟩ := anchor.read_l (ZF.modelsKP hZF) source.source.transitive mx
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
    -- 按轮与树边分别解构，避免一次展开整个后继证书。
    obtain ⟨v, round, first⟩ :=
      context.pad_round_l hZFC nc ε source tree succ hc mx hwε ho root image anchor lowerε above seed
    obtain ⟨β, T₁, Q₁, G₁, E₁, id, π₁, padded, pad, node₁, padEdge, identity, padEmpty,
      root₁, image₁, anchor₁, second⟩ := first
    obtain ⟨β₂, T₂, Q₂, G₂, E₂, L₂, d, j, N, R₂, K₂, ℓ, F, κ, U, D, u, η₂, C₂, W,
      next, extend, node₂, edge, mn, ready, ultra, critical, payload, limit, bound, subset, heights, rest⟩ := second
    obtain ⟨iU, iD, iu, reply, iη, iC, context₂, _, hW, _, common, level, _, _, _, _,
      π₂, root₂, image₂, anchor₂, update⟩ := rest
    let ρ := tg_round_env_d ε v
    have sameS : (ρ.bound 19).val = (ι.bound 7).val := congrArg Subtype.val (head 3)
    have padMap := padded.tree.diagram.elementary ξ α id c X R c X R padEdge
      (pad.2.2.1 ξ c hc) node₁ mx.1 mx.1
    obtain ⟨S', _, hS⟩ := padMap.1.1.2.2 (ι.bound 7).val
      (source.source.transitive C context.member _ (ι.bound 7).property)
    have hS : Rd_entry_d (ι.bound 7).val (ρ.bound 19).val id :=
      sameS.symm ▸ (identity _ _ hS).symm ▸ hS
    have request : Tg_request_d Eq (fun i => (ι.bound i).val) (fun i => (ρ.bound i).val) :=
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
      rankZ.transitive_l source.source.transitive hZ ω hωZ _
        (num_mem_l hZF.1 source.source.omega (show Num_d 0 (ι.bound 1).val from he))
    have play : Tg_play_d I X R C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ.bound 40).val := by
      apply digitZero.symm ▸ (tg_play_read_l I hZF.1 mx source.source.transitive context.member fs.transitive nc J
        (ι.bound 4) (ι.bound 3) (ι.bound 20) (ι.bound 1)).mpr
      rintro i x ⟨p, _, hp⟩
      exact (empty₀ p hp).elim
    have padLower : ∀ p κ L F, Rd_entry_d ξ p E₁ → It_payload_d p κ L F →
        ∃ c X R, Rd_entry_d ξ c Q₁ ∧ Smdl_d I c X R ∧ It_lower_d I γ X R κ := by
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

/-! ## 统一递归的可编码不变量

十八项保存当前模型、有限树、完整历史及原请求的记录码。所有旧轮由同一
内部函数图索引；表、反射层、根图和共同层均是已实现对象。扩展器列逐项
保留原低层高度以下无临界点的不变量，而不只保留偶数边的单步临界点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

-- X,R,μ,K,η,C,α,ξ,T,Q,G,E,L,H,b,c,π,r；u 是同一记录码 r 的四十六项。
structure Tg_run_d (ω c₀ o Cᵣ γ Z A : M.Domain) (v : Fin 18 → M.Domain) (u : Fin 46 → M.Domain) : Prop where
  source : Ic_model_d hZF ω (v 2) (v 3) (v 0) (v 1)
  context : Tg_context_d I ω (v 0) (v 1) (v 4) (v 5)
  finite : M.mem (v 7) ω
  successor : M.SuccessorOf (v 6) (v 7)
  tree : It_pnice_d hZF ω c₀ (v 6) (v 8) (v 9) (v 10) (v 11) (v 12)
  node : Rd_entry_d (v 7) (v 15) (v 9)
  model : Smem_d I (v 15) (v 0) (v 1)
  root : It_map_d (v 10) o (v 7) (v 16)
  image : Rd_entry_d Cᵣ (v 5) (v 16)
  anchor : Tg_anchor_d I γ Z (v 0) (v 1) (v 16)
  record : Rf_record_d I (v 0) (v 1) tg_issued0_m (v 5) (v 17)
  values : Rf_tuple_d I (v 0) (v 1) u (v 17)
  omega : u 0 = ω
  alphabet : u 6 = A
  lower : M.MemberSubset γ (u 24)
  past : Tg_past_d hZF ω (u 19) (v 13) (v 0) (v 14)
  links : Tg_past_links_d I (v 13) (v 9)
  roots : Tg_past_roots_d I ω (v 13) (v 10) o Cᵣ γ Z
  events : Tg_past_events_d I ω (v 13) (v 0) (v 1) (v 5) (u 4) (u 1) (u 2) (u 20)
  below : M.mem (v 14) (u 24)
  bounds : ∀ i ν, Rd_entry_d i ν (v 12) → M.mem ν (v 14) ∨ ν = v 14
  span : M.mem (u 19) (v 6)
  tree_name : Tg_common_tree_d ω (v 13) (v 10) o (v 16) (u 7)
  play : Tg_past_play_d I ω (v 13) Z (v 0) (v 1) (v 5) (u 4) (u 3) (u 20)
  critical : It_critical_bound_d I γ (v 9) (v 11)

theorem Tg_run_d.read_l {ω c₀ o Cᵣ γ Z A : M.Domain} {v : Fin 18 → M.Domain} {u : Fin 46 → M.Domain}
    (h : Tg_run_d hZF ω c₀ o Cᵣ γ Z A v u) :
    let X₀ := smdl_structure_l I (R := v 1) h.model.1.2.1
    let C : X₀.Domain := ⟨v 5, h.context.member⟩
    ∃ nc : Nonempty {x : X₀.Domain // X₀.mem x C}, ∃ ι : Env (rt_model_l C nc) 46,
      (∀ i, (ι.bound i).val.val = u i) ∧ Formula.satisfies ι tg_issued0_m := by
  let X₀ := smdl_structure_l I (R := v 1) h.model.1.2.1
  let C : X₀.Domain := ⟨v 5, h.context.member⟩
  have ext := smem_ext_l I h.model.1 h.model.2 h.source.source.transitive hZF.1
  have finite := h.context.finite_l h.model.1.2.1 ext
  let nd : Nonempty {x : X₀.Domain // X₀.mem x C} :=
    ⟨⟨⟨ω, h.context.omega_mem⟩, finite.omega_mem⟩⟩
  obtain ⟨ρ, eq, valid⟩ := h.record.values_l I h.model.1.2.1 ext tg_issued0_m tg_issued0_closed_l C
    ⟨v 17, h.record.elim fun mem _ => mem 1⟩ finite.transitive nd h.values
  exact ⟨nd, ρ, eq, valid⟩

def Tg_run_next_d (ω c₀ : M.Domain) (v : Fin 18 → M.Domain) (u : Fin 46 → M.Domain)
    (w : Fin 18 → M.Domain) (t : Fin 46 → M.Domain) : Prop :=
  ∃ k β T Q G E L j h,
    It_pnice_d hZF ω c₀ β T Q G E L ∧
    It_extension_d (v 6) (v 7) k (v 8) (v 9) (v 10) (v 11) β T Q G E ∧
    It_extension_d β (v 6) (v 7) T Q G E (w 6) (w 8) (w 9) (w 10) (w 11) ∧
    w 7 = β ∧ M.SuccessorOf (t 19) (u 19) ∧ It_map_d (w 10) (v 7) (w 7) j ∧
    (∀ i : Fin 19, Rd_entry_d (u (i.castAdd 27)) (t (i.castAdd 27)) j) ∧
    Rd_entry_d (u 20) h j ∧ M.MemberSubset h (t 20) ∧ h ≠ t 20 ∧ M.MemberSubset (v 13) (w 13) ∧
    ∃ Y R μ K η C L V q S n s g, Tg_past_at_d (w 13) (u 19) (v 6) Y R μ K η C L V q ∧
      Tg_saved_branch_d Y R ω V q S n s (u 23) g ∧ Tg_odd_d ω (v 13) (v 7) (v 6) k G (u 1) (u 23) (u 22) (u 7) S n s g

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 统一历史不变量的原一阶编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def tg_run_m {d} (ω c₀ o C γ Z A : Term d) (v : Fin 18 → Term d) (u : Fin 46 → Term d) : Formula 1 d := set[d] ⟪
  ⌜ic_model_m⌝ₚ(⌜ω⌝ₛ, ⌜v 2⌝ₛ, ⌜v 3⌝ₛ, ⌜v 0⌝ₛ, ⌜v 1⌝ₛ) ∧
  ⌜tg_context_data_m⌝ₚ(⌜ω⌝ₛ, ⌜v 0⌝ₛ, ⌜v 1⌝ₛ, ⌜v 4⌝ₛ, ⌜v 5⌝ₛ) ∧ ⌜v 7⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜KP.succ0_m⌝ₚ(⌜v 6⌝ₛ, ⌜v 7⌝ₛ) ∧
  ⌜it_pnice_m⌝ₚ(⌜ω⌝ₛ, ⌜c₀⌝ₛ, ⌜v 6⌝ₛ, ⌜v 8⌝ₛ, ⌜v 9⌝ₛ, ⌜v 10⌝ₛ, ⌜v 11⌝ₛ, ⌜v 12⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜v 7⌝ₛ, ⌜v 15⌝ₛ, ⌜v 9⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜v 15⌝ₛ, ⌜v 0⌝ₛ, ⌜v 1⌝ₛ) ∧
  ⌜it_map_m⌝ₚ(⌜v 10⌝ₛ, ⌜o⌝ₛ, ⌜v 7⌝ₛ, ⌜v 16⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜C⌝ₛ, ⌜v 5⌝ₛ, ⌜v 16⌝ₛ) ∧
  ⌜tg_anchor_m⌝ₚ(⌜γ⌝ₛ, ⌜Z⌝ₛ, ⌜v 0⌝ₛ, ⌜v 1⌝ₛ, ⌜v 16⌝ₛ) ∧
  ⌜rf_record_m (𝒞 := kpair_convention_l) tg_issued0_m⌝ₚ(⌜v 0⌝ₛ, ⌜v 1⌝ₛ, ⌜v 5⌝ₛ, ⌜v 17⌝ₛ) ∧
  ⌜rf_tuple_m (𝒞 := kpair_convention_l) (v 0) (v 1) u⌝ₚ(⌜v 17⌝ₛ) ∧
  ⌜u 0⌝ₛ = ⌜ω⌝ₛ ∧ ⌜u 6⌝ₛ = ⌜A⌝ₛ ∧ ⌜γ⌝ₛ ⊆ ⌜u 24⌝ₛ ∧
  ⌜tg_past_m⌝ₚ(⌜ω⌝ₛ, ⌜u 19⌝ₛ, ⌜v 13⌝ₛ, ⌜v 0⌝ₛ, ⌜v 14⌝ₛ) ∧ ⌜tg_past_links_m⌝ₚ(⌜v 13⌝ₛ, ⌜v 9⌝ₛ) ∧
  ⌜tg_past_roots_m⌝ₚ(⌜ω⌝ₛ, ⌜v 13⌝ₛ, ⌜v 10⌝ₛ, ⌜o⌝ₛ, ⌜C⌝ₛ, ⌜γ⌝ₛ, ⌜Z⌝ₛ) ∧
  ⌜tg_past_events_m⌝ₚ(⌜ω⌝ₛ, ⌜v 13⌝ₛ, ⌜v 0⌝ₛ, ⌜v 1⌝ₛ, ⌜v 5⌝ₛ, ⌜u 4⌝ₛ, ⌜u 1⌝ₛ, ⌜u 2⌝ₛ, ⌜u 20⌝ₛ) ∧
  ⌜v 14⌝ₛ ∈ ⌜u 24⌝ₛ ∧ (∀ i ν, ⌜rd_entry0_m⌝ₚ(i, ν, ⌜v 12⌝ₛ) → ν ∈ ⌜v 14⌝ₛ ∨ ν = ⌜v 14⌝ₛ) ∧
  ⌜u 19⌝ₛ ∈ ⌜v 6⌝ₛ ∧ ⌜tg_common_tree_m⌝ₚ(⌜ω⌝ₛ, ⌜v 13⌝ₛ, ⌜v 10⌝ₛ, ⌜o⌝ₛ, ⌜v 16⌝ₛ, ⌜u 7⌝ₛ) ∧
  ⌜tg_past_play_m⌝ₚ(⌜ω⌝ₛ,⌜v 13⌝ₛ,⌜Z⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 5⌝ₛ,⌜u 4⌝ₛ,⌜u 3⌝ₛ,⌜u 20⌝ₛ) ∧
  ⌜it_critical_bound_m⌝ₚ(⌜γ⌝ₛ,⌜v 9⌝ₛ,⌜v 11⌝ₛ)⟫

@[simp] theorem tg_run_closed_l {d} (ω c₀ o C γ Z A : Term d) (v : Fin 18 → Term d) (u : Fin 46 → Term d)
    (hw : ω.freeSupport = []) (hc : c₀.freeSupport = []) (ho : o.freeSupport = []) (hC : C.freeSupport = [])
    (hγ : γ.freeSupport = []) (hZ : Z.freeSupport = []) (hA : A.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hu : ∀ i, (u i).freeSupport = []) : (tg_run_m ω c₀ o C γ Z A v u).FreeClosed := by
  simp -implicitDefEqProofs [tg_run_m, Definitional.Formula.FreeClosed, hw, hc, ho, hC, hγ, hZ, hA, hv, hu,
    rf_record_closed_l _ tg_issued0_closed_l _ _ _ _ (hv 0) (hv 1) (hv 5) (hv 17)]

theorem tg_run_sat_l {d} (η : Env M d) (ω c₀ o C γ Z A : Term d) (v : Fin 18 → Term d) (u : Fin 46 → Term d) :
    Formula.satisfies η (tg_run_m ω c₀ o C γ Z A v u) ↔
      Tg_run_d hZF (ω.eval η) (c₀.eval η) (o.eval η) (C.eval η) (γ.eval η) (Z.eval η) (A.eval η)
        (fun i => (v i).eval η) (fun i => (u i).eval η) := by
  simp only [tg_run_m, Formula.satisfies_conj_iff, ic_model_sat_l hZF, tg_context_data_sat_l I,
    Formula.satisfies_mem_iff, KP.succ0_sat_l hZF.1, it_pnice_sat_l hZF, rd_entry0_sat_l hZF.1, smem_sat_l I,
    it_map_sat_l hZF.1, tg_anchor_sat_l I hZF.1, rf_record_sat_l I _ _ tg_issued0_closed_l,
    rf_tuple_sat_l I, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_subset_iff,
    tg_past_sat_l hZF, tg_past_links_sat_l I hZF.1, tg_past_roots_sat_l I hZF.1,
    tg_past_events_sat_l I hZF.1, tg_common_tree_sat_l hZF.1, tg_past_play_sat_l I hZF.1, it_critical_bound_sat_l I hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_disj_iff, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,z,bound⟩ => ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,z,bound⟩,
    fun h => ⟨h.source,h.context,h.finite,h.successor,h.tree,h.node,h.model,h.root,h.image,h.anchor,
      h.record,h.values,h.omega,h.alphabet,h.lower,h.past,h.links,h.roots,h.events,h.below,h.bounds,h.span,h.tree_name,h.play,h.critical⟩⟩

def Tg_run_code_d (ω c₀ o C γ Z A n s : M.Domain) : Prop := ∃ q : Fin 64 → M.Domain,
  Rt_tuple_d q s ∧ Tg_run_d hZF ω c₀ o C γ Z A (fun i => q (i.castAdd 46)) (fun i => q (Fin.natAdd 18 i)) ∧ q 37 = n

def tg_run_code0_m : Formula 1 9 := rt_exists_m 64
  (.conj (rt_tuple_m (fun i : Fin 64 => .bound (i.castAdd 9)) (.bound 72))
    (.conj (tg_run_m (.bound 64) (.bound 65) (.bound 66) (.bound 67) (.bound 68) (.bound 69) (.bound 70)
      (fun i => .bound ((i.castAdd 46).castAdd 9)) (fun i => .bound ((Fin.natAdd 18 i).castAdd 9)))
      (Formula.extensionalEq (.bound 37) (.bound 71))))

theorem tg_run_code0_closed_l : tg_run_code0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, ?_, ?_⟩
  · apply tg_run_closed_l <;> first | rfl | exact fun _ => rfl
  · exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))

theorem tg_run_code0_sat_l (η : Env M 9) : Formula.satisfies η tg_run_code0_m ↔
    Tg_run_code_d hZF (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) (η.bound 4) (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) := by
  rw [tg_run_code0_m, rt_exists_sat_l]
  apply exists_congr
  intro q
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hZF.1, tg_run_sat_l hZF,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, Term.eval_bound]
  have new (i : Fin 64) : (rt_push_d η 64 q).bound (i.castAdd 9) = q i := rt_push_new_l η q i
  have old (i : Fin 9) : (rt_push_d η 64 q).bound (Fin.natAdd 64 i) = η.bound i := rt_push_old_l η q i
  simp only [new]
  rw [show (rt_push_d η 64 q).bound 72 = η.bound 8 from old 8,
    show (rt_push_d η 64 q).bound 64 = η.bound 0 from old 0,
    show (rt_push_d η 64 q).bound 65 = η.bound 1 from old 1,
    show (rt_push_d η 64 q).bound 66 = η.bound 2 from old 2,
    show (rt_push_d η 64 q).bound 67 = η.bound 3 from old 3,
    show (rt_push_d η 64 q).bound 68 = η.bound 4 from old 4,
    show (rt_push_d η 64 q).bound 69 = η.bound 5 from old 5,
    show (rt_push_d η 64 q).bound 70 = η.bound 6 from old 6,
    show (rt_push_d η 64 q).bound 71 = η.bound 7 from old 7,
    show (rt_push_d η 64 q).bound 37 = q 37 from new 37]

def tg_run_code_m {d} (ω c₀ o C γ Z A n s : Term d) : Formula 1 d :=
  tg_run_code0_m.bind (fun i => [ω,c₀,o,C,γ,Z,A,n,s].get i)

@[simp] theorem tg_run_code_closed_l {d} (ω c₀ o C γ Z A n s : Term d)
    (hw : ω.freeSupport = []) (hc : c₀.freeSupport = []) (ho : o.freeSupport = []) (hC : C.freeSupport = [])
    (hγ : γ.freeSupport = []) (hZ : Z.freeSupport = []) (hA : A.freeSupport = [])
    (hn : n.freeSupport = []) (hs : s.freeSupport = []) : (tg_run_code_m ω c₀ o C γ Z A n s).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hc (Fin.cases ho (Fin.cases hC (Fin.cases hγ (Fin.cases hZ
      (Fin.cases hA (Fin.cases hn (Fin.cases hs (fun i => Fin.elim0 i)))))))))) _).mpr tg_run_code0_closed_l

theorem tg_run_code_sat_l {d} (η : Env M d) (ω c₀ o C γ Z A n s : Term d) :
    Formula.satisfies η (tg_run_code_m ω c₀ o C γ Z A n s) ↔
      Tg_run_code_d hZF (ω.eval η) (c₀.eval η) (o.eval η) (C.eval η) (γ.eval η) (Z.eval η) (A.eval η) (n.eval η) (s.eval η) := by
  rw [tg_run_code_m, Formula.satisfies_bind, tg_run_code0_sat_l hZF]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际后继关系及全部控制参数的集合编码 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def tg_run_next_m {d} (ω c₀ : Term d) (v w : Fin 18 → Term d) (u t : Fin 46 → Term d) : Formula 1 d := set[d] ⟪
  ∃ k β T Q G E L j h,
    ⌜it_pnice_m⌝ₚ(⌜ω⌝ₛ, ⌜c₀⌝ₛ, β, T, Q, G, E, L) ∧
    ⌜it_extension_m⌝ₚ(⌜v 6⌝ₛ, ⌜v 7⌝ₛ, k, ⌜v 8⌝ₛ, ⌜v 9⌝ₛ, ⌜v 10⌝ₛ, ⌜v 11⌝ₛ, β, T, Q, G, E) ∧
    ⌜it_extension_m⌝ₚ(β, ⌜v 6⌝ₛ, ⌜v 7⌝ₛ, T, Q, G, E, ⌜w 6⌝ₛ, ⌜w 8⌝ₛ, ⌜w 9⌝ₛ, ⌜w 10⌝ₛ, ⌜w 11⌝ₛ) ∧
    ⌜w 7⌝ₛ = β ∧ ⌜KP.succ0_m⌝ₚ(⌜t 19⌝ₛ, ⌜u 19⌝ₛ) ∧ ⌜it_map_m⌝ₚ(⌜w 10⌝ₛ, ⌜v 7⌝ₛ, ⌜w 7⌝ₛ, j) ∧
    (⌜rd_entry0_m⌝ₚ(⌜u 0⌝ₛ, ⌜t 0⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 1⌝ₛ, ⌜t 1⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 2⌝ₛ, ⌜t 2⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 3⌝ₛ, ⌜t 3⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 4⌝ₛ, ⌜t 4⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 5⌝ₛ, ⌜t 5⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 6⌝ₛ, ⌜t 6⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 7⌝ₛ, ⌜t 7⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 8⌝ₛ, ⌜t 8⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 9⌝ₛ, ⌜t 9⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 10⌝ₛ, ⌜t 10⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 11⌝ₛ, ⌜t 11⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 12⌝ₛ, ⌜t 12⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 13⌝ₛ, ⌜t 13⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 14⌝ₛ, ⌜t 14⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 15⌝ₛ, ⌜t 15⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 16⌝ₛ, ⌜t 16⌝ₛ, j) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 17⌝ₛ, ⌜t 17⌝ₛ, j) ∧
     ⌜rd_entry0_m⌝ₚ(⌜u 18⌝ₛ, ⌜t 18⌝ₛ, j)) ∧ ⌜rd_entry0_m⌝ₚ(⌜u 20⌝ₛ, h, j) ∧ h ⊆ ⌜t 20⌝ₛ ∧
    ¬ (h = ⌜t 20⌝ₛ) ∧ ⌜v 13⌝ₛ ⊆ ⌜w 13⌝ₛ ∧
    (∃ Y R μ K η C L V q S n s g, ⌜tg_past_at_m⌝ₚ(⌜w 13⌝ₛ, ⌜u 19⌝ₛ, ⌜v 6⌝ₛ, Y, R, μ, K, η, C, L, V, q) ∧
      ⌜tg_saved_branch_m⌝ₚ(Y, R, ⌜ω⌝ₛ, V, q, S, n, s, ⌜u 23⌝ₛ, g) ∧
      ⌜tg_odd_m⌝ₚ(⌜ω⌝ₛ, ⌜v 13⌝ₛ, ⌜v 7⌝ₛ, ⌜v 6⌝ₛ, k, G, ⌜u 1⌝ₛ, ⌜u 23⌝ₛ, ⌜u 22⌝ₛ, ⌜u 7⌝ₛ, S, n, s, g))⟫

@[simp] theorem tg_run_next_closed_l {d} (ω c₀ : Term d) (v w : Fin 18 → Term d) (u t : Fin 46 → Term d)
    (hw : ω.freeSupport = []) (hc : c₀.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hw' : ∀ i, (w i).freeSupport = [])
    (hu : ∀ i, (u i).freeSupport = []) (ht : ∀ i, (t i).freeSupport = []) : (tg_run_next_m ω c₀ v w u t).FreeClosed := by
  simp -implicitDefEqProofs [tg_run_next_m, Definitional.Formula.FreeClosed, hw, hc, hv, hw', hu, ht]

theorem tg_run_next_sat_l {d} (η : Env M d) (ω c₀ : Term d) (v w : Fin 18 → Term d) (u t : Fin 46 → Term d) :
    Formula.satisfies η (tg_run_next_m ω c₀ v w u t) ↔ Tg_run_next_d hZF (ω.eval η) (c₀.eval η)
      (fun i => (v i).eval η) (fun i => (u i).eval η) (fun i => (w i).eval η) (fun i => (t i).eval η) := by
  simp only [tg_run_next_m, Tg_run_next_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    it_pnice_sat_l hZF, it_extension_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    KP.succ0_sat_l hZF.1, it_map_sat_l hZF.1, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff, tg_past_at_sat_l hZF.1,
    tg_saved_branch_sat_l hZF.1, tg_odd_sat_l hZF.1, Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  rfl

def Tg_run_edge_d (ω c₀ s t : M.Domain) : Prop := ∃ q : Fin 128 → M.Domain,
  Rt_tuple_d (fun i : Fin 64 => q (i.castAdd 64)) s ∧ Rt_tuple_d (fun i : Fin 64 => q (Fin.natAdd 64 i)) t ∧
  Tg_run_next_d hZF ω c₀ (fun i => q ((i.castAdd 46).castAdd 64)) (fun i => q ((Fin.natAdd 18 i).castAdd 64))
    (fun i => q (Fin.natAdd 64 (i.castAdd 46))) (fun i => q (Fin.natAdd 64 (Fin.natAdd 18 i)))

def tg_run_edge0_m : Formula 1 4 := rt_exists_m 128
  (.conj (rt_tuple_m (fun i : Fin 64 => .bound ((i.castAdd 64).castAdd 4)) (.bound 130))
    (.conj (rt_tuple_m (fun i : Fin 64 => .bound ((Fin.natAdd 64 i).castAdd 4)) (.bound 131))
      (tg_run_next_m (.bound 128) (.bound 129)
        (fun i => .bound (((i.castAdd 46).castAdd 64).castAdd 4))
        (fun i => .bound ((Fin.natAdd 64 (i.castAdd 46)).castAdd 4))
        (fun i => .bound (((Fin.natAdd 18 i).castAdd 64).castAdd 4))
        (fun i => .bound ((Fin.natAdd 64 (Fin.natAdd 18 i)).castAdd 4)))))

theorem Tg_run_edge_d.read_l {ω c s t : M.Domain} {v w : Fin 64 → M.Domain}
    (edge : Tg_run_edge_d hZF ω c s t) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    Tg_run_next_d hZF ω c (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 18 i))
      (fun i => w (i.castAdd 46)) (fun i => w (Fin.natAdd 18 i)) := by
  obtain ⟨q, ps', pt', step⟩ := edge
  have ev := rt_tuple_inj_l ps' ps
  have ew := rt_tuple_inj_l pt' pt
  exact ev ▸ ew ▸ step

theorem tg_run_edge0_closed_l : tg_run_edge0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, rt_tuple_closed_l _ _ (fun _ => rfl) rfl, ?_⟩
  apply tg_run_next_closed_l <;> first | rfl | exact fun _ => rfl

theorem tg_run_edge0_sat_l (η : Env M 4) : Formula.satisfies η tg_run_edge0_m ↔
    Tg_run_edge_d hZF (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 3) := by
  rw [tg_run_edge0_m, rt_exists_sat_l]
  apply exists_congr
  intro q
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hZF.1, tg_run_next_sat_l hZF, Term.eval_bound]
  have new (i : Fin 128) : (rt_push_d η 128 q).bound (i.castAdd 4) = q i := rt_push_new_l η q i
  have old (i : Fin 4) : (rt_push_d η 128 q).bound (Fin.natAdd 128 i) = η.bound i := rt_push_old_l η q i
  simp only [new]
  rw [show (rt_push_d η 128 q).bound 128 = η.bound 0 from old 0,
    show (rt_push_d η 128 q).bound 129 = η.bound 1 from old 1,
    show (rt_push_d η 128 q).bound 130 = η.bound 2 from old 2,
    show (rt_push_d η 128 q).bound 131 = η.bound 3 from old 3]

def tg_run_edge_m {d} (ω c₀ s t : Term d) : Formula 1 d := tg_run_edge0_m.bind (fun i => [ω,c₀,s,t].get i)

@[simp] theorem tg_run_edge_closed_l {d} (ω c₀ s t : Term d)
    (hw : ω.freeSupport = []) (hc : c₀.freeSupport = []) (hs : s.freeSupport = []) (ht : t.freeSupport = []) :
    (tg_run_edge_m ω c₀ s t).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hw (Fin.cases hc (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i))))) _).mpr tg_run_edge0_closed_l

theorem tg_run_edge_sat_l {d} (η : Env M d) (ω c₀ s t : Term d) :
    Formula.satisfies η (tg_run_edge_m ω c₀ s t) ↔ Tg_run_edge_d hZF (ω.eval η) (c₀.eval η) (s.eval η) (t.eval η) := by
  rw [tg_run_edge_m, Formula.satisfies_bind, tg_run_edge0_sat_l hZF]
  rfl

theorem Tg_run_d.pack_l {ω c₀ o C γ Z A : M.Domain} {v : Fin 18 → M.Domain} {u : Fin 46 → M.Domain}
    (h : Tg_run_d hZF ω c₀ o C γ Z A v u) : ∃ s, Tg_run_code_d hZF ω c₀ o C γ Z A (u 19) s := by
  let q : Fin 64 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v u
  obtain ⟨s, code⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) q
  refine ⟨s, q, code, ?_, rfl⟩
  simpa only [q, Fin.addCases_left, Fin.addCases_right] using h

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限树的全部旧列与旧前驱保持

两次实际扩张给出六列的包含；树序还保留每个旧终点的全部前驱。
该关系在对象语言中可定义，故可沿内部 ω 传播到任意两个阶段。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_pnice_d.extension_keep_l {ω c α T Q G E L β T' Q' G' E' L' ξ k : M.Domain}
    (h : It_pnice_d hZF ω c α T Q G E L) (g : It_pnice_d hZF ω c β T' Q' G' E' L')
    (e : It_extension_d α ξ k T Q G E β T' Q' G' E') :
    (∀ i j, M.mem j α → (Rd_entry_d i j T' ↔ Rd_entry_d i j T)) ∧
    M.MemberSubset T T' ∧ M.MemberSubset Q Q' ∧ M.MemberSubset G G' ∧ M.MemberSubset E E' ∧ M.MemberSubset L L' := by
  obtain ⟨order,t,q,gmap,e'⟩ := h.tree.extension_keep_l hZF e
  exact ⟨order,t,q,gmap,e',it_levels_subset_l hZF.1 h.function.1
    (fun i l => (h.levels i l).mp) (fun i l => (g.levels i l).mpr) e'⟩
theorem Tg_run_next_d.keep_l {ω c o C γ Z A : M.Domain} {v w : Fin 64 → M.Domain}
    (h : Tg_run_d hZF ω c o C γ Z A (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 18 i)))
    (g : Tg_run_d hZF ω c o C γ Z A (fun i => w (i.castAdd 46)) (fun i => w (Fin.natAdd 18 i)))
    (step : Tg_run_next_d hZF ω c (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 18 i))
      (fun i => w (i.castAdd 46)) (fun i => w (Fin.natAdd 18 i))) : Tg_tree_keep_d (fun i => v (i.castAdd 50)) (fun i => w (i.castAdd 50)) := by
  obtain ⟨k, β, T, Q, G, E, L, _, _, mid, e, e', _, _, even, _, _, _, _, past, _⟩ := step
  obtain ⟨order, cols⟩ := h.tree.extension_keep_l hZF mid e
  obtain ⟨order', cols'⟩ := mid.extension_keep_l hZF g.tree e'
  have sub {a b : M.Domain} (s : M.SuccessorOf b a) : M.MemberSubset a b := fun x hx => (s x).mpr (Or.inl hx)
  have keep (a : Fin 5) : M.MemberSubset (v ⟨8+a.val, by omega⟩) (w ⟨8+a.val, by omega⟩) := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))) a <;>
      intro x hx
    · exact cols'.1 x (cols.1 x hx)
    · exact cols'.2.1 x (cols.2.1 x hx)
    · exact cols'.2.2.1 x (cols.2.2.1 x hx)
    · exact cols'.2.2.2.1 x (cols.2.2.2.1 x hx)
    · exact cols'.2.2.2.2 x (cols.2.2.2.2 x hx)
  refine ⟨fun x hx => sub e'.1 x (sub e.1 x hx),
    fun i j hj => (order' i j (sub e.1 j hj)).trans (order i j hj),
    fun a => Fin.lastCases past (fun i => keep i) a, ?_⟩
  intro i hi
  have old := (e'.2.1 i (v 7)).mpr (Or.inl ((e.2.1 i (v 7)).mpr (Or.inl hi)))
  exact g.tree.tree.diagram.order.trans i (v 7) (w 7) old (g.tree.tree.diagram.map_bound_l hZF even)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 统一有限树列的内部并

先从记录值域的传递闭包分离各列。任意有限组条目回到共同阶段核验；
旧终点的全部前驱保持使并树在每个旧阶段上的限制精确等于原树。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_sequence_d (ω c o C γ Z A D f : M.Domain) : Prop where
  function : Fn0_d ω D f
  rows : ∀ i s, Rd_entry_d i s f → ∃ n, M.SuccessorOf n i ∧ Tg_run_code_d hZF ω c o C γ Z A n s
  steps : ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s f → Rd_entry_d j t f → Tg_run_edge_d hZF ω c s t

theorem Tg_sequence_d.read_l {ω c o C γ Z A D f : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) {i s} {v : Fin 64 → M.Domain}
    (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) :
    Tg_run_d hZF ω c o C γ Z A (fun j => v (j.castAdd 46)) (fun j => v (Fin.natAdd 18 j)) ∧ M.mem i (v 6) := by
  obtain ⟨n, ns, q, pack, run, num⟩ := h.rows i s hs
  have eq := rt_tuple_inj_l pack code
  subst q
  exact ⟨run, run.tree.tree.diagram.order.ordinal.transitive n (num ▸ run.span) i ns.predecessor_mem⟩

/-- 并列中的每个真实扩展器来自某一有限轮，故保留同一个临界点下界。 -/
theorem Tg_sequence_d.critical_bound_l {ω c o C γ Z A D f Q E : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (models : ∀ x, M.mem x Q ↔ Tg_run_value_d (n := 63) 9 f x)
    (column : ∀ x, M.mem x E ↔ Tg_run_value_d (n := 63) 11 f x) : It_critical_bound_d I γ Q E := by
  rintro i p κ L F ⟨q, pair, hq⟩ payload
  obtain ⟨v, n, s, hs, code, hq⟩ := (column q).mp hq
  obtain ⟨a, X, R, ⟨r, hp, hr⟩, model, lower⟩ :=
    (h.read_l hZF hs code).1.critical i p κ L F ⟨q, pair, hq⟩ payload
  exact ⟨a, X, R, ⟨r, hp, (models r).mpr ⟨v, n, s, hs, code, hr⟩⟩, model, lower⟩

theorem Tg_sequence_d.merge_l {ω c o C γ Z A D f : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hω : M.IsOmega ω) {i j s t} {v w : Fin 64 → M.Domain}
    (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    ∃ k r, ∃ z : Fin 64 → M.Domain, Rd_entry_d k r f ∧ Rt_tuple_d z r ∧ Tg_tree_keep_d (fun i => v (i.castAdd 50)) (fun i => z (i.castAdd 50)) ∧ Tg_tree_keep_d (fun i => w (i.castAdd 50)) (fun i => z (i.castAdd 50)) := by
  have read {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) := h.read_l hZF hs code
  have next {i j s t} (ij : M.SuccessorOf j i) (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) : Tg_run_keep_d (fun i : Fin 14 => i.castAdd 50) s t := by
    obtain ⟨q, ps, pt, step⟩ := h.steps i j s t ij hs ht
    exact ⟨_, _, ps, pt, step.keep_l (v := fun i => q (i.castAdd 64)) (w := fun i => q (Fin.natAdd 64 i)) hZF (read hs ps).1 (read ht pt).1⟩
  exact Tg_run_keep_d.merge_l hZF hω h.function (fun _ _ _ _ => next) hs ht ps pt

/-- 旧运行直接提供公共有限框架，不另行构造或重选原树。 -/
theorem Tg_sequence_d.frames_l {ω c o C γ Z A D f : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω) :
    It_frames_d hZF (fun i : Fin 14 => i.castAdd 50) ω c D f := by
  refine ⟨h.function,?_,fun _ _ _ _ _ _ hs ht ps pt => h.merge_l hZF hw hs ht ps pt⟩
  intro i s hs
  obtain ⟨_,_,v,code,_⟩ := h.rows i s hs
  have read := h.read_l hZF hs code
  obtain ⟨m,succ,hm⟩ := hw.1.2 (v 7) read.1.finite
  have finite : M.mem (v 6) ω := succ.eq hZF.1 read.1.successor ▸ hm
  exact ⟨v,code,read.1.tree.tree,finite,read.2,read.1.tree.function,read.1.tree.levels,read.1.past.sequence.2.1⟩

/-- 并树在旧终点之前的限制由同一公共框架恢复。 -/
theorem Tg_sequence_d.order_l {ω c o C γ Z A D f i s x y : M.Domain} {U : Fin 6 → M.Domain}
    {v : Fin 64 → M.Domain} (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω)
    (columns : ∀ a z, M.mem z (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val,by omega⟩ f z)
    (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (hy : M.mem y (v 6)) :
    Rd_entry_d x y (U 0) ↔ Rd_entry_d x y (v 8) :=
  (h.frames_l hZF hw).order_l hZF columns hs code hy

theorem Tg_sequence_d.union_l {ω c o C γ Z A D f : M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω) : ∃ U : Fin 6 → M.Domain,
    It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4) ∧ M.IsSetFunction I (U 5) ∧
      ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val,by omega⟩ f x := by
  obtain ⟨U,tree,lf,levels,archive,columns⟩ := (h.frames_l hZF hw).union_l hZF hw
  have keep {i s} {v : Fin 64 → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      (a : Fin 6) {x y} (xy : Rd_entry_d x y (v ⟨8+a.val,by omega⟩)) : Rd_entry_d x y (U a) := by
    obtain ⟨p,pair,hp⟩ := xy
    exact ⟨p,pair,(columns a p).mpr ⟨v,i,s,hs,code,hp⟩⟩
  refine ⟨U,⟨tree,lf,levels,?_,?_⟩,archive,columns⟩
  · intro i p κ L F hp payload
    obtain ⟨q,pair,hq⟩ := hp
    obtain ⟨v,j,s,hs,code,hq⟩ := (columns 3 q).mp hq
    obtain ⟨a,X,R,ha,ma,trans,strong,inaccessible⟩ := (h.read_l hZF hs code).1.tree.exactness
      i p κ L F ⟨q,pair,hq⟩ payload
    exact ⟨a,X,R,keep hs code 1 ha,ma,trans,strong,inaccessible⟩
  · intro i j L V hi hj ij
    obtain ⟨p,pair,hp⟩ := hi
    obtain ⟨q,qp,hq⟩ := hj
    obtain ⟨v,k,s,hs,ps,hp⟩ := (columns 4 p).mp hp
    obtain ⟨w,l,t,ht,pt,hq⟩ := (columns 4 q).mp hq
    obtain ⟨m,r,u,hr,pr,su,tu⟩ := h.merge_l hZF hw hs ht ps pt
    exact (h.read_l hZF hr pr).1.tree.increasing i j L V
      ⟨p,pair,su.2.2.1 4 p hp⟩ ⟨q,qp,tu.2.2.1 4 q hq⟩ ij

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原树名称沿统一递归和有限树取并保持 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_run_name_d (S s : M.Domain) : Prop := ∃ v : Fin 64 → M.Domain,
  Rt_tuple_d v s ∧ Rd_entry_d S (v 25) (v 16)

def tg_run_name0_m : Formula 1 2 := rt_exists_m 64
  (.conj (rt_tuple_m (fun i => .bound (i.castAdd 2)) (.bound 65))
    (rd_entry0_m (.bound 64) (.bound 25) (.bound 16)))

theorem tg_run_name0_closed_l : tg_run_name0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  refine ⟨rt_tuple_closed_l _ _ (fun _ => rfl) rfl, ?_⟩
  simp -implicitDefEqProofs [rd_entry0_m]

theorem tg_run_name0_sat_l (hE : Extensional M) (η : Env M 2) :
    Formula.satisfies η tg_run_name0_m ↔ Tg_run_name_d (η.bound 0) (η.bound 1) := by
  rw [tg_run_name0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, rd_entry0_sat_l hE, Term.eval_bound]
  have new (i : Fin 64) : (rt_push_d η 64 v).bound (i.castAdd 2) = v i := rt_push_new_l η v i
  simp only [new]
  rw [show (rt_push_d η 64 v).bound 65 = η.bound 1 from rt_push_old_l η v 1,
    show (rt_push_d η 64 v).bound 64 = η.bound 0 from rt_push_old_l η v 0]
  rfl

def tg_run_name_m {d} (S s : Term d) : Formula 1 d := tg_run_name0_m.bind (Fin.cases S (fun _ => s))
@[simp] theorem tg_run_name_closed_l {d} (S s : Term d) (hS : S.freeSupport = []) (hs : s.freeSupport = []) :
    (tg_run_name_m S s).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases hS (fun _ => hs)) _).mpr tg_run_name0_closed_l

theorem tg_run_name_sat_l (hE : Extensional M) {d} (η : Env M d) (S s : Term d) :
    Formula.satisfies η (tg_run_name_m S s) ↔ Tg_run_name_d (S.eval η) (s.eval η) := by
  rw [tg_run_name_m, Formula.satisfies_bind, tg_run_name0_sat_l hE]; rfl

variable (hZF : M.Models ZF)

theorem Tg_run_edge_d.name_l {ω c o C γ Z A n m s t S : M.Domain}
    (h : Tg_run_code_d hZF ω c o C γ Z A n s) (g : Tg_run_code_d hZF ω c o C γ Z A m t)
    (step : Tg_run_edge_d hZF ω c s t) (name : Tg_run_name_d S s) : Tg_run_name_d S t := by
  obtain ⟨v, vs, h, _⟩ := h
  obtain ⟨w, wt, g, _⟩ := g
  obtain ⟨v', vs', image⟩ := name
  have eq := rt_tuple_inj_l vs' vs
  subst v'
  have edge := step.read_l hZF vs wt
  have keep := edge.keep_l hZF h g
  have root : It_map_d (w 10) o (v 7) (v 16) := by
    obtain ⟨r, pair, p, pp, hp⟩ := h.root
    exact ⟨r, pair, p, pp, keep.2.2.1 2 p hp⟩
  obtain ⟨_, _, _, _, _, _, _, j, _, _, _, _, _, _, even, images, _⟩ := edge
  exact ⟨w, wt, g.tree.tree.diagram.comp o (v 7) (w 7) (v 16) j (w 16)
    root even g.root S (v 25) (w 25) image (images 7)⟩

theorem Tg_sequence_d.root_tree_l {ω c o C γ Z A D f S : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (names : ∀ i s, Rd_entry_d i s f → Tg_run_name_d S s) : Tg_root_tree_d ω (U 5) (U 2) o S := by
  intro m i Y R μ K η E L V q S' n digits t g row br
  obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := row
  obtain ⟨v, k, s, hs, code, hp⟩ := (columns 5 p).mp hp
  have run := (h.read_l hZF hs code).1
  obtain ⟨w, pack, image⟩ := names k s hs
  have eq := rt_tuple_inj_l pack code
  subst w
  obtain ⟨S₀, image₀, trees⟩ := run.tree_name
  have diagram := run.tree.tree.diagram
  obtain ⟨a, B, T, ha, ma⟩ := diagram.model_l hZF (diagram.order.bound o (v 7) (diagram.map_bound_l hZF run.root)).1
  have map := diagram.elementary o (v 7) (v 16) a B T (v 15) (v 0) (v 1) run.root ha run.node ma run.model.1
  have eq := map.1.2 S₀ S (v 25) image₀ image
  subst S₀
  obtain ⟨j, ⟨a, ap, b, bp, hb⟩, value⟩ := trees m i Y R μ K η E L V q S' n digits t g ⟨r, ⟨p, pair, hp⟩, cell⟩ br
  exact ⟨j, ⟨a, ap, b, bp, (columns 2 b).mpr ⟨v, k, s, hs, code, hb⟩⟩, value⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 旧运行直接产生同一当前节点共尾枝 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem Tg_sequence_d.even_branch_l {ω c o C γ Z A D f : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_tree_d hZF ω c ω (U 0) (U 1) (U 2) (U 3))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val,by omega⟩ f x) :
    ∃ B, It_branch_d ω (U 0) B ∧ ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 64) f (U 0) x :=
  (h.frames_l hZF tree.omega).even_branch_l hZF tree columns
    (fun _ _ _ hs code => (h.read_l hZF hs code).1.successor)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任何非偶数共尾枝都有共尾的实际奇数回答

一个结点首次进入有限树时只能是新奇数回答或新偶数结点。内部最小阶段
排除旧树结点；分支与偶数枝分开后，剩下的首次出现结点都来自原保存历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_odd_edge_d (ω H T G B y : M.Domain) : Prop := Tg_odd_node_d H y ∧
  ∃ m ξ k e t ℓ Sₑ Y R μ K η C L V q S n a g,
    Tg_past_at_d H m y Y R μ K η C L V q ∧ Tg_saved_branch_d Y R ω V q S n a t g ∧
    Tg_odd_d ω H ξ y k G e t ℓ Sₑ S n a g ∧ It_pred_d T k y ∧ M.mem ξ B

def Tg_odd_tail_d (ω H T G B b : M.Domain) : Prop := ∃ z,
  M.mem z b ∧ ¬ M.mem z B ∧ Tg_odd_node_d H z ∧ ∀ y, M.mem y b → M.mem z y →
    Tg_odd_edge_d ω H T G B y ∧ ∀ k, It_pred_d T k y →
      M.mem k b ∧ ¬ M.mem k B ∧ (z = k ∨ M.mem z k)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_sequence_d.late_odd_l {ω c o C γ Z A D f B e s₀ y : M.Domain} {U : Fin 6 → M.Domain}
    {v₀ : Fin 64 → M.Domain} (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (even : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 64) f (U 0) x) (empty : ∀ x, ¬ M.mem x e)
    (first : Rd_entry_d e s₀ f) (code₀ : Rt_tuple_d v₀ s₀) (hy : M.mem y ω)
    (outside : ¬ M.mem y (v₀ 6)) (not_even : ¬ M.mem y B) : Tg_odd_edge_d ω (U 5) (U 0) (U 2) B y := by
  classical
  have hw := tree.tree.omega
  obtain ⟨l,k,t,s,w,v,succ,ht,ct,hs,code,old,hyv⟩ :=
    (h.frames_l hZF hw).first_l hZF v₀ empty first code₀ hy outside
  obtain ⟨a, β, T, Q, G, E, L₀, _, _, mid, ext₁, ext₂, head, _, _, _, _, _, _, _,
    Y, R, μ, K, η, C, L, V, q, S, n, digits, g, saved, br, odd⟩ := (h.steps l k t s succ ht hs).read_l hZF ct code
  rcases (ext₂.1 y).mp hyv with hyβ | eq
  · rcases (ext₁.1 y).mp hyβ with hyold | eq
    · exact (old hyold).elim
    · have eq := hZF.1.eq_of_same_members y (w 6) eq
      subst y
      have oldRun := (h.read_l hZF ht ct).1
      have newRun := (h.read_l hZF hs code).1
      have inside a := fun z hz => (columns a z).mpr ⟨v, k, s, hs, code, hz⟩
      have oldInside a := fun z hz => (columns a z).mpr ⟨w, l, t, ht, ct, hz⟩
      have ha : M.mem a (w 6) := by
        rcases odd with ⟨_, eq, _⟩ | ⟨_, Y, R, μ, K, η, C, L, V, q, _, _, _, _, _, _, _, _, _, row, _⟩
        · exact eq ▸ oldRun.successor.predecessor_mem
        · obtain ⟨d, hd, _⟩ := oldRun.links _ _ _ _ _ _ _ _ _ _ _ row
          exact (oldRun.tree.tree.diagram.model_domain a).mpr ⟨d, hd⟩
      have keep₁ := oldRun.tree.extension_keep_l hZF mid ext₁
      have keep₂ := mid.extension_keep_l hZF newRun.tree ext₂
      have hyβ := ext₁.1.predecessor_mem
      have hyv := (ext₂.1 _).mpr (Or.inl hyβ)
      have hav := (ext₂.1 _).mpr (Or.inl ((ext₁.1 _).mpr (Or.inl ha)))
      have tip i : Rd_entry_d i (w 6) T ↔ i = w 6 ∨ Rd_entry_d i a (w 8) :=
        (ext₁.2.1 i (w 6)).trans ⟨fun h => h.elim
          (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZF) _ (oldRun.tree.tree.diagram.order.bound _ _ h).2).elim)
          And.right, fun h => Or.inr ⟨rfl, h⟩⟩
      have pred : It_pred_d (U 0) a (w 6) := ⟨ha, fun i =>
        (h.order_l hZF hw columns hs code hyv).trans ((keep₂.1 i _ hyβ).trans
          ((tip i).trans (or_congr Iff.rfl ((keep₁.1 i a ha).symm.trans
            ((keep₂.1 i a ((ext₁.1 a).mpr (Or.inl ha))).symm.trans (h.order_l hZF hw columns hs code hav).symm)))))⟩
      have liftMap {i j} (hj : It_map_d G i (w 6) j) : It_map_d (U 2) i (w 6) j := by
        obtain ⟨r, pair, p, pp, hp⟩ := (ext₂.2.2.2.1 i (w 6) j hyβ).mpr hj
        exact ⟨r, pair, p, pp, inside 2 p hp⟩
      have moved : Tg_odd_d ω (U 5) (w 7) (w 6) a (U 2) (w 19) (w 41) (w 40) (w 25) S n digits g := by
        rcases odd with reset | ⟨ne, Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, j, x, b, z, row, br, hj, rest⟩
        · obtain ⟨he, hk, hg, j, edge, image⟩ := reset
          exact Or.inl ⟨he, hk, hg, j, liftMap edge, image⟩
        · obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := row
          have hj := (ext₂.2.2.2.1 a (w 6) j hyβ).mpr hj
          obtain ⟨r', pair', p', pp, hp'⟩ := hj
          exact Or.inr ⟨ne, Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, j, x, b, z,
            ⟨r, ⟨p, pair, oldInside 5 p hp⟩, cell⟩, br, ⟨r', pair', p', pp, inside 2 p' hp'⟩, rest⟩
      obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := saved
      have row : Tg_past_at_d (U 5) (w 37) (w 6) Y R μ K η C L V q :=
        ⟨r, ⟨p, pair, inside 5 p hp⟩, cell⟩
      exact ⟨⟨w 37, r, cell.choose, ⟨p, pair, inside 5 p hp⟩, cell.choose_spec.1⟩,
        w 37, w 7, a, w 19, w 41, w 40, w 25, Y, R, μ, K, η, C, L, V, q, S, n, digits, g,
        row, br, moved, pred, (even (w 7)).mpr ⟨w, l, t, ht, ct,
          tree.tree.diagram.order.refl (w 7) oldRun.finite⟩⟩
  · have eq := hZF.1.eq_of_same_members y β eq
    have yr : y = v 7 := eq.trans head.symm
    exact (not_even ((even y).mpr ⟨v, k, s, hs, code,
      yr.symm ▸ tree.tree.diagram.order.refl (v 7) (h.read_l hZF hs code).1.finite⟩)).elim

theorem Tg_sequence_d.odd_tail_l {ω c o C γ Z A D f B b : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (even_branch : It_branch_d ω (U 0) B) (even : ∀ x, M.mem x B ↔ Tg_even_d (7 : Fin 64) f (U 0) x)
    (branch : It_branch_d ω (U 0) b) (ne : b ≠ B) :
    Tg_odd_cofinal_d ω b (U 5) ∧ Tg_odd_tail_d ω (U 5) (U 0) (U 2) B b := by
  classical
  have hw := tree.tree.omega
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  obtain ⟨e, empty, he⟩ := hw.1.1
  obtain ⟨s₀, _, first⟩ := h.function.2.1 e he
  obtain ⟨_, _, v₀, code₀, _⟩ := h.rows e s₀ first
  have run := (h.read_l hZF first code₀).1
  have ha := (hw.1.2 _ run.finite).elim fun a h => (h.1.eq hZF.1 run.successor) ▸ h.2
  have late := branch.separate_l hZF.1 tree.tree.diagram.order even_branch ne ha
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨y, hy, iy, not_even, outside⟩ := late i hi
    exact ⟨y, hy, iy, (h.late_odd_l hZF tree columns even empty first code₀ (branch.subset y hy) outside not_even).1⟩
  · obtain ⟨z, hz, _, not_even, outside⟩ := late e he
    refine ⟨z, hz, not_even,
      (h.late_odd_l hZF tree columns even empty first code₀ (branch.subset z hz) outside not_even).1,
      fun y hy zy => ?_⟩
    have order := branch.forward_l tree.tree.diagram.order hz hy (Or.inr zy)
    have yn : ¬ M.mem y B := fun h => not_even (even_branch.down z y order h)
    have yo : ¬ M.mem y (v₀ 6) := fun h => outside ((hw.members_areOrdinals (ZF.modelsKP hZF) _ ha).transitive y h z zy)
    refine ⟨h.late_odd_l hZF tree columns even empty first code₀ (branch.subset y hy) yo yn, ?_⟩
    intro k pred
    have zk : Rd_entry_d z k (U 0) := ((pred.2 z).mp order).elim
      (fun eq => (ir y (eq ▸ zy)).elim) id
    have ky := (pred.2 k).mpr (Or.inr (tree.tree.diagram.order.refl k
      (hw.transitive (ZF.modelsKP hZF) y (branch.subset y hy) k pred.1)))
    exact ⟨branch.down k y ky hy, fun h => not_even (even_branch.down z k zk h),
      tree.tree.diagram.order.forward z k zk⟩

end YesMetaZFC.SetTheory.LargeCardinal

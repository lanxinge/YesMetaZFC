import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunState
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnswerHistory

/-! # 两条树边之后闭合整份递归历史

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
    ∃ w t, Tg_run_d hZF ω c₀ o Cᵣ γ Z A w t ∧ Tg_run_next_d hZF ω c₀ v u w t := by
  let nc : Nonempty {z // M.mem z (v 5)} := ⟨⟨ω, h.context.omega⟩⟩
  obtain ⟨ι, eu, issued⟩ := h.read_l hZF nc
  have eq : (fun i => (ι.bound i).val) = u := funext eu
  rw [← eq]
  have h : Tg_run_d hZF ω c₀ o Cᵣ γ Z A v (fun i => (ι.bound i).val) := eq.symm ▸ h
  have fs := (h.context.read_l hZF h.source.source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  have state := (tg_issued_sat_l J ext ι).mp issued
  have hn : M.mem (ι.bound 19).val ω := h.omega ▸ state.round
  obtain ⟨k, β, T₁, Q₁, G₁, E₁, H₁, a, Y, R, μ, K, η₁, C₁, π₁,
    nice₁, ext₁, node₁, my, sy, cy, root₁, image₁, anchor₁, n₁, ρ, round, request, high, odd,
    β₂, T₂, Q₂, G₂, E₂, H₂, d, j, N, R₂, K₂, L, F, κ, U, D, u₀, η₂, C₂, W, π₂,
    nice₂, ext₂, node₂, edge, mn, sn, ultra, crit, limit, bound, subset, heights,
    iU, iD, iu, reply, iη, iC, cn, hW, common, level, root₂, image₂, anchor₂, update⟩ :=
    h.context.tree_successor_l hZFC h.source nc ι issued h.omega h.tree h.successor h.node h.model ho
      h.root h.image h.anchor hγ hωZ (h.alphabet.symm ▸ hAZ) h.lower h.past h.links h.roots h.events h.below h.bounds
  have hj := ultra.elementary_l hZF h.model.1 mn.1
  have fn := hj.1.1.1.2
  have natural := hj.natural_l hZF h.source.source.omega h.source.source.transitive sn.source.transitive
    h.model mn h.source.source.omega_mem
  have fixed {z z'} (hz : M.mem z ω) (hz' : Rd_entry_d z z' j) : z' = z := fn z z' z hz' (natural z hz)
  let n₂ : Nonempty {z // M.mem z C₂} := ⟨⟨ω, cn.omega⟩⟩
  have ft := (cn.read_l hZF sn.source).1
  let P := rt_pair_l ft.transitive n₂ hZF.1 ft.pair
  obtain ⟨θ, images, moved⟩ := hj.relative_image_l hZF h.source.source.omega h.source.source.transitive
    sn.source.transitive h.model mn fs.transitive ft.transitive nc n₂ iC tg_issued0_m tg_issued0_closed_l ι
  have valid := moved.mp issued
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
  have hl := sy.source.omega.transitive hZF _ hm _ language.2.2.1
  have first := (rt_successor_l (cy.read_l hZF sy.source).1.transitive n₁ hZF.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp seed.2.2.2.2.2.2.2.1)
  have hk := sy.source.omega.transitive hZF _ hl _ first.predecessor_mem
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
  have δlimit := δ.limit_l (ZF.modelsKP hZF) sn.source.transitive sn.source.theory.algebra.pair
  have below := δlimit.1.transitive κ (eκ ▸ state'.bound) (ρ.bound 15).val (subset _ bound)
  obtain ⟨B, S, Kᵣ, mb, sb⟩ := h.tree.tree.sources o c₀ (h.tree.tree.root o ho)
  have jy := nice₁.tree.diagram.elementary o (v 6) π₁ c₀ B S a Y R root₁ (nice₁.tree.root o ho) node₁ mb.1 my.1
  have jn := nice₂.tree.diagram.elementary o β π₂ c₀ B S d N R₂ root₂ (nice₂.tree.root o ho) node₂ mb.1 mn.1
  have answer := cy.answer_history_l hZF n₁ ρ cn sy.source sn.source sn.hierarchy sb.transitive mb my mn
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
  have roots := Tg_past_roots_d.push_l hZF past ns newest entries (h.roots.extend_l keepRoot)
    ((ext₂.2.2.2.1 o (v 6) π₁ ext₁.1.predecessor_mem).mpr root₁) image₁ anchor₁ ⟨_, code, high⟩
  have rules := (Formula.satisfies_conj_iff ..).mp state.control |>.2.2.1
  simp only [tg_rules_m] at rules
  have ze : ∀ z, ¬ M.mem z (ι.bound 1).val := fun z hz =>
    (Formula.satisfies_isEmpty_iff ..).mp rules.2.1 ⟨z, fs.transitive _ (ι.bound 1).property z hz⟩ hz
  have zeroω := num_mem_l hZF.1 h.source.source.omega (show Num_d 0 (ι.bound 1).val from ze)
  have succω {a b : M.Domain} (ha : M.mem a ω) (hs : M.SuccessorOf b a) : M.mem b ω := by
    obtain ⟨b', hs', hb'⟩ := h.source.source.omega.1.2 a ha
    exact hs'.eq hZF.1 hs ▸ hb'
  have one := (rt_successor_l fs.transitive nc hZF.1 (ι.bound 2) (ι.bound 1)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp rules.2.2.1)
  have two := (rt_successor_l fs.transitive nc hZF.1 (ι.bound 3) (ι.bound 2)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp rules.2.2.2.1)
  have three := (rt_successor_l fs.transitive nc hZF.1 (ι.bound 4) (ι.bound 3)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp rules.2.2.2.2.1)
  have ha := succω zeroω one
  have hc := succω (succω ha two) three
  have ec := fixed hc (images 4)
  have ee := fixed zeroω (images 1)
  have ea := fixed ha (images 2)
  have en := fixed hn (images 19)
  have events := h.events.map_l hZF h.past hn h.source.source.omega h.source.source.transitive sn.source.transitive
    h.model mn hj h.source.source.omega_mem hc zeroω ha iC (images 20) fixedPast
  have events : Tg_past_events_d ω (v 13) C₂ (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val (θ.bound 20).val :=
    ec.symm ▸ ee.symm ▸ ea.symm ▸ events
  have labels : Fn0_d (ι.bound 26).val ω (ι.bound 23).val := h.omega ▸
    (fn0_sat_l hZF.1 _ (.bound 0) (.bound 1) (.bound 2)).mp
      ((rt_model_delta_l fs.transitive nc (fn0_delta_l (.bound 0) (.bound 1) (.bound 2))
        (⟨fun i => [ι.bound 26, ι.bound 0, ι.bound 23].get i, fun _ => ι.bound 0⟩ : Env (rt_model_l (v 5) nc) 3)).mp
          ((fn0_sat_l ext _ (.bound 0) (.bound 1) (.bound 2)).mpr state.labels))
  have et := fn _ _ _ (images 23) (hj.finite_fixed_l hZF h.source.source.omega h.source.source.transitive
    sn.source.transitive h.model mn h.source.source.omega_mem (Eq.mp (congrArg (fun z => M.mem z ω) (request 2)) hk)
      (h.source.source.transitive _ h.context.member _ (ι.bound 23).property) labels)
  have et : (θ.bound 23).val = (ρ.bound 41).val := et.trans (request 18).symm
  have oldRoot := keepRoot (v 7) (v 16) h.root
  have eA := (nice₂.tree.diagram.elementary o β π₂ c₀ B S d N R₂ root₂ (nice₂.tree.root o ho) node₂ mb.1 mn.1).1.1.1.2
    A (θ.bound 6).val A (nice₂.tree.diagram.comp o (v 7) β (v 16) j π₂ oldRoot edge root₂
      A A (θ.bound 6).val (h.anchor.fixed A hAZ) (h.alphabet ▸ images 6)) (anchor₂.fixed A hAZ)
  obtain ⟨_, t₀, _, _, _, _, _, advance⟩ := answer
  have xC : M.mem x C₂ := ft.transitive _ (θ.bound 6).property x (eA.symm ▸ hx)
  have hxθ : M.mem x (θ.bound 6).val := eA.symm ▸ hx
  obtain ⟨_, t, _, m, _, _, _, _, next, _, ε, head, num, legal, _, _, growth, keep, proper, trace⟩ :=
    advance ⟨x, xC⟩ hxθ
  have control (i : Fin 19) : ε.bound (i.castAdd 27) = θ.bound (i.castAdd 27) :=
    (head i).trans (by simp only [tg_position_env_d, Fin.addCases_left])
  have sm := (rt_successor_l ft.transitive n₂ hZF.1 (ε.bound 19) (θ.bound 19)).mp (num.symm ▸ next)
  have sm : M.SuccessorOf (ε.bound 19).val (ι.bound 19).val := en ▸ sm
  have em : (ε.bound 19).val = n := sm.eq hZF.1 ns
  have events := events.mono_l hZF ft.transitive n₂ P (θ.bound 4) (θ.bound 1) (θ.bound 2) (θ.bound 20) (ε.bound 20) keep
  have trace : Tg_trace_d ω C₂ (θ.bound 4).val (θ.bound 1).val (θ.bound 2).val
      (ι.bound 19).val (ε.bound 20).val (ρ.bound 41).val (ρ.bound 15).val (ρ.bound 11).val := en ▸ et ▸ trace
  have events := Tg_past_events_d.push_l hZF past ns newest entries events _ code trace
  have events : Tg_past_events_d ω H C₂ (ε.bound 4).val (ε.bound 1).val (ε.bound 2).val (ε.bound 20).val :=
    (congrArg Subtype.val (control 4)).symm ▸ (congrArg Subtype.val (control 1)).symm ▸
      (congrArg Subtype.val (control 2)).symm ▸ events
  obtain ⟨r, record, values⟩ := cn.save_issued_l hZF sn.source n₂ ε legal
  let w : Fin 18 → M.Domain := fun i => [N, R₂, L, K₂, η₂, C₂, β₂, β, T₂, Q₂, G₂, E₂, H₂, H, κ, d, π₂, r].get i
  have growing : M.mem κ (ε.bound 24).val := eκ ▸ growth
  have highκ : M.MemberSubset γ κ := fun z hz => subset z (limit.1.transitive _ bound z (high z hz))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, lang⟩ := tg_issued_query_l P (rt_model_ext_l hZF.1 ft.transitive n₂) ε legal
  simp only [tg_reply_language0_m, Formula.satisfies_conj_iff] at lang
  have κlimit := (rt_limit_l ft.transitive n₂ (ZF.modelsKP hZF) (ε.bound 24)).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp lang.2.2.2.1)
  have images' (i : Fin 19) : Rd_entry_d (ι.bound (i.castAdd 27)).val (ε.bound (i.castAdd 27)).val j :=
    Eq.mpr (congrArg (fun z => Rd_entry_d (ι.bound (i.castAdd 27)).val z j)
      (congrArg Subtype.val (control i))) (images (i.castAdd 27))
  have historyKeep : M.MemberSubset (v 13) H := by
    intro p hp
    obtain ⟨a, b, pair⟩ := h.past.sequence.2.1.1 p hp
    have old : Rd_entry_d a b (v 13) := ⟨p, pair, hp⟩
    obtain ⟨r, rp, hr⟩ := (entries a b ((h.past.sequence.2.2 a).mpr ⟨b, old⟩)).mpr old
    exact kpair_unique_l M hZF.1 rp pair ▸ hr
  have span : M.mem (ε.bound 19).val β₂ := ordinal_down_l (ZF.modelsKP hZF)
    (KP.successor_isOrdinal (ZF.modelsKP hZF) (h.source.source.omega.members_areOrdinals hZF _ hn) sm)
    nice₂.tree.diagram.order.ordinal (fun z hz => ((sm z).mp hz).elim
      (h.tree.tree.diagram.order.ordinal.transitive _ h.span z)
      (fun eq => (hZF.1.eq_of_same_members z _ eq).symm ▸ h.span))
    (nice₂.tree.diagram.order.ordinal.transitive β ext₂.1.predecessor_mem _ ext₁.1.predecessor_mem)
  refine ⟨w, (fun i => (ε.bound i).val), ⟨sn, cn, succω (succω h.finite h.successor) ext₁.1,
    ext₂.1, nice₂, node₂, mn, root₂, image₂, anchor₂, record, values,
    (congrArg Subtype.val (control 0)).trans ωθ, (congrArg Subtype.val (control 6)).trans eA,
    fun z hz => κlimit.1.transitive κ growing z (highκ z hz), em.symm ▸ past, links, roots, events, growing, heights, span⟩,
    k, β, T₁, Q₁, G₁, E₁, H₁, j, (θ.bound 20).val, nice₁, ext₁, ext₂, rfl, sm, edge,
    images', images 20, keep, proper, historyKeep, Y, R, μ, K, η₁, C₁, L, W, q,
    (ρ.bound 19).val, (ρ.bound 22).val, (ρ.bound 42).val, newest, ⟨_, code, rfl, rfl, rfl⟩, odd⟩

end YesMetaZFC.SetTheory.LargeCardinal

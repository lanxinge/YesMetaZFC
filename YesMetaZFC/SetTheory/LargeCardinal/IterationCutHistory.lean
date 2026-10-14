import YesMetaZFC.SetTheory.LargeCardinal.IterationNice
import YesMetaZFC.SetTheory.LargeCardinal.IterationCutStep
import YesMetaZFC.SetTheory.LargeCardinal.IterationHistory

/-! # nice 树的实际秩段列与有限历史延伸

高度列 A 和秩段结构码列 D 均是内部集合图。每一步使用原树已有的前驱、
超幂及严格高度下降，自动读取历史中的两个旧行并生成下一行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure It_cut_d (ω α Q E A D : M.Domain) : Prop where
  heights : M.IsSetFunction I A
  height_domain : M.IsDomainOf I α A
  codes : M.IsSetFunction I D
  code_domain : M.IsDomainOf I α D
  ranks : ∀ i c a β X R, Rd_entry_d i c Q → Rd_entry_d i a D → Rd_entry_d i β A → Smem_d I c X R →
    ∃ V S, Smem_d I a V S ∧ M.mem V X ∧ Vr_d X β V ∧ Sc_regular_d X β ∧ M.mem ω V
  contains : ∀ i p κ ρ F a V S, Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d i a D →
    Smem_d I a V S → M.mem ρ V ∧ M.mem F V
  next : ∀ i j p κ ρ F a V S, M.SuccessorOf j i → Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d j a D →
    Smem_d I a V S → M.mem ρ V

/-- 单根的实际严格正则秩段给出高度列和结构码列的原生实例。 -/
theorem it_root_cut_l {ω c X R K β V : M.Domain} (source : Ep_source_d hZF ω ω K X R)
    (model : Smem_d I c X R) (hV : M.mem V X) (rank : Vr_d X β V) (regular : Sc_regular_d X β)
    (hω : M.mem ω V) : ∃ z α T Q G A D a S,
      (∀ x, ¬ M.mem x z) ∧ M.SuccessorOf α z ∧ It_nice_d hZF ω c α T Q G z z ∧
      It_cut_d hZF ω α Q z A D ∧ Rd_entry_d z a D ∧ Smem_d I a V S := by
  obtain ⟨z, α, T, Q, G, hz, hα, nice⟩ := it_nice_root_l hZF ⟨X, R, K, model, source⟩
  obtain ⟨a, S, code⟩ := smdl_membership_l I hZF ⟨ω, hω⟩
  obtain ⟨C, cs⟩ := KP.exists_singleton (ZF.modelsKP hZF) β
  obtain ⟨A, af, as⟩ := ZF.exists_constantFunction hZF I (source := α) ((cs β).mpr rfl)
  obtain ⟨B, bs⟩ := KP.exists_singleton (ZF.modelsKP hZF) a
  obtain ⟨D, df, ds⟩ := ZF.exists_constantFunction hZF I (source := α) ((bs a).mpr rfl)
  refine ⟨z, α, T, Q, G, A, D, a, S, hz, hα, nice, ⟨af.1, af.2.1, df.1, df.2.1, ?_, ?_, ?_⟩,
    (ds z a).mpr ⟨hα.predecessor_mem, rfl⟩, code⟩
  · intro i d b γ Y U hi hb hg my
    obtain ⟨hiα, rfl⟩ := (as i γ).mp hg
    have eqi := ((hα i).mp hiα).elim (fun h => (hz i h).elim) (hZF.1.eq_of_same_members i z)
    subst i
    have eq := nice.tree.diagram.model_function.2 z d c hi (nice.tree.root z hz)
    subst d
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I my.1 model.1
    exact ((ds z b).mp hb).2.symm ▸ ⟨V, S, code, hV, rank, regular, hω⟩
  · intro i p _ _ _ _ _ _ hp
    exact (hp.elim fun r hr => hz r hr.2).elim
  · intro i j p _ _ _ _ _ _ _ hp
    exact (hp.elim fun r hr => hz r hr.2).elim

end
variable (hZFC : M.Models ZFC)

/-- 每一段合法历史的下一步由原树数据构造，没有额外的可延伸性前提。 -/
theorem pn_history_active_l
    {ω c T Q G E L A D C n m H : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (cuts : It_cut_d (ZFC.models_zf_l hZFC) ω ω Q E A D)
    (drop : ∀ i j k f p κ ρ F α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
      Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d k α A → Rd_entry_d j β A →
        ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ)
    (history : Pn_history_d (ZFC.models_zf_l hZFC) ω D L C m H)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (ct : M.TransitiveSet C) (algebra : Sc_algebra_d C)
    (codes : ∀ i a, Rd_entry_d i a D → M.mem a C) (active : ∃ ρ, Rd_entry_d n ρ L) :
    ∃ l J, M.SuccessorOf l m ∧ Pn_history_d (ZFC.models_zf_l hZFC) ω D L C l J ∧
      ∀ i r, Rd_entry_d i r H → Rd_entry_d i r J := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hω := nice.tree.omega
  obtain ⟨m₀, hm₀, hmω⟩ := hω.1.2 n hn
  have eq := hZF.1.eq_of_same_members m₀ m fun x => (hm₀ x).trans (hm x).symm
  subst m₀
  obtain ⟨k, b, a, d, j, p, κ, ρ, F, N, S, X, R, pred, hb, ha, hd, hj, hp, payload, mn, mx,
    loc, agree, ultra, strength, inaccessible, hl⟩ := nice.step_l hZF hmω hm active
  obtain ⟨N₀, S₀, K₀, mn₀, owner₀⟩ := nice.tree.sources n b hb
  obtain ⟨en, es⟩ := smdl_unique_l I mn₀.1 mn.1
  subst N₀ S₀
  obtain ⟨X₀, R₀, K₁, mx₀, parent₀⟩ := nice.tree.sources k a ha
  obtain ⟨ex, er⟩ := smdl_unique_l I mx₀.1 mx.1
  subst X₀ R₀
  obtain ⟨P, U, K₂, mp, next⟩ := nice.tree.sources m d hd
  have ko := (loc.ordinals_l (ZF.modelsKP hZF) owner₀.transitive).1
  obtain ⟨K₃, owner⟩ := owner₀.rebase_l hZF loc.2.1
    (by obtain ⟨_, _, _, _, pre⟩ := loc
        simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
        exact ko.transitive ω pre.1.2.2.1)
    (sc_ordinal_small_l hZF hω owner₀.transitive mn owner₀.theory loc.2.1 ko)
  obtain ⟨K₄, parent⟩ := agree.subset_l.alphabet_l hZF owner parent₀ ko
  obtain ⟨r, hrC, hr⟩ := history.function.2.1 n hm.predecessor_mem
  obtain ⟨b', V, Z, σ, η, cell, hb', row⟩ := history.rows n r hr
  obtain ⟨s, hsC, hs⟩ := history.function.2.1 k pred.1
  obtain ⟨a', W, Y, π, ι, cell', ha', row'⟩ := history.rows k s hs
  obtain ⟨β, hβ⟩ := (cuts.height_domain n).mp hn
  obtain ⟨α, hα⟩ := (cuts.height_domain k).mp (hω.transitive hZF m hmω k pred.1)
  obtain ⟨δ, hδ⟩ := (cuts.height_domain m).mp hmω
  obtain ⟨d', hd'⟩ := (cuts.code_domain m).mp hmω
  obtain ⟨V₀, V₁, mv₀, hV, rv, gv, hωV⟩ := cuts.ranks n b b' β N S hb hb' hβ mn
  obtain ⟨W₀, W₁, mw₀, hW, rw, gw, hωW⟩ := cuts.ranks k a a' α X R ha ha' hα mx
  obtain ⟨B, B₁, mb, hB, rb, gb, _⟩ := cuts.ranks m d d' δ P U hd hd' hδ mp
  have row₀ := row
  have row₁ := row'
  obtain ⟨_, V₂, V₃, c₁, μ, J₀, mv, mz, sz, _⟩ := row₀
  obtain ⟨_, W₂, W₃, c₂, ν, J₁, mw, my, sy, _⟩ := row₁
  obtain ⟨ev, es⟩ := smdl_unique_l I mv₀.1 mv.1
  subst V₀ V₁
  obtain ⟨ew, er⟩ := smdl_unique_l I mw₀.1 mw.1
  subst W₀ W₁
  obtain ⟨hρ, hF⟩ := cuts.contains n p κ ρ F b' V V₂ hp payload hb' mv
  obtain ⟨l, sl, hlω⟩ := hω.1.2 m hmω
  have hρB := cuts.next n m p κ ρ F d' B B₁ hm hp payload hd' mb
  obtain ⟨γ, image, decrease⟩ := drop n m k j p κ ρ F α δ hm pred hj hp payload hα hδ
  have previous : M.MemberSubset Z Y ∧
      ((W = V ∧ Y = Z ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d W Y π V Z σ ρ φ ∧ Es_strength_d W ρ V) := by
    rcases (hm k).mp pred.1 with hk | eq
    · obtain ⟨prior, below, _⟩ := history.past k n s r a' W Y π ι b' V Z σ η hs hr hk cell' cell
      exact ⟨below.elim (fun eq => fun x hx => eq.symm ▸ hx) (fun hz => sy.source.transitive Z hz), prior.prior_l⟩
    · have eq := hZF.1.eq_of_same_members k n eq
      subst k
      have eq := (fn0_function_l (ZF.modelsKP hZF) history.function).1.2 n s r hs hr
      subst s
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := cell'.unique_l cell
      exact ⟨fun _ h => h, Or.inl ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨B', τ, ξ, φ, hBZ, new, exactness, adjacent⟩ := pn_cut_step_l hZFC parent owner next mx mp
    (fun n D A hn hd sub => (agree n D A hn hd sub).symm) ultra hW rw gw hωW hV rv gv hρ hF hB rb gb hρB
    mw mv mb image decrease loc strength inaccessible row' row previous.1 previous.2
  have cell₀ := cell
  obtain ⟨u, path, _⟩ := cell₀
  obtain ⟨v, pv, pr⟩ := path
  have hZC := (pv.mem_l M ct (pr.mem_l M ct hrC).2).1
  obtain ⟨s', hs', cell''⟩ := new.cell_l hZF ct algebra (codes m d' hd') (ct Z hZC B' hBZ)
  obtain ⟨l, J, succ, result, entries⟩ := history.active_push_l hZF hm (hω.members_areOrdinals hZF n hn)
    hr cell row hl (fun i ρ hi hρ => nice.increasing i n ρ _ hρ hl hi) new hd' cell'' hs' hBZ adjacent exactness
  exact ⟨l, J, succ, result, fun i r hr => (entries i r).mpr (Or.inl hr)⟩
/-- 统一下一步：真实扩展器严格缩小模型，空操作保存已保持的同一秩段。 -/
theorem pn_history_extend_l {ω c T Q G E L A D C n m H : M.Domain}
    (nice : It_pnice_d (ZFC.models_zf_l hZFC) ω c ω T Q G E L)
    (cuts : It_cut_d (ZFC.models_zf_l hZFC) ω ω Q E A D)
    (pads : ∀ i j p, M.SuccessorOf j i → Rd_entry_d i p E → (∀ x, ¬ M.mem x p) →
      ∀ a, Rd_entry_d i a D ↔ Rd_entry_d j a D)
    (drop : ∀ i j k f p κ ρ F α β, M.SuccessorOf j i → It_pred_d T k j → It_map_d G k j f →
      Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d k α A → Rd_entry_d j β A →
        ∃ γ, Rd_entry_d α γ f ∧ M.mem β γ)
    (history : Pn_history_d (ZFC.models_zf_l hZFC) ω D L C m H)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (ct : M.TransitiveSet C) (algebra : Sc_algebra_d C)
    (codes : ∀ i a, Rd_entry_d i a D → M.mem a C) :
    ∃ l J, M.SuccessorOf l m ∧ Pn_history_d (ZFC.models_zf_l hZFC) ω D L C l J ∧
      ∀ i r, Rd_entry_d i r H → Rd_entry_d i r J := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  by_cases active : ∃ ρ, Rd_entry_d n ρ L
  · exact pn_history_active_l hZFC nice cuts drop history hn hm ct algebra codes active
  · obtain ⟨m₀, sm, hmω⟩ := nice.tree.omega.1.2 n hn
    have eq := sm.eq hZF.1 hm
    subst m₀
    obtain ⟨p, hp⟩ := (nice.tree.move_domain n).mpr ⟨m, hmω, hm⟩
    have empty : ∀ x, ¬ M.mem x p := (nice.tree.move_cases_l hZF hp).elim id (fun ⟨κ, ρ, F, pay⟩ =>
      (active ⟨ρ, (nice.levels n ρ).mpr ⟨p, κ, F, hp, pay⟩⟩).elim)
    obtain ⟨r, _, hr⟩ := history.function.2.1 n hm.predecessor_mem
    obtain ⟨a, X, P, π, ι, cell, ha, row⟩ := history.rows n r hr
    obtain ⟨l, J, sl, hist, kept⟩ := history.pad_push_l hZF hm (nice.tree.omega.members_areOrdinals hZF n hn)
      hr cell row ((pads n m p hm hp empty a).mp ha) (fun ρ hρ => active ⟨ρ, hρ⟩)
    exact ⟨l, J, sl, hist, fun i r hr => (kept i r).mpr (Or.inl hr)⟩

end YesMetaZFC.SetTheory.LargeCardinal

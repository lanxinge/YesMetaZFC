import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddBranch
import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeSource

/-! # 奇数存档的实际有限树节点

并历史仍按全部内部自然数索引。每个恢复图从原存档的同一完整回答读出，
具有精确的有限定义域，而且与两张坐标图合成原树节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_saved_d.node_l {ω Y R μ K η C L V q : M.Domain} {v : Fin 54 → M.Domain}
    (h : Tg_saved_d hZF ω Y R μ K η C L V q) (cv : Tg_saved_code_d ω V q v) :
    M.mem (v 22) ω ∧ (∀ i, M.mem (v i) Y) ∧ Tg_node_d I (v 22) (v 19) (v 40) (v 41) (v 42) := by
  let nc : Nonempty {x // M.mem x C} := ⟨⟨ω, h.context.omega⟩⟩
  have fs := (h.context.read_l hZF h.source.source).1
  obtain ⟨ρ, code, round, hw, _⟩ := h.read_l hZF nc
  have eq := rt_tuple_inj_l code cv
  have same (i : Fin 54) : (ρ.bound i).val = v i := congrFun eq i.succ.succ
  have seed := ((Formula.satisfies_conj_iff ..).mp round).1
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  obtain ⟨_, _, _, _, _, _, _, first, last, _, _, _, realized, _, _, _, _, _, _, node, _⟩ := seed
  simp only [tt_realized_m, Formula.satisfies_bind, tt_realized0_m, Formula.satisfies_conj_iff] at realized
  have finite : M.mem (ρ.bound 24).val ω := hw ▸ realized.2.1
  have first := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 23) (ρ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp first)
  have last := (rt_successor_l fs.transitive nc hZF.1 (ρ.bound 24) (ρ.bound 23)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp last)
  have finite := h.source.source.omega.transitive hZF _
    (h.source.source.omega.transitive hZF _ finite _ last.predecessor_mem) _ first.predecessor_mem
  let ε := ρ.reindex (fun i : Fin 38 => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  have node : Tg_node_d I (ρ.bound 22).val (ρ.bound 19).val (ρ.bound 40).val
      (ρ.bound 41).val (ρ.bound 42).val :=
    (tg_node_source_l fs.transitive nc hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ε
      (.bound 6) (.bound 3) (.bound 24) (.bound 25) (.bound 26)).mp node
  have member i := h.source.source.transitive C h.context.member _ (ρ.bound i).property
  exact ⟨same 22 ▸ finite, fun i => same i ▸ member i,
    same 22 ▸ same 19 ▸ same 40 ▸ same 41 ▸ same 42 ▸ node⟩

theorem Tg_sequence_d.archive_l {ω c o C γ Z A D f : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω)
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x) :
    M.IsDomainOf I ω (U 5) ∧ Tg_past_links_d I (U 5) (U 1) ∧
      ∀ m i Y R μ K η C L V q, Tg_past_at_d (U 5) m i Y R μ K η C L V q →
        Tg_saved_d hZF ω Y R μ K η C L V q := by
  have read {m i Y R μ K η C L V q}
      (ha : Tg_past_at_d (U 5) m i Y R μ K η C L V q) :
      Tg_saved_d hZF ω Y R μ K η C L V q ∧ ∃ d, Rd_entry_d i d (U 1) ∧ Smem_d I d Y R := by
    obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := ha
    obtain ⟨v, k, s, hs, code, hp⟩ := (columns 5 p).mp hp
    have run := (h.read_l hZF hs code).1
    have ha : Tg_past_at_d (v 13) m i Y R μ K η C L V q := ⟨r, ⟨p, pair, hp⟩, cell⟩
    obtain ⟨d, ⟨z, zp, hz⟩, model⟩ := run.links m i Y R μ K η C L V q ha
    exact ⟨(run.past.read_l hZF ha).1, d,
      ⟨z, zp, (columns 1 z).mpr ⟨v, k, s, hs, code, hz⟩⟩, model⟩
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ _ _ ha => (read ha).2,
    fun _ _ _ _ _ _ _ _ _ _ _ ha => (read ha).1⟩
  intro i
  constructor
  · intro hi
    obtain ⟨s, _, hs⟩ := h.function.2.1 i hi
    obtain ⟨n, succ, v, code, run, num⟩ := h.rows i s hs
    obtain ⟨r, p, pair, hp⟩ := (run.past.sequence.2.2 i).mp (num.symm ▸ succ.predecessor_mem)
    exact ⟨r, p, pair, (columns 5 p).mpr ⟨v, i, s, hs, code, hp⟩⟩
  · rintro ⟨r, p, pair, hp⟩
    obtain ⟨v, k, s, hs, code, hp⟩ := (columns 5 p).mp hp
    obtain ⟨n, succ, w, pack, run, num⟩ := h.rows k s hs
    have eq := rt_tuple_inj_l pack code
    subst w
    have hn := (hw.1.2 k (h.function.bound_l hs).1).elim fun m h => (h.1.eq hZF.1 succ) ▸ h.2
    exact hw.transitive hZF n hn i (num ▸ (run.past.sequence.2.2 i).mpr ⟨r, p, pair, hp⟩)

/-- 较晚轮的奇数结点是前一有限树的高度，严格高于该树中所有旧存档结点。 -/
theorem Tg_sequence_d.archive_order_l {ω c o C γ Z A D f m n r s i j t u : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω)
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (archive : M.IsSetFunction I (U 5)) (hr : Rd_entry_d m r (U 5)) (hs : Rd_entry_d n s (U 5))
    (ri : KPair_d M r i t) (sj : KPair_d M s j u) (lt : M.mem m n) : M.mem i j := by
  have hn := ((h.archive_l hZF hw columns).1 n).mpr ⟨s, hs⟩
  obtain ⟨k, hk, succ⟩ := hw.exists_predecessor_of_mem_of_nonempty hZF hn ⟨m, lt⟩
  obtain ⟨a, _, ha⟩ := h.function.2.1 k hk
  obtain ⟨n', ns, v, code, run, num⟩ := h.rows k a ha
  have round : v 37 = n := num.trans (ns.eq hZF.1 succ)
  obtain ⟨r', hmr⟩ := (run.past.sequence.2.2 m).mp (round.symm ▸ lt)
  have keep {m r} (hr : Rd_entry_d m r (v 13)) : Rd_entry_d m r (U 5) := by
    obtain ⟨p, pair, hp⟩ := hr
    exact ⟨p, pair, (columns 5 p).mpr ⟨v, k, a, ha, code, hp⟩⟩
  have eq := archive.2 m r' r (keep hmr) hr
  subst r'
  obtain ⟨i', Y, R, μ, K, η, C, L, V, q, cell, _⟩ := run.past.rows m r hmr
  have eq : i' = i := (kpair_injective_l M cell.choose_spec.1 ri).1
  subst i'
  obtain ⟨d, hd, _⟩ := run.links m i Y R μ K η C L V q ⟨r, hmr, cell⟩
  have hi := (run.tree.tree.diagram.model_domain i).mpr ⟨d, hd⟩
  obtain ⟨b, _, hb⟩ := h.function.2.1 n hn
  obtain ⟨_, _, w, pack, _⟩ := h.rows n b hb
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    Y', R', μ', K', η', C', L', V', q', _, _, _, _, row, _⟩ := (h.steps k n a b succ ha hb).read_l hZF code pack
  obtain ⟨r', ⟨p, pair, hp⟩, cell'⟩ := row
  have image : Rd_entry_d n r' (U 5) := round ▸
    (show Rd_entry_d (v 37) r' (U 5) from ⟨p, pair, (columns 5 p).mpr ⟨w, n, b, hb, pack, hp⟩⟩)
  have eq := archive.2 n r' s image hs
  subst r'
  have eq : v 6 = j := (kpair_injective_l M cell'.choose_spec.1 sj).1
  exact eq ▸ hi

/-- 原轮号的严格保序性保证一个奇数结点只有一份完整存档。 -/
theorem Tg_sequence_d.archive_unique_l {ω c o C γ Z A D f m n r s i t u : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω)
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (archive : M.IsSetFunction I (U 5)) (hr : Rd_entry_d m r (U 5)) (hs : Rd_entry_d n s (U 5))
    (ri : KPair_d M r i t) (si : KPair_d M s i u) : m = n ∧ r = s := by
  have domain := (h.archive_l hZF hw columns).1
  have hm := (domain m).mpr ⟨r, hr⟩
  have hn := (domain n).mpr ⟨s, hs⟩
  rcases (hw.isOrdinal hZF).wellOrder.linear.compare m hm n hn with eq | lt | gt
  · have eq := hZF.1.eq_of_same_members m n eq
    exact ⟨eq, archive.2 n r s (eq ▸ hr) hs⟩
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i (h.archive_order_l hZF hw columns archive hr hs ri si lt)).elim
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i (h.archive_order_l hZF hw columns archive hs hr si ri gt)).elim

end YesMetaZFC.SetTheory.LargeCardinal

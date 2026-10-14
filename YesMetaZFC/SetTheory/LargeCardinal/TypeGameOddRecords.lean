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

end YesMetaZFC.SetTheory.LargeCardinal

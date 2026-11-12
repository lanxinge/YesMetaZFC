import YesMetaZFC.SetTheory.LargeCardinal.Game.OddBranch
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding

/-! # 奇数存档的实际有限树节点

并历史仍按全部内部自然数索引。每个恢复图从原存档的同一完整回答读出，
具有精确的有限定义域，而且与两张坐标图合成原树节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_saved_d.node_l {ω Y R η C L V q c : M.Domain} {v : Fin 54 → M.Domain}
    (h : Tg_saved_d I ω Y R η C L V q) (hω : M.IsOmega ω)
    (model : Smem_d I c Y R) (trans : M.TransitiveSet Y) (cv : Tg_saved_code_d Y R ω V q v) :
    M.mem (v 22) ω ∧ (∀ i, M.mem (v i) Y) ∧ Tg_node_d I (v 22) (v 19) (v 40) (v 41) (v 42) := by
  let nc : Nonempty {x // M.mem x C} := ⟨⟨ω, h.context.omega_l ⟨c, model⟩⟩⟩
  have ct := (h.context.rank_l (ZF.modelsKP hZF) trans ⟨c, model⟩).transitive_l trans h.context.member
  obtain ⟨ρ, code, round, hw, _⟩ := h.membership_l I hZF.1 model (trans C h.context.member) nc
  have eq := code.inj_l I hZF.1 cv
  have same (i : Fin 54) : (ρ.bound i).val = v i := congrFun eq i.succ.succ
  obtain ⟨finite,node⟩ := tg_round_node_l (ZF.modelsKP hZF) hω ct nc ρ round hw
  exact ⟨same 22 ▸ finite, cv.values_l I hZF.1,
    same 22 ▸ same 19 ▸ same 40 ▸ same 41 ▸ same 42 ▸ node⟩

theorem Tg_sequence_d.archive_l {ω c o C γ Z A D f : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω)
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x) :
    M.IsDomainOf I ω (U 5) ∧ Tg_past_links_d I (U 5) (U 1) ∧
      ∀ m i Y R μ K η C L V q, Tg_past_at_d (U 5) m i Y R μ K η C L V q →
        M.TransitiveSet Y ∧ Tg_saved_d I ω Y R η C L V q := by
  have read {m i Y R μ K η C L V q}
      (ha : Tg_past_at_d (U 5) m i Y R μ K η C L V q) :
      (M.TransitiveSet Y ∧ Tg_saved_d I ω Y R η C L V q) ∧ ∃ d, Rd_entry_d i d (U 1) ∧ Smem_d I d Y R := by
    obtain ⟨r, ⟨p, pair, hp⟩, cell⟩ := ha
    obtain ⟨v, k, s, hs, code, hp⟩ := (columns 5 p).mp hp
    have run := (h.read_l hZF hs code).1
    have ha : Tg_past_at_d (v 13) m i Y R μ K η C L V q := ⟨r, ⟨p, pair, hp⟩, cell⟩
    obtain ⟨d, ⟨z, zp, hz⟩, model⟩ := run.links m i Y R μ K η C L V q ha
    exact ⟨⟨(run.past.read_l hZF ha).1.source.transitive, (run.past.read_l hZF ha).2.1⟩, d,
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
    exact hw.transitive (ZF.modelsKP hZF) n hn i (num ▸ (run.past.sequence.2.2 i).mpr ⟨r, p, pair, hp⟩)

/-- 较晚轮的奇数结点是前一有限树的高度，严格高于该树中所有旧存档结点。 -/
theorem Tg_sequence_d.archive_order_l {ω c o C γ Z A D f m n r s i j t u : M.Domain} {U : Fin 6 → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f) (hw : M.IsOmega ω)
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
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
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (n := 63) ⟨8+a.val, by omega⟩ f x)
    (archive : M.IsSetFunction I (U 5)) (hr : Rd_entry_d m r (U 5)) (hs : Rd_entry_d n s (U 5))
    (ri : KPair_d M r i t) (si : KPair_d M s i u) : m = n ∧ r = s := by
  have domain := (h.archive_l hZF hw columns).1
  have hm := (domain m).mpr ⟨r, hr⟩
  have hn := (domain n).mpr ⟨s, hs⟩
  rcases (hw.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare m hm n hn with eq | lt | gt
  · have eq := hZF.1.eq_of_same_members m n eq
    exact ⟨eq, archive.2 n r s (eq ▸ hr) hs⟩
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i (h.archive_order_l hZF hw columns archive hr hs ri si lt)).elim
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) i (h.archive_order_l hZF hw columns archive hs hr si ri gt)).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 奇数边上的三张坐标图在返回极限中相容

继续边严格使用被原请求选中的完整存档。三张图的嵌入像均包含于新图，
故在同一返回锥中的像也满足包含；空标签仍保留原重置分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_odd_compatible_d (ω H G π P : M.Domain) : Prop := ∀ ξ α k e t ℓ Sₑ S n s g,
  (∃ m Y R μ K η C L V q, Tg_past_at_d H m α Y R μ K η C L V q) →
  Tg_odd_d ω H ξ α k G e t ℓ Sₑ S n s g → (t = e ∧ k = ξ ∧ g = e) ∨
    ∃ Y R μ K η C L V q S₀ n₀ s₀ t₀ g₀,
      Tg_past_at_d H ℓ k Y R μ K η C L V q ∧ Tg_saved_branch_d Y R ω V q S₀ n₀ s₀ t₀ g₀ ∧
      M.mem n₀ ω ∧ M.SuccessorOf n n₀ ∧
      ∀ (i : Fin 3) a b p q x y, Rd_entry_d a ([s₀,t₀,g₀].get i) π → Rd_entry_d b ([s,t,g].get i) π →
        Rd_entry_d k p P → Rd_entry_d α q P → Rd_entry_d a x p → Rd_entry_d b y q → M.MemberSubset x y

theorem It_pull_subset_d.odd_l (hZF : M.Models ZF) {ω H T Q G π P : M.Domain}
    (h : It_pull_subset_d G π P) (hw : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (links : Tg_past_links_d (kp_pair_l (ZF.modelsKP hZF)) H Q)
    (saved : ∀ m i Y R μ K η C L V q, Tg_past_at_d H m i Y R μ K η C L V q →
      M.TransitiveSet Y ∧ Tg_saved_d (kp_pair_l (ZF.modelsKP hZF)) ω Y R η C L V q) :
    Tg_odd_compatible_d ω H G π P := by
  intro ξ α k e t ℓ Sₑ S n s g present odd
  rcases odd with reset | ⟨_, Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, j, a, b, z, row, branch,
    hj, _, hn, hga, succ, _, graph, is, ss, it, st⟩
  · exact Or.inl ⟨reset.1, reset.2.1, reset.2.2.1⟩
  · obtain ⟨yt, old⟩ := saved _ _ _ _ _ _ _ _ _ _ _ row
    have hb := branch
    obtain ⟨v, code, _, num, _⟩ := hb
    obtain ⟨c, hc, mc⟩ := links _ _ _ _ _ _ _ _ _ _ _ row
    have finite : M.mem n₀ ω := num ▸ (old.node_l hZF hw mc yt code).1
    obtain ⟨m, X, R', μ', K', η', C', L', V', q', row'⟩ := present
    obtain ⟨d, hd, mx⟩ := links _ _ _ _ _ _ _ _ _ _ _ row'
    have xt := (saved _ _ _ _ _ _ _ _ _ _ _ row').1
    have emb := diagram.elementary k α j c Y R d X R' hj hc hd mc.1 mx.1
    have fixed := emb.natural_l hZF hw yt xt mc mx old.context.omega_mem n₀ finite
    have eq := emb.1.1.1.2 n₀ b n₀ hn fixed
    subst b
    refine Or.inr ⟨Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, row, branch, finite, succ, ?_⟩
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) i <;>
      intro x y p q u v hx hy hp hq hu hv
    · exact h k α j x s₀ y s s₀ p q u v hj hx hy is ss hp hq hu hv
    · exact h k α j x t₀ y t t₀ p q u v hj hx hy it st hp hq hu hv
    · exact h k α j x g₀ y g a p q u v hj hx hy hga (fun z hz => (graph z).mpr (Or.inl hz)) hp hq hu hv

/-- 原存档的恒等解释直接沿同一个极限锥保持奇数历史；只读取两份实际存档。 -/
theorem It_embedding_d.odd_l (hZF : M.Models ZF) {ω H T Q G π P b d N W : M.Domain}
    (hw : M.IsOmega ω) (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G)
    (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q G d N W P)
    (mn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N W) (nt : M.TransitiveSet N)
    (identity : ∀ x y, Rd_entry_d x y π → x = y)
    (links : Tg_past_links_d (kp_pair_l (ZF.modelsKP hZF)) H Q)
    (saved : ∀ m i Y R μ K η C L V q, Tg_past_at_d H m i Y R μ K η C L V q →
      M.TransitiveSet Y ∧ Tg_saved_d (kp_pair_l (ZF.modelsKP hZF)) ω Y R η C L V q) :
    Tg_odd_compatible_d ω H G π P := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro ξ α k e t ℓ Sₑ S n s g present odd
  rcases odd with reset | ⟨_, Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, j, a, b, z, row, branch,
    hj, _, hn, hga, succ, _, graph, is, ss, it, st⟩
  · exact Or.inl ⟨reset.1, reset.2.1, reset.2.2.1⟩
  · obtain ⟨yt, old⟩ := saved _ _ _ _ _ _ _ _ _ _ _ row
    have hb := branch
    obtain ⟨v, code, _, num, _⟩ := hb
    obtain ⟨c, hc, mc⟩ := links _ _ _ _ _ _ _ _ _ _ _ row
    have finite : M.mem n₀ ω := num ▸ (old.node_l hZF hw mc yt code).1
    obtain ⟨m, X, R', μ', K', η', C', L', V', q', row'⟩ := present
    obtain ⟨d, hd, mx⟩ := links _ _ _ _ _ _ _ _ _ _ _ row'
    have xt := (saved _ _ _ _ _ _ _ _ _ _ _ row').1
    have emb := diagram.elementary k α j c Y R d X R' hj hc hd mc.1 mx.1
    have fixed := emb.natural_l hZF hw yt xt mc mx old.context.omega_mem n₀ finite
    have eq := emb.1.1.1.2 n₀ b n₀ hn fixed
    subst b
    have carry {a b z p q x y : M.Domain} (image : Rd_entry_d a z j) (sub : M.MemberSubset z b)
        (hp : Rd_entry_d k p P) (hq : Rd_entry_d α q P) (hax : Rd_entry_d a x p) (hby : Rd_entry_d b y q) :
        M.MemberSubset x y := by
      have left := cone.elementary k p c Y R hp hc mc.1
      have right := cone.elementary α q d X R' hq hd mx.1
      obtain ⟨z', _, hz⟩ := right.1.1.2.2 z (emb.1.1.output_mem_of_pairMember image)
      have eq := left.1.1.1.2 a z' x (cone.commute k α j p q hj hp hq a z z' image hz) hax
      exact eq ▸ (right.subset_l hZF hw xt nt mx mn hz hby).mp sub
    refine Or.inr ⟨Y, R, μ, K, η, C, L, V, q, S₀, n₀, s₀, t₀, g₀, row, branch, finite, succ, ?_⟩
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) i <;>
      intro x y p q u v hx hy hp hq hu hv
    · have ex := identity x s₀ hx
      have ey := identity y s hy
      subst x y
      exact carry is ss hp hq hu hv
    · have ex := identity x t₀ hx
      have ey := identity y t hy
      subst x y
      exact carry it st hp hq hu hv
    · have ex := identity x g₀ hx
      have ey := identity y g hy
      subst x y
      exact carry hga (fun z hz => (graph z).mpr (Or.inl hz)) hp hq hu hv

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原恢复图、共同极限证书及一阶公式

公式只量化原保存码的固定元数坐标。内部轮号、结点、有限长度及两层
嵌入条目保持原值，供替代和内部归纳直接使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

section

def Tg_return_node_d (ω H π P m i n S s t g : M.Domain) : Prop :=
  ∃ Y R μ K η C L V q, ∃ v : Fin 54 → M.Domain,
    Tg_past_at_d H m i Y R μ K η C L V q ∧ Tg_saved_code_d Y R ω V q v ∧ n = v 22 ∧
    ∃ a b c d j, Rd_entry_d a (v 19) π ∧ Rd_entry_d b (v 40) π ∧
      Rd_entry_d c (v 41) π ∧ Rd_entry_d d (v 42) π ∧ Rd_entry_d i j P ∧
      Rd_entry_d a S j ∧ Rd_entry_d b s j ∧ Rd_entry_d c t j ∧ Rd_entry_d d g j

/-- 按同一轮号读取恢复图；归档函数性排除另选记录。 -/
theorem Tg_return_node_d.graphs_l (hZF : M.Models ZF) {ω H π P m i n S s t g Y R μ K η C L V q S' n' s' t' g' : M.Domain}
    (h : Tg_return_node_d ω H π P m i n S s t g) (hf : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) H)
    (row : Tg_past_at_d H m i Y R μ K η C L V q) (br : Tg_saved_branch_d Y R ω V q S' n' s' t' g') :
    n = n' ∧ ∀ a : Fin 3, ∃ x j, Rd_entry_d x ([s',t',g'].get a) π ∧
      Rd_entry_d i j P ∧ Rd_entry_d x ([s,t,g].get a) j := by
  obtain ⟨Y₀, R₀, μ₀, K₀, η₀, C₀, L₀, V₀, q₀, v, old, code, num,
    _, a, b, c, j, _, ia, ib, ic, leg, _, va, vb, vc⟩ := h
  obtain ⟨r, hr, cell⟩ := row
  obtain ⟨r₀, hr₀, cell₀⟩ := old
  have eq := hf.2 m r₀ r hr₀ hr
  subst r₀
  have eq := rt_tuple_inj_l cell₀ cell
  have eY : Y₀ = Y := congrFun eq 1
  have eR : R₀ = R := congrFun eq 2
  have eV : V₀ = V := congrFun eq 8
  have eq : q₀ = q := congrFun eq 9
  subst Y₀ R₀ V₀ q₀
  obtain ⟨w, cw, _, hn, hs, ht, hg⟩ := br
  have eq := code.inj_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1 cw
  have en : v 22 = w 22 := congrFun eq 24
  have es : v 40 = w 40 := congrFun eq 42
  have et : v 41 = w 41 := congrFun eq 43
  have eg : v 42 = w 42 := congrFun eq 44
  refine ⟨num.trans (en.trans hn), fun k => ?_⟩
  exact Fin.cases ⟨a,j,es.trans hs ▸ ia,leg,va⟩
    (Fin.cases ⟨b,j,et.trans ht ▸ ib,leg,vb⟩ (Fin.cases ⟨c,j,eg.trans hg ▸ ic,leg,vc⟩ (fun k => Fin.elim0 k))) k

def Tg_return_growth_d (hZF : M.Models ZF) (ω H π P N m i ℓ k : M.Domain) : Prop :=
  ∃ n S s t g n₀ S₀ s₀ t₀ g₀, M.mem n ω ∧ M.mem n₀ ω ∧ M.mem g N ∧ M.mem g₀ N ∧
    M.SuccessorOf n n₀ ∧ Tg_node_d (kp_pair_l (ZF.modelsKP hZF)) n S s t g ∧
    Tg_node_d (kp_pair_l (ZF.modelsKP hZF)) n₀ S₀ s₀ t₀ g₀ ∧
    Tg_return_node_d ω H π P m i n S s t g ∧ Tg_return_node_d ω H π P ℓ k n₀ S₀ s₀ t₀ g₀ ∧
    (∀ a : Fin 3, M.MemberSubset ([s₀,t₀,g₀].get a) ([s,t,g].get a)) ∧ g₀ ≠ g

-- 取并只消费锥中的实际恢复图，不消费返回原模型的映射。
structure Tg_odd_limit_d (hZF : M.Models ZF) (ω T G b H π N P : M.Domain) : Prop where
  transitive : M.TransitiveSet N
  omega_mem : M.mem ω N
  injective : ∀ a b x, Rd_entry_d a x π → Rd_entry_d b x π → a = b
  function : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) P
  legs : ∀ i j, Rd_entry_d i j P → M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) j
  nodes : ∀ m i r t₀, M.mem i b → Rd_entry_d m r H → KPair_d M r i t₀ → ∃ n S s t g,
    M.mem n ω ∧ M.mem S N ∧ M.mem s N ∧ M.mem t N ∧ M.mem g N ∧
    Tg_node_d (kp_pair_l (ZF.modelsKP hZF)) n S s t g ∧ Tg_return_node_d ω H π P m i n S s t g
  proper : ∀ m ξ α k e t ℓ Sₑ Y R μ K η C L V q S n s g,
    M.mem α b → Tg_past_at_d H m α Y R μ K η C L V q → Tg_saved_branch_d Y R ω V q S n s t g →
    Tg_odd_d ω H ξ α k G e t ℓ Sₑ S n s g → It_pred_d T k α → t ≠ e →
      Tg_return_growth_d hZF ω H π P N m α ℓ k

/-- 5.15 另外使用的返回因子；它不再是任意良基分支取并的前提。 -/
def Tg_return_model_d (hZF : M.Models ZF) (ω o c X T Q G b π N P : M.Domain) : Prop :=
  ∃ A Rₐ a U Rᵤ u Q₀ G₀ c₀ X₀ R₀ π₀ d W σ,
    M.TransitiveSet A ∧ M.TransitiveSet U ∧ M.mem ω A ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) a A Rₐ ∧ Smem_d (kp_pair_l (ZF.modelsKP hZF)) u U Rᵤ ∧
    Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω a u A U π ∧
    Rd_entry_d Q₀ Q π ∧ Rd_entry_d G₀ G π ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) c₀ X₀ R₀ ∧ Rd_entry_d c₀ c π ∧ Rd_entry_d X₀ X π ∧
    M.IsRestrictionOf (kp_pair_l (ZF.modelsKP hZF)) π₀ π X₀ ∧
    It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q₀ G₀ ∧ Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N W ∧
    It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b Q₀ G₀ d N W P ∧
    Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω d c N X σ ∧
    ∃ j, Rd_entry_d o j P ∧ It_comp_d j σ π₀

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 非重置奇数边在同一个锥中严格增加长度，并延长全部恢复图。 -/
theorem Tg_odd_compatible_d.growth_l {ω T G b H π N P : M.Domain}
    (growth : Tg_odd_compatible_d ω H G π P) (hw : M.IsOmega ω) (order : It_order_d ω T)
    (branch : It_branch_d ω T b) (archive : M.IsSetFunction I H)
    (nodes : ∀ m i r t₀, M.mem i b → Rd_entry_d m r H → KPair_d M r i t₀ → ∃ n S s t g,
      M.mem n ω ∧ M.mem S N ∧ M.mem s N ∧ M.mem t N ∧ M.mem g N ∧
      Tg_node_d I n S s t g ∧ Tg_return_node_d ω H π P m i n S s t g) :
    ∀ m ξ α k e t ℓ Sₑ Y R μ K η C L V q S n s g,
      M.mem α b → Tg_past_at_d H m α Y R μ K η C L V q → Tg_saved_branch_d Y R ω V q S n s t g →
      Tg_odd_d ω H ξ α k G e t ℓ Sₑ S n s g → It_pred_d T k α → t ≠ e →
        Tg_return_growth_d hZF ω H π P N m α ℓ k := by
  intro m ξ α k e t ℓ Sₑ Y R μ K η C L V q S n s g hi row br odd pred ne
  have hk := branch.down k α ((pred.2 k).mpr (Or.inr (order.refl k
    (hw.transitive (ZF.modelsKP hZF) α (branch.subset α hi) k pred.1)))) hi
  rcases growth ξ α k e t ℓ Sₑ S n s g ⟨m, Y, R, μ, K, η, C, L, V, q, row⟩ odd with reset | ⟨Y₁, R₁, μ₁, K₁, η₁, C₁, L₁, V₁, q₁, S₁, n₁, s₁, t₁, g₁, row₁, br₁, _, succ, sub⟩
  · exact (ne reset.1).elim
  · have get {m i Y R μ K η C L V q} (hi : M.mem i b)
        (row : Tg_past_at_d H m i Y R μ K η C L V q) : ∃ n S s t g,
        M.mem n ω ∧ M.mem S N ∧ M.mem s N ∧ M.mem t N ∧ M.mem g N ∧
        Tg_node_d I n S s t g ∧ Tg_return_node_d ω H π P m i n S s t g := by
      obtain ⟨r, hr, cell⟩ := row
      exact nodes m i r cell.choose hi hr cell.choose_spec.1
    obtain ⟨n', S', s', t', g', hn', _, _, _, hg', node', trace'⟩ := get hi row
    obtain ⟨n₀, S₀, s₀, t₀, g₀, hn₀, _, _, _, hg₀, node₀, trace₀⟩ := get hk row₁
    obtain ⟨en, images'⟩ := trace'.graphs_l hZF archive row br
    obtain ⟨en₀, images₀⟩ := trace₀.graphs_l hZF archive row₁ br₁
    have succ : M.SuccessorOf n' n₀ := en.symm ▸ en₀.symm ▸ succ
    refine ⟨n', S', s', t', g', n₀, S₀, s₀, t₀, g₀, hn', hn₀, hg', hg₀, succ,
      node', node₀, trace', trace₀, ?_, ?_⟩
    · intro a
      obtain ⟨x, j₀, ix, hj₀, vx⟩ := images₀ a
      obtain ⟨y, j', iy, hj', vy⟩ := images' a
      exact sub a x y j₀ j' _ _ ix iy hj₀ hj' vx vy
    · intro eq
      obtain ⟨z, hz⟩ := (node'.2.2.1.2 n₀).mp succ.predecessor_mem
      exact KP.mem_irrefl_d (ZF.modelsKP hZF) n₀ ((node₀.2.2.1.2 n₀).mpr ⟨z, eq.symm ▸ hz⟩)

end

private def tg_return_body_m : Formula 1 79 := .conj
  (tg_past_at_m (.bound 69) (.bound 72) (.bound 73) (.bound 0) (.bound 1) (.bound 2)
    (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8)) (.conj
  (tg_saved_code_m (.bound 0) (.bound 1) (.bound 68) (.bound 7) (.bound 8)
    (fun i : Fin 54 => .bound (Fin.natAdd 14 (i.castAdd 11))))
  (set[79] ⟪⌜(.bound 74 : Term 79)⌝ₛ = ⌜(.bound 36 : Term 79)⌝ₛ ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 9 : Term 79)⌝ₛ, ⌜(.bound 33 : Term 79)⌝ₛ, ⌜(.bound 70 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 10 : Term 79)⌝ₛ, ⌜(.bound 54 : Term 79)⌝ₛ, ⌜(.bound 70 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 11 : Term 79)⌝ₛ, ⌜(.bound 55 : Term 79)⌝ₛ, ⌜(.bound 70 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 12 : Term 79)⌝ₛ, ⌜(.bound 56 : Term 79)⌝ₛ, ⌜(.bound 70 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 73 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ, ⌜(.bound 71 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 9 : Term 79)⌝ₛ, ⌜(.bound 75 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 10 : Term 79)⌝ₛ, ⌜(.bound 76 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 11 : Term 79)⌝ₛ, ⌜(.bound 77 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 12 : Term 79)⌝ₛ, ⌜(.bound 78 : Term 79)⌝ₛ, ⌜(.bound 13 : Term 79)⌝ₛ)⟫))

def tg_return_node0_m : Formula 1 11 := rt_exists_m 54 (rt_exists_m 14 tg_return_body_m)

private theorem tg_return_body_closed_l : tg_return_body_m.FreeClosed := by
  refine ⟨by simp -implicitDefEqProofs, ?_⟩
  exact ⟨tg_saved_code_closed_l _ _ _ _ _ _ rfl rfl rfl rfl rfl (fun _ => rfl),
    by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]⟩

theorem tg_return_node0_closed_l : tg_return_node0_m.FreeClosed :=
  (rt_exists_closed_l _).mpr ((rt_exists_closed_l _).mpr tg_return_body_closed_l)

theorem tg_return_node0_sat_l (hE : Extensional M) (ρ : Env M 11) :
    Formula.satisfies ρ tg_return_node0_m ↔ Tg_return_node_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2)
      (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10) := by
  have read (v : Fin 54 → M.Domain) (u : Fin 14 → M.Domain) :
      Formula.satisfies (rt_push_d (rt_push_d ρ 54 v) 14 u) tg_return_body_m ↔
        Tg_past_at_d (ρ.bound 1) (ρ.bound 4) (ρ.bound 5) (u 0) (u 1) (u 2) (u 3) (u 4) (u 5) (u 6) (u 7) (u 8) ∧
        Tg_saved_code_d (u 0) (u 1) (ρ.bound 0) (u 7) (u 8) v ∧ ρ.bound 6 = v 22 ∧
        Rd_entry_d (u 9) (v 19) (ρ.bound 2) ∧ Rd_entry_d (u 10) (v 40) (ρ.bound 2) ∧
        Rd_entry_d (u 11) (v 41) (ρ.bound 2) ∧ Rd_entry_d (u 12) (v 42) (ρ.bound 2) ∧
        Rd_entry_d (ρ.bound 5) (u 13) (ρ.bound 3) ∧ Rd_entry_d (u 9) (ρ.bound 7) (u 13) ∧
        Rd_entry_d (u 10) (ρ.bound 8) (u 13) ∧ Rd_entry_d (u 11) (ρ.bound 9) (u 13) ∧ Rd_entry_d (u 12) (ρ.bound 10) (u 13) := by
    -- 两个固定元组先一次合并赋值，避免逐个字段反复展开六十八层 push。
    let σ : Env M 79 := ⟨Fin.addCases (motive := fun _ => M.Domain) u
      (Fin.addCases (motive := fun _ => M.Domain) v ρ.bound), ρ.free⟩
    have values : (rt_push_d (rt_push_d ρ 54 v) 14 u).bound = σ.bound := by
      funext i
      refine Fin.addCases (m := 14) (n := 65) (fun j => ?_) (fun j => ?_) i
      · simp only [σ, Fin.addCases_left]
        have e : j.castAdd 65 = (⟨j.val, by omega⟩ : Fin 79) := Fin.ext rfl
        exact (congrArg (rt_push_d (rt_push_d ρ 54 v) 14 u).bound e).trans
          (rt_push_new_l (rt_push_d ρ 54 v) u j)
      · simp only [σ, Fin.addCases_right]
        rw [show (rt_push_d (rt_push_d ρ 54 v) 14 u).bound (Fin.natAdd 14 j) =
          (rt_push_d ρ 54 v).bound j from rt_push_old_l (rt_push_d ρ 54 v) u j]
        refine Fin.addCases (m := 54) (n := 11) (fun k => ?_) (fun k => ?_) j
        · simp only [Fin.addCases_left]
          have e : k.castAdd 11 = (⟨k.val, by omega⟩ : Fin 65) := Fin.ext rfl
          exact (congrArg (rt_push_d ρ 54 v).bound e).trans (rt_push_new_l ρ v k)
        · simp only [Fin.addCases_right]
          have e : Fin.natAdd 54 k = (⟨54+k.val, by omega⟩ : Fin 65) := Fin.ext rfl
          exact (congrArg (rt_push_d ρ 54 v).bound e).trans (rt_push_old_l ρ v k)
    apply (Formula.closed_env_l tg_return_body_m tg_return_body_closed_l values).trans
    simp only [tg_return_body_m, Formula.satisfies_conj_iff, tg_past_at_sat_l hE, tg_saved_code_sat_l,
      Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE, Term.eval_bound,
      σ, Fin.addCases_left, Fin.addCases_right]
    rfl
  rw [tg_return_node0_m, rt_exists_sat_l]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu⟩ := (rt_exists_sat_l ..).mp hv
    obtain ⟨row, code, num, facts⟩ := (read v u).mp hu
    exact ⟨u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, v, row, code, num, u 9, u 10, u 11, u 12, u 13, facts⟩
  · rintro ⟨Y, R, μ, K, η, C, L, V, q, v, row, code, num, a, b, c, d, j, facts⟩
    let u : Fin 14 → M.Domain := fun i => [Y, R, μ, K, η, C, L, V, q, a, b, c, d, j].get i
    exact ⟨v, (rt_exists_sat_l ..).mpr ⟨u, (read v u).mpr ⟨row, code, num, facts⟩⟩⟩

def tg_return_node_m {d} (ω H π P m i n S s t g : Term d) : Formula 1 d :=
  tg_return_node0_m.bind (fun j => [ω,H,π,P,m,i,n,S,s,t,g].get j)

@[simp] theorem tg_return_node_closed_l {d} (v : Fin 11 → Term d) (hv : ∀ i, (v i).freeSupport = []) :
    (tg_return_node0_m.bind v).FreeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _ hv _).mpr tg_return_node0_closed_l

theorem tg_return_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H π P m i n S s t g : Term d) :
    Formula.satisfies ρ (tg_return_node_m ω H π P m i n S s t g) ↔
      Tg_return_node_d (ω.eval ρ) (H.eval ρ) (π.eval ρ) (P.eval ρ) (m.eval ρ) (i.eval ρ)
        (n.eval ρ) (S.eval ρ) (s.eval ρ) (t.eval ρ) (g.eval ρ) := by
  rw [tg_return_node_m, Formula.satisfies_bind, tg_return_node0_sat_l hE]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

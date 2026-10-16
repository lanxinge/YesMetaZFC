import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddRecords
import YesMetaZFC.SetTheory.LargeCardinal.IterationHullReturn
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameOddCompatibility
import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeEmbedding

/-! # 任意奇数极限中的原恢复图

先回拉完整存档，再取同一返回锥的像。每个有限节点仍带有原存档、壳映射
和极限投影的实际条目；有限长度由自然数固定性保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_return_node_d (ω H π P m i n S s t g : M.Domain) : Prop :=
  ∃ Y R μ K η C L V q, ∃ v : Fin 54 → M.Domain,
    Tg_past_at_d H m i Y R μ K η C L V q ∧ Tg_saved_code_d ω V q v ∧ n = v 22 ∧
    ∃ a b c d j, Rd_entry_d a (v 19) π ∧ Rd_entry_d b (v 40) π ∧
      Rd_entry_d c (v 41) π ∧ Rd_entry_d d (v 42) π ∧ Rd_entry_d i j P ∧
      Rd_entry_d a S j ∧ Rd_entry_d b s j ∧ Rd_entry_d c t j ∧ Rd_entry_d d g j

/-- 按同一轮号读取恢复图；归档函数性排除另选记录。 -/
theorem Tg_return_node_d.graphs_l (hZF : M.Models ZF) {ω H π P m i n S s t g Y R μ K η C L V q S' n' s' t' g' : M.Domain}
    (h : Tg_return_node_d ω H π P m i n S s t g) (hf : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) H)
    (row : Tg_past_at_d H m i Y R μ K η C L V q) (br : Tg_saved_branch_d ω V q S' n' s' t' g') :
    n = n' ∧ ∀ a : Fin 3, ∃ x j, Rd_entry_d x ([s',t',g'].get a) π ∧
      Rd_entry_d i j P ∧ Rd_entry_d x ([s,t,g].get a) j := by
  obtain ⟨Y₀, R₀, μ₀, K₀, η₀, C₀, L₀, V₀, q₀, v, old, code, num,
    _, a, b, c, j, _, ia, ib, ic, leg, _, va, vb, vc⟩ := h
  obtain ⟨r, hr, cell⟩ := row
  obtain ⟨r₀, hr₀, cell₀⟩ := old
  have eq := hf.2 m r₀ r hr₀ hr
  subst r₀
  have eq := rt_tuple_inj_l cell₀ cell
  have eV : V₀ = V := congrFun eq 8
  have eq : q₀ = q := congrFun eq 9
  subst V₀ q₀
  obtain ⟨w, cw, _, hn, hs, ht, hg⟩ := br
  have eq := rt_tuple_inj_l code cw
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
    M.mem α b → Tg_past_at_d H m α Y R μ K η C L V q → Tg_saved_branch_d ω V q S n s t g →
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
    It_diagram_d hZF ω ω T Q₀ G₀ ∧ Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N W ∧
    It_embedding_d hZF ω b Q₀ G₀ d N W P ∧
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
      M.mem α b → Tg_past_at_d H m α Y R μ K η C L V q → Tg_saved_branch_d ω V q S n s t g →
      Tg_odd_d ω H ξ α k G e t ℓ Sₑ S n s g → It_pred_d T k α → t ≠ e →
        Tg_return_growth_d hZF ω H π P N m α ℓ k := by
  intro m ξ α k e t ℓ Sₑ Y R μ K η C L V q S n s g hi row br odd pred ne
  have hk := branch.down k α ((pred.2 k).mpr (Or.inr (order.refl k
    (hw.transitive hZF α (branch.subset α hi) k pred.1)))) hi
  rcases growth ξ α k e t ℓ Sₑ S n s g odd with reset | ⟨Y₁, R₁, μ₁, K₁, η₁, C₁, L₁, V₁, q₁, S₁, n₁, s₁, t₁, g₁, row₁, br₁, _, succ, sub⟩
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

theorem Tg_sequence_d.odd_limit_l {ω c o C γ Z A D f X B b : M.Domain} {U : Fin 6 → M.Domain}
    {k} {v : Fin k → M.Domain}
    (h : Tg_sequence_d hZF ω c o C γ Z A D f)
    (tree : It_pnice_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) (U 4))
    (archive : M.IsSetFunction I (U 5))
    (columns : ∀ a x, M.mem x (U a) ↔ Tg_run_value_d ⟨8+a.val, by omega⟩ f x)
    (back : It_hull_return_d hZF ω o c X (U 0) (U 1) (U 2) (U 3) (U 4) B b
      (Fin.cases (U 5) v)) :
    ∃ π N P, Tg_return_model_d hZF ω o c X (U 0) (U 1) (U 2) b π N P ∧
      Tg_odd_limit_d hZF ω (U 0) (U 2) b (U 5) π N P ∧
      ∀ i, ∃ x, Rd_entry_d x (v i) π := by
  obtain ⟨B₀, Rₐ, a, K, V₀, Rᵤ, u, J, π, c₀, X₀, R₀, π₀, Q₀, G₀, E₀, L₀,
    sb, su, mb, mu, hj, _, mx₀, hcc, hXX, restrict, _, small, hQ, hG, _, _, ret, _, params⟩ := back
  obtain ⟨H₀, _, hH⟩ := params 0
  obtain ⟨_, _, _, _, _, _, d, N, W, P, σ, branch, _, _, mn, cone, ready, hs, _, root⟩ := ret
  have hw := tree.tree.omega
  have omega := hj.omega_l I hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  have nat := hj.natural_l hZF hw sb.transitive su.transitive mb mu sb.omega_mem
  have ar := h.archive_l hZF hw columns
  have hf : Tg_graph_d I ω H₀ := (hj.tg_graph_l hZF hw sb.transitive su.transitive mb mu omega hH).mpr ⟨archive, ar.1⟩
  obtain ⟨N', W', _, mn', sn⟩ := ready
  obtain ⟨eN, eW⟩ := smdl_unique_l I mn'.1 mn.1
  subst N' W'
  have compatible := it_cone_pull_subset_l hZF hw sb.transitive su.transitive sn.transitive mb mu mn hj
    sb.omega_mem (hj.1.1.input_mem_of_pairMember hQ) hG small.tree.diagram tree.tree.diagram (by
      intro i c hc
      obtain ⟨Y, R, _, my, sy⟩ := small.tree.sources i c hc
      exact ⟨Y, R, my, sy.transitive⟩) cone.toIt_embedding_d
  have growth := compatible.odd_l hZF hw tree.tree.diagram (by
    intro i c hc
    obtain ⟨Y, R, _, my, sy⟩ := tree.tree.sources i c hc
    exact ⟨Y, R, my, sy.transitive⟩) ar.2.1 ar.2.2
  suffices nodes : ∀ m i r t₀, M.mem i b → Rd_entry_d m r (U 5) → KPair_d M r i t₀ → ∃ n S s t g,
      M.mem n ω ∧ M.mem S N ∧ M.mem s N ∧ M.mem t N ∧ M.mem g N ∧
      Tg_node_d I n S s t g ∧ Tg_return_node_d ω (U 5) π P m i n S s t g by
    refine ⟨π, N, P, ⟨B₀, Rₐ, a, V₀, Rᵤ, u, Q₀, G₀, c₀, X₀, R₀, π₀, d, W, σ,
      sb.transitive, su.transitive, sb.omega_mem, mb, mu, hj, hQ, hG, mx₀, hcc, hXX, restrict,
      small.tree.diagram, mn, cone.toIt_embedding_d, hs, root⟩,
      ⟨sn.transitive, sn.omega_mem, hj.1.2, cone.function, ?_, nodes,
        growth.growth_l hZF hw tree.tree.diagram.order branch archive nodes⟩,
      fun i => (params i.succ).elim fun x h => ⟨x, h.2⟩⟩
    intro i j hij
    obtain ⟨c, X, R, hc, mx⟩ := small.tree.diagram.model_l hZF (branch.subset i ((cone.domain i).mpr ⟨j, hij⟩))
    exact (cone.elementary i j c X R hij hc mx).1.1.1
  intro m i r t₀ hi hr pair
  have hm := (ar.1 m).mpr ⟨r, hr⟩
  obtain ⟨r₀, hr₀⟩ := (hf.2 m).mp hm
  have hrB := (rd_entry_transitive_l sb.transitive (hj.1.1.input_mem_of_pairMember hH) hr₀).2
  obtain ⟨r', _, hrr⟩ := hj.1.1.2.2 r₀ hrB
  have eq := archive.2 m r' r ((hj.entry_l hZF hw sb.transitive su.transitive mb mu (nat m hm) hrr hH).mp hr₀) hr
  subst r'
  obtain ⟨p, pr, hp⟩ := hr
  obtain ⟨v, k, z, hz, code, hp⟩ := (columns 5 p).mp hp
  obtain ⟨i', Y, R, μ, K, η, C, L, V, q, cell, saved, _⟩ := (h.read_l hZF hz code).1.past.rows m r ⟨p, pr, hp⟩
  have eq : i' = i := (kpair_injective_l M cell.choose_spec.1 pair).1
  subst i'
  have row : Tg_past_at_d (U 5) m i Y R μ K η C L V q :=
    ⟨r, ⟨p, pr, (columns 5 p).mpr ⟨v, k, z, hz, code, hp⟩⟩, cell⟩
  obtain ⟨w, _, images⟩ := hj.tuple_preimage_l hZF hw sb.transitive su.transitive mb mu hrr cell
  obtain ⟨ρ, cq, _, _, _⟩ := saved.read_l hZF ⟨⟨ω, saved.context.omega⟩⟩
  obtain ⟨s, _, values⟩ := hj.tuple_preimage_l hZF hw sb.transitive su.transitive mb mu (images 9) cq
  obtain ⟨hn, member, node⟩ := saved.node_l hZF cq
  let n := (ρ.bound 22).val
  have hiω := branch.subset i hi
  obtain ⟨a₀, ha₀⟩ := (small.tree.diagram.model_domain i).mp hiω
  obtain ⟨Y₀, R', K', my, sy⟩ := small.tree.sources i a₀ ha₀
  have haB := (rd_entry_transitive_l sb.transitive (hj.1.1.input_mem_of_pairMember hQ) ha₀).2
  obtain ⟨a', _, haa⟩ := hj.1.1.2.2 a₀ haB
  have ha := (hj.entry_l hZF hw sb.transitive su.transitive mb mu (nat i hiω) haa hQ).mp ha₀
  obtain ⟨a'', ha', my'⟩ := ar.2.1 m i Y R μ K η C L V q row
  have eq := tree.tree.diagram.model_function.2 i a' a'' ha ha'
  subst a''
  obtain ⟨Y', R'', _, orig, source⟩ := tree.tree.sources i a' ha
  obtain ⟨eY, eR⟩ := smdl_unique_l I orig.1 my'.1
  subst Y' R''
  obtain ⟨Y', R'', _, _, my'', _, imageY, _⟩ := ep_set_source_pull_l hZF sb su mb mu hj haa my' source
  obtain ⟨eY, eR⟩ := smdl_unique_l I my''.1 my.1
  subst Y' R''
  have smallMember (a : Fin 54) : M.mem (s a.succ.succ) Y₀ :=
    (hj.member_l I hZF hw mb mu (values a.succ.succ) imageY).mpr (member a)
  let x : Fin 5 → M.Domain := fun a => [n, s 21, s 42, s 43, s 44].get a
  let y : Fin 5 → M.Domain := fun a => [n, (ρ.bound 19).val, (ρ.bound 40).val, (ρ.bound 41).val, (ρ.bound 42).val].get a
  have xy : ∀ a, Rd_entry_d (x a) (y a) π :=
    Fin.cases (nat n hn) (Fin.cases (values 21) (Fin.cases (values 42)
      (Fin.cases (values 43) (Fin.cases (values 44) (fun a => Fin.elim0 a)))))
  have smallNode := (hj.tg_node_l hZF hw sb.transitive su.transitive mb mu xy).mpr node
  obtain ⟨j, hjP⟩ := (cone.domain i).mp hi
  have leg := cone.elementary i j a₀ Y₀ R' hjP ha₀ my.1
  obtain ⟨S, hS, iS⟩ := leg.1.1.2.2 (s 21) (smallMember 19)
  obtain ⟨s', hs', is⟩ := leg.1.1.2.2 (s 42) (smallMember 40)
  obtain ⟨t', ht', it⟩ := leg.1.1.2.2 (s 43) (smallMember 41)
  obtain ⟨g, hg, ig⟩ := leg.1.1.2.2 (s 44) (smallMember 42)
  have fixed := leg.natural_l hZF hw sy.transitive sn.transitive my mn sy.omega_mem n hn
  let y' : Fin 5 → M.Domain := fun a => [n, S, s', t', g].get a
  have image : ∀ a, Rd_entry_d (x a) (y' a) j :=
    Fin.cases fixed (Fin.cases iS (Fin.cases is (Fin.cases it (Fin.cases ig (fun a => Fin.elim0 a)))))
  exact ⟨n, S, s', t', g, hn, hS, hs', ht', hg,
    (leg.tg_node_l hZF hw sy.transitive sn.transitive my mn image).mp smallNode,
    Y, R, μ, K, η, C, L, V, q, (fun a => (ρ.bound a).val), row, cq, rfl,
    s 21, s 42, s 43, s 44, j, values 21, values 42, values 43, values 44, hjP, iS, is, it, ig⟩

end YesMetaZFC.SetTheory.LargeCardinal

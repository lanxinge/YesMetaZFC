import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawExactHistory
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # 有效后继步自动扩张整棵迭代树

一次调用实际添加树序、模型、所有祖先嵌入和操作记录。已有后继步及
极限条件均由精确旧图方程保留；新步的施加证书与新边绑定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_tree_extend_l {ω c₀ α ξ T Q G E k c d b X R Y S j p : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smdl_d I d X R) (my : Smdl_d I b Y S)
    (hj : Smap_d I ω d b X Y j) (source : It_source_d hZF ω b)
    (step : ((∀ x, ¬ M.mem x p) ∧ k = ξ ∧ b = c ∧ ∀ x y, Rd_entry_d x y j → x = y) ∨ It_active_d hZF ω c d b j p) :
    ∃ β U Q' G' E', M.SuccessorOf β α ∧ It_tree_d hZF ω c₀ β U Q' G' E' ∧
      (∀ i l, Rd_entry_d i l U ↔ Rd_entry_d i l T ∨ l = α ∧ (i = α ∨ Rd_entry_d i k T)) ∧
      (∀ i a, Rd_entry_d i a Q' ↔ Rd_entry_d i a Q ∨ i = α ∧ a = b) ∧
      (∀ i l f, M.mem l α → (It_map_d G' i l f ↔ It_map_d G i l f)) ∧
      (∀ i a, Rd_entry_d i a E' ↔ Rd_entry_d i a E ∨ i = ξ ∧ a = p) ∧ It_map_d G' k α j := by
  have order := tree.diagram.order
  have no : ¬ M.mem α α := fun ha => order.ordinal.wellOrder.linear.irrefl α ha ha
  have hk := (tree.diagram.model_domain k).mpr ⟨d, hd⟩
  obtain ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs, edge⟩ :=
    it_diagram_extend_l hZF tree.omega tree.diagram hα hd mx my hj
  have fresh a (ha : Rd_entry_d ξ a E) : False := by
    obtain ⟨η, hη, hηξ⟩ := (tree.move_domain ξ).mp ⟨a, ha⟩
    exact no (Structure.SuccessorOf.eq hZF.1 hηξ hα ▸ hη)
  obtain ⟨E', ef, es⟩ := it_move_push_l (ZF.modelsKP hZF) tree.move_function fresh (p := p)
  have old i l (hl : M.mem l α) : Rd_entry_d i l U ↔ Rd_entry_d i l T :=
    (us i l).trans ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hl)).elim), Or.inl⟩
  have qold i a (hi : M.mem i α) : Rd_entry_d i a Q' ↔ Rd_entry_d i a Q :=
    (qs i a).trans ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have gold i l f (hl : M.mem l α) : It_map_d G' i l f ↔ It_map_d G i l f :=
    (gs i l f).trans ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hl)).elim), Or.inl⟩
  have older η (hη : M.mem η β) : M.mem η α ∨ η = α :=
    ((hβ η).mp hη).imp_right (hZF.1.eq_of_same_members η α)
  have predecessor : It_pred_d U k α := ⟨hk, fun i => (us i α).trans
    ⟨fun hh => hh.elim (fun hh => (no (order.bound i α hh).2).elim)
        (fun hh => hh.2.imp_right ((old i k hk).mpr)),
      fun hh => Or.inr ⟨rfl, hh.imp_right ((old i k hk).mp)⟩⟩⟩
  have domain i : (∃ a, Rd_entry_d i a E') ↔ ∃ η, M.mem η β ∧ M.SuccessorOf η i := by
    constructor
    · rintro ⟨a, ha⟩
      rcases (es i a).mp ha with ha | ⟨rfl, _⟩
      · obtain ⟨η, hη, hηi⟩ := (tree.move_domain i).mp ⟨a, ha⟩
        exact ⟨η, (hβ η).mpr (Or.inl hη), hηi⟩
      · exact ⟨α, hβ.predecessor_mem, hα⟩
    · rintro ⟨η, hη, hηi⟩
      rcases older η hη with hη | rfl
      · obtain ⟨a, ha⟩ := (tree.move_domain i).mpr ⟨η, hη, hηi⟩
        exact ⟨a, (es i a).mpr (Or.inl ha)⟩
      · have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (order.ordinal.mem hηi.predecessor_mem) hηi hα
        exact ⟨p, (es i p).mpr (Or.inr ⟨eq, rfl⟩)⟩
  have steps i η (hη : M.mem η β) (hηi : M.SuccessorOf η i) : It_step_d hZF ω U Q' G' E' i η := by
    rcases older η hη with hη | rfl
    · obtain ⟨l, c, d, b, f, a, ⟨hlη, pred⟩, hc, hd, hb, hf, ha, valid⟩ := tree.steps i η hη hηi
      have hl := order.ordinal.transitive η hη l hlη
      exact ⟨l, c, d, b, f, a, ⟨hlη, fun x => (old x η hη).trans ((pred x).trans (or_congr Iff.rfl (old x l hl).symm))⟩,
        (qs i c).mpr (Or.inl hc), (qs l d).mpr (Or.inl hd), (qs η b).mpr (Or.inl hb),
        (gold l η f hη).mpr hf, (es i a).mpr (Or.inl ha), valid⟩
    · have eq := Structure.SuccessorOf.predecessor_eq hZF.1 (order.ordinal.mem hηi.predecessor_mem) hηi hα
      subst i
      exact ⟨k, c, d, b, j, p, predecessor, (qs ξ c).mpr (Or.inl hc), (qs k d).mpr (Or.inl hd),
        (qs _ b).mpr (Or.inr ⟨rfl, rfl⟩), edge, (es ξ p).mpr (Or.inr ⟨rfl, rfl⟩), step⟩
  have limits δ (hδ : M.mem δ β) (hl : M.IsLimitOrdinal δ) : It_limit_d U Q' G' δ := by
    have hδα : M.mem δ α := (older δ hδ).elim id fun eq =>
      (it_successor_not_limit_l hZF.1 (order.ordinal.mem hα.predecessor_mem) hα (eq ▸ hl)).elim
    intro c X R hc hp y hy
    obtain ⟨i, hi, hiδ, f, hf, x, hxy⟩ := tree.limits δ hδα hl c X R ((qold δ c hδα).mp hc) hp y hy
    exact ⟨i, hi, (old i δ hδα).mpr hiδ, f, (gold i δ f hδα).mpr hf, x, hxy⟩
  refine ⟨β, U, Q', G', E', hβ,
    { omega := tree.omega, diagram := diagram
      root := fun z hz => (qs z c₀).mpr (Or.inl (tree.root z hz))
      move_function := ef, move_domain := domain, steps := steps, limits := limits
      sources := ?_ }, us, qs, gold, es, edge⟩
  intro i a ha
  rcases (qs i a).mp ha with ha | ⟨_, rfl⟩
  · exact tree.sources i a ha
  · exact source

/-- 本次原关系超幂的同一目标、常值图和操作码直接进入指定树前驱。 -/
theorem it_apply_l {ω c₀ α ξ T Q G E k c d b j p : M.Domain}
    (h : It_active_d hZF ω c d b j p) (tree : It_tree_d hZF ω c₀ α T Q G E)
    (hα : M.SuccessorOf α ξ) (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q)
    (source : It_source_d hZF ω b) :
    ∃ β U Q' G' E', It_tree_d hZF ω c₀ β U Q' G' E' ∧
      It_extension_d α ξ k T Q G E β U Q' G' E' ∧
      Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧ Rd_entry_d ξ p E' ∧
      ∀ i f g, It_map_d G i k f → It_comp_d f j g → It_map_d G' i α g := by
  have active := h
  obtain ⟨κ, ℓ, F, X, R, Y, S, _, _, parent, data⟩ := h
  obtain ⟨w, z, Γ, t, L, J, O, Z, A, q, V, W, r, N, B, _, _, data⟩ := data
  obtain ⟨_, _, _, _, _, target, map, _⟩ := data
  obtain ⟨β, U', Q', G', E', hβ, next, us, qs, gs, es, edge⟩ :=
    it_tree_extend_l hZF tree hα hc hd parent target map source (Or.inr active)
  refine ⟨β, U', Q', G', E', next, ⟨hβ, us, fun i a hi => (qs i a).mpr (Or.inl hi), gs,
    fun i a hi => (es i a).mpr (Or.inl hi), fun i a hi => ?_⟩,
    (qs α b).mpr (Or.inr ⟨rfl, rfl⟩), edge, (es ξ p).mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
  · exact (es i a).trans ⟨fun h => h.elim id (fun h => (hi h.1).elim), Or.inl⟩
  · intro i f g hf comp
    have old := (gs i k f ((tree.diagram.model_domain k).mpr ⟨d, hd⟩)).mpr hf
    have ik := next.diagram.map_bound_l hZF old
    obtain ⟨r, hr⟩ := next.diagram.map_l hZF
      (next.diagram.order.trans i k α ik (next.diagram.map_bound_l hZF edge))
    obtain ⟨a, X₀, R₀, ha, mx⟩ := next.diagram.model_l hZF (next.diagram.order.bound i k ik).1
    have ff := next.diagram.elementary i k f a X₀ R₀ d Y S old ha ((qs k d).mpr (Or.inl hd)) mx parent
    have rr := next.diagram.elementary i α r a X₀ R₀ b N B hr ha ((qs α b).mpr (Or.inr ⟨rfl, rfl⟩)) mx target
    have square := next.diagram.comp i k α f j r old edge hr
    have actual : It_comp_d f j r := by
      refine ⟨rr.1.1.1.1, fun x z => ⟨?_, fun ⟨y, hxy, hyz⟩ => square x y z hxy hyz⟩⟩
      intro hxz
      obtain ⟨y, hy, hxy⟩ := ff.1.1.2.2 x (rr.1.1.input_mem_of_pairMember hxz)
      obtain ⟨z', _, hyz⟩ := map.1.1.2.2 y hy
      exact ⟨y, hxy, rr.1.1.1.2 x z' z (square x y z' hxy hyz) hxz ▸ hyz⟩
    exact (comp.unique_l hZF.1 actual).symm ▸ hr

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原树操作列的实际支撑列

空操作没有支撑，实际扩展器操作恰追加它自己的支撑。
两种更新只读取原树和操作载荷，不要求任何工作复制历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原恒等边不产生支撑；原支撑列逐项保持。 -/
theorem It_extension_d.levels_pad_l
    {m n k T Q G E θ T₁ Q₁ G₁ E₁ L : M.Domain}
    (extension : It_extension_d m n k T Q G E θ T₁ Q₁ G₁ E₁)
    (empty : ∀ p, Rd_entry_d n p E₁ → ∀ x, ¬ M.mem x p)
    (levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F) :
    ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ ρ F := by
  classical
  intro i ρ
  constructor
  · intro hi
    obtain ⟨p,κ,F,hp,pay⟩ := (levels i ρ).mp hi
    exact ⟨p,κ,F,extension.2.2.2.2.1 i p hp,pay⟩
  · rintro ⟨p,κ,F,hp,pay⟩
    by_cases eq : i = n
    · subst i
      obtain ⟨r,⟨a,b,_,_,pair⟩,_⟩ := pay
      exact (empty p hp a ((pair a).mpr (Or.inl rfl))).elim
    · exact (levels i ρ).mpr ⟨p,κ,F,(extension.2.2.2.2.2 i p eq).mp hp,pay⟩

/-- 同一次实际扩展器的支撑进入原列，并保留全部旧条目。 -/
theorem It_tree_d.levels_extend_l
    {ω c n m T Q G E L k l T₁ Q₁ G₁ E₁ p κ μ F : M.Domain}
    (tree : It_tree_d hZF ω c m T Q G E) (hm : M.SuccessorOf m n)
    (function : M.IsSetFunction I L)
    (levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (next : It_tree_d hZF ω c l T₁ Q₁ G₁ E₁)
    (extension : It_extension_d m n k T Q G E l T₁ Q₁ G₁ E₁)
    (move : Rd_entry_d n p E₁) (payload : It_payload_d p κ μ F) :
    ∃ L₁, M.IsSetFunction I L₁ ∧
      (∀ i ρ, Rd_entry_d i ρ L₁ ↔ ∃ p κ F, Rd_entry_d i p E₁ ∧ It_payload_d p κ ρ F) ∧
      (∀ i ρ, Rd_entry_d i ρ L₁ ↔ Rd_entry_d i ρ L ∨ i = n ∧ ρ = μ) := by
  classical
  have no ρ (hρ : Rd_entry_d n ρ L) : False := by
    obtain ⟨p,κ,F,hp,_⟩ := (levels n ρ).mp hρ
    obtain ⟨j,hj,succ⟩ := (tree.move_domain n).mp ⟨p,hp⟩
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) m (succ.eq hZF.1 hm ▸ hj)
  obtain ⟨L₁,fn,entries⟩ := it_move_push_l (ZF.modelsKP hZF) function no (p := μ)
  refine ⟨L₁,fn,?_,entries⟩
  intro i ρ
  constructor
  · intro hi
    rcases (entries i ρ).mp hi with hi | ⟨rfl,rfl⟩
    · obtain ⟨q,a,B,hq,pay⟩ := (levels i ρ).mp hi
      exact ⟨q,a,B,extension.2.2.2.2.1 i q hq,pay⟩
    · exact ⟨p,κ,F,move,payload⟩
  · rintro ⟨q,a,B,hq,pay⟩
    by_cases eq : i = n
    · subst i
      have eq := next.move_function.2 n q p hq move
      subst q
      exact (entries n ρ).mpr (Or.inr ⟨rfl,(pay.unique_l payload).2.1⟩)
    · exact (entries i ρ).mpr
        (Or.inl ((levels i ρ).mpr ⟨q,a,B,(extension.2.2.2.2.2 i q eq).mp hq,pay⟩))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 单根迭代树及恒等延长的实际实例

长度是对象模型中的 1，模型列、对角嵌入列和空操作列均实际构造。
pad 随后复用同一个后继扩张定理，自动保存全部旧图与极限条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_root_l {ω c : M.Domain} (ready : It_source_d hZF ω c) :
    ∃ z α T Q G, (∀ x, ¬ M.mem x z) ∧ M.SuccessorOf α z ∧ It_tree_d hZF ω c α T Q G z := by
  obtain ⟨X, R, _, _, _, code, _, _⟩ := ready.objects
  obtain ⟨z, hz, hzω⟩ := ready.omega.1.1
  obtain ⟨α, hα, hαω⟩ := ready.omega.1.2 z hzω
  have one i (hi : M.mem i α) : i = z := ((hα i).mp hi).elim
    (fun hi => (hz i hi).elim) (hZF.1.eq_of_same_members i z)
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => z⟩
  have idread i j := Formula.denote_identityValue_iff hZF.1 ρ i j
  obtain ⟨T, ht, ts₀⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I BinarySchema.identityValue ρ (source := α) (target := α)
    (fun i _ => ⟨i, (idread i i).mpr rfl⟩)
    (fun i _ j k hj hk => ((idread i j).mp hj).symm.trans ((idread i k).mp hk))
    (fun i j hi hj => (idread i j).mp hj ▸ hi)
  have ts i j : Rd_entry_d i j T ↔ M.mem i α ∧ i = j := (ts₀ i j).trans (and_congr_right fun _ => idread i j)
  obtain ⟨C, hC⟩ := KP.exists_singleton (ZF.modelsKP hZF) c
  obtain ⟨Q, hQ, qs⟩ := ZF.exists_constantFunction hZF I (source := α) ((hC c).mpr rfl)
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (c := c) (X := X) ready.omega
  obtain ⟨D, hD⟩ := KP.exists_singleton (ZF.modelsKP hZF) e
  obtain ⟨G, hG, gs⟩ := ZF.exists_constantFunction hZF I (source := T) ((hD e).mpr rfl)
  have maps i j f : It_map_d G i j f ↔ Rd_entry_d i j T ∧ f = e := by
    constructor
    · rintro ⟨r, hr, hrf⟩
      obtain ⟨hrT, eq⟩ := (gs r f).mp hrf
      exact ⟨⟨r, hr, hrT⟩, eq⟩
    · rintro ⟨⟨r, hr, hrT⟩, rfl⟩
      exact ⟨r, hr, (gs r _).mpr ⟨hrT, rfl⟩⟩
  have impossible i j (hj : M.mem j α) (hs : M.SuccessorOf j i) : False :=
    hz i (one j hj ▸ hs.predecessor_mem)
  have no_limit i (hi : M.mem i α) (hl : M.IsLimitOrdinal i) : False := by
    obtain ⟨j, hj⟩ := hl.2.1
    exact hz j (one i hi ▸ hj)
  have order : It_order_d α T := ⟨ready.omega.members_areOrdinals (ZF.modelsKP hZF) α hαω, ht.1.1,
    fun i j hij => ⟨ht.input_mem_of_pairMember hij, ht.output_mem_of_pairMember hij⟩,
    fun i hi => (ts i i).mpr ⟨hi, rfl⟩,
    fun i j k hij hjk => (ts i k).mpr ⟨((ts i j).mp hij).1, ((ts i j).mp hij).2.trans ((ts j k).mp hjk).2⟩,
    fun i j hij => Or.inl ((ts i j).mp hij).2,
    fun i j k hik hjk => Or.inl ((ts i j).mpr ⟨((ts i k).mp hik).1, ((ts i k).mp hik).2.trans ((ts j k).mp hjk).2.symm⟩),
    fun i j hj hs => (impossible i j hj hs).elim, fun i hi hl => (no_limit i hi hl).elim⟩
  have diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G := by
    refine ⟨order, hQ.1, hQ.2.1, fun i b hb => ?_, hG.1, hG.2.1, ?_, ?_, ?_⟩
    · exact ((qs i b).mp hb).2.symm ▸ ⟨X, R, code⟩
    · intro i j f b Y S d Z V hf hb hd mb md
      have eb := ((qs i b).mp hb).2
      have ed := ((qs j d).mp hd).2
      have ef := ((maps i j f).mp hf).2
      subst b d f
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mb code
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I md code
      exact he
    · intro i f hf x y hxy
      exact ((es x y).mp (((maps i i f).mp hf).2 ▸ hxy)).2
    · intro i j k f g h hf hg hh x y z hxy hyz
      have ef := ((maps i j f).mp hf).2
      have eg := ((maps j k g).mp hg).2
      have eh := ((maps i k h).mp hh).2
      subst f g h
      exact ((es x y).mp hxy).2.symm ▸ hyz
  have empty i x (hix : Rd_entry_d i x z) : False := hix.elim fun r hr => hz r hr.2
  refine ⟨z, α, T, Q, G, hz, hα,
    { omega := ready.omega, diagram := diagram, root := ?_
      move_function := ⟨fun p hp => (hz p hp).elim, fun i x _ hix _ => (empty i x hix).elim⟩
      move_domain := ?_, steps := fun i j hj hs => (impossible i j hj hs).elim
      limits := fun i hi hl => (no_limit i hi hl).elim
      sources := fun i b hb => ((qs i b).mp hb).2.symm ▸ ready }⟩
  · intro z' hz'
    have eq := hZF.1.eq_of_same_members z' z fun x => iff_of_false (hz' x) (hz x)
    exact (qs z' c).mpr ⟨eq.symm ▸ hα.predecessor_mem, rfl⟩
  · intro i
    exact ⟨fun ⟨x, hx⟩ => (empty i x hx).elim, fun ⟨j, hj, hs⟩ => (impossible i j hj hs).elim⟩

theorem it_pad_l {ω c₀ α ξ T Q G E : M.Domain} (tree : It_tree_d hZF ω c₀ α T Q G E)
    (hα : M.SuccessorOf α ξ) : ∃ β U Q' G' E' c j, M.SuccessorOf β α ∧ It_tree_d hZF ω c₀ β U Q' G' E' ∧
      It_extension_d α ξ ξ T Q G E β U Q' G' E' ∧ Rd_entry_d ξ c Q ∧ Rd_entry_d α c Q' ∧ It_map_d G' ξ α j ∧
      (∀ x y, Rd_entry_d x y j → x = y) ∧ (∀ i f, Rd_entry_d i f E → Rd_entry_d i f E') ∧
      ∀ p, Rd_entry_d ξ p E' → ∀ x, ¬ M.mem x p := by
  obtain ⟨c, hc⟩ := (tree.diagram.model_domain ξ).mp hα.predecessor_mem
  obtain ⟨X, R, _, _, _, code, _, _⟩ := (tree.sources ξ c hc).objects
  obtain ⟨j, hj, js⟩ := smap_identity_l I hZF (c := c) (X := X) tree.omega
  obtain ⟨p, hp⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have idj x y (hxy : Rd_entry_d x y j) := ((js x y).mp hxy).2
  obtain ⟨β, U, Q', G', E', hβ, h', us, qs, gs, es, edge⟩ := it_tree_extend_l hZF tree hα hc hc code code hj
    (tree.sources ξ c hc) (Or.inl ⟨hp, rfl, rfl, idj⟩)
  refine ⟨β, U, Q', G', E', c, j, hβ, h', ⟨hβ, us, fun i a hi => (qs i a).mpr (Or.inl hi), gs,
    fun i a hi => (es i a).mpr (Or.inl hi), ?_⟩, hc, (qs α c).mpr (Or.inr ⟨rfl, rfl⟩), edge, idj,
    fun i f hi => (es i f).mpr (Or.inl hi), ?_⟩
  · exact fun i a hi => (es i a).trans ⟨fun hh => hh.elim id (fun hh => (hi hh.1).elim), Or.inl⟩
  · intro q hq
    have eq := h'.move_function.2 ξ q p hq ((es ξ p).mpr (Or.inr ⟨rfl, rfl⟩))
    exact eq.symm ▸ hp

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## nice 支撑证书及实际空树实例

每个非空操作给出所属模型的实际传递呈示及其强度证据，字面支撑由该规范呈示解释。
支撑比较属于该附加证书；
一般原关系迭代树独立保存真实超幂边。单根实例直接来自原源的恒等图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 支撑列只记录实际扩展器；恒等 padding 不添加虚假的支撑。 -/
structure It_pnice_d (ω c α T Q G E L : M.Domain) : Prop where
  tree : It_tree_d hZF ω c α T Q G E
  function : M.IsSetFunction I L
  levels : ∀ i ρ, Rd_entry_d i ρ L ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F
  exactness : ∀ i p κ ρ F, Rd_entry_d i p E → It_payload_d p κ ρ F →
    ∃ a X R, Rd_entry_d i a Q ∧ Smem_d I a X R ∧ M.TransitiveSet X ∧
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ ρ X F ∧ Sc_inaccessible_d ω X ρ
  increasing : ∀ i j ρ φ, Rd_entry_d i ρ L → Rd_entry_d j φ L → M.mem i j → M.mem ρ φ

/-- 无 padding 的子类用于逐项复制；共同强度条件全部继承自一般树。 -/
structure It_nice_d (ω c α T Q G E L : M.Domain) : Prop extends It_pnice_d hZF ω c α T Q G E L where
  active : ∀ i p, Rd_entry_d i p E → ∃ κ ρ F, It_payload_d p κ ρ F

/-- 有限树的末项支撑界住整列；最后一项允许等号。 -/
theorem It_pnice_d.last_bound_l {ω c β α ξ T Q G E H L : M.Domain}
    (h : It_pnice_d hZF ω c β T Q G E H) (hb : M.SuccessorOf β α) (ha : M.SuccessorOf α ξ)
    (last : Rd_entry_d ξ L H) : ∀ i μ, Rd_entry_d i μ H → M.mem μ L ∨ μ = L := by
  intro i μ hi
  obtain ⟨p, _, _, hp, _⟩ := (h.levels i μ).mp hi
  obtain ⟨j, hj, sj⟩ := (h.tree.move_domain i).mp ⟨p, hp⟩
  have oa := h.tree.diagram.order.ordinal.mem hb.predecessor_mem
  have hia : M.mem i α := ((hb j).mp hj).elim
    (fun hj => oa.transitive j hj i sj.predecessor_mem)
    (fun eq => (hZF.1.eq_of_same_members j α eq) ▸ sj.predecessor_mem)
  rcases (ha i).mp hia with lt | eq
  · exact Or.inl (h.increasing i ξ μ L hi last lt)
  · have eq := hZF.1.eq_of_same_members i ξ eq
    exact Or.inr (h.function.2 ξ μ L (eq ▸ hi) last)

theorem it_nice_root_l {ω c : M.Domain} (source : It_source_d hZF ω c) :
    ∃ z α T Q G, (∀ x, ¬ M.mem x z) ∧ M.SuccessorOf α z ∧ It_nice_d hZF ω c α T Q G z z := by
  obtain ⟨z, α, T, Q, G, hz, hα, tree⟩ := it_root_l hZF source
  have no i p (h : Rd_entry_d i p z) : False := h.elim fun r hr => hz r hr.2
  exact ⟨z, α, T, Q, G, hz, hα, ⟨tree, tree.move_function,
    fun i ρ => ⟨fun h => (no i ρ h).elim, fun ⟨p, _, _, h, _⟩ => (no i p h).elim⟩,
    fun i p _ _ _ h _ => (no i p h).elim,
    fun i _ ρ _ h => (no i ρ h).elim⟩, fun i p h => (no i p h).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## nice 树的原始强度条件

操作列中的每个扩展器以支撑为最大强度，该支撑在所属模型中不可达，
并沿操作序严格递增。单根及实际超幂添枝直接构造这些条件的实例。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原树步中的 padding 与非空扩展器码矛盾，故读取的是同一条实际超幂边。 -/
theorem It_pnice_d.step_l {ω c₀ α T Q G E L i j : M.Domain}
    (h : It_pnice_d hZF ω c₀ α T Q G E L) (hj : M.mem j α) (succ : M.SuccessorOf j i) (active : ∃ ρ, Rd_entry_d i ρ L) :
    ∃ k c d b f p κ ρ F X R Y S,
      It_pred_d T k j ∧ Rd_entry_d i c Q ∧ Rd_entry_d k d Q ∧ Rd_entry_d j b Q ∧ It_map_d G k j f ∧
      Rd_entry_d i p E ∧ It_payload_d p κ ρ F ∧ Smem_d I c X R ∧ M.TransitiveSet X ∧ Smdl_d I d Y S ∧ It_active_d hZF ω c d b f p ∧
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ ρ X F ∧ Sc_inaccessible_d ω X ρ ∧ Rd_entry_d i ρ L := by
  obtain ⟨k, c, d, b, f, p, pred, hc, hd, hb, hf, hp, step⟩ := h.tree.steps i j hj succ
  rcases step with ⟨empty, _⟩ | op
  · obtain ⟨ρ, hl⟩ := active
    obtain ⟨q, κ, F, hq, pay⟩ := (h.levels i ρ).mp hl
    have eq := h.tree.move_function.2 i q p hq hp
    obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := eq ▸ pay
    exact (empty u ((pair u).mpr (Or.inl rfl))).elim
  · have raw := op
    obtain ⟨κ, ρ, F, _, _, Y, S, payload, _, my, _⟩ := op
    obtain ⟨a, X, R, ha, mx, trans, strength, inaccessible⟩ := h.exactness i p κ ρ F hp payload
    have eq := h.tree.diagram.model_function.2 i a c ha hc
    subst a
    exact ⟨k, c, d, b, f, p, κ, ρ, F, X, R, Y, S, pred, hc, hd, hb, hf, hp, payload, mx, trans, my,
      raw, strength, inaccessible, (h.levels i ρ).mpr ⟨p, κ, F, hp, payload⟩⟩

/-- 原树步中的 padding 与非空扩展器码矛盾，故读取的是同一条实际超幂边。 -/
theorem It_nice_d.step_l {ω c₀ α T Q G E L i j : M.Domain}
    (h : It_nice_d hZF ω c₀ α T Q G E L) (hj : M.mem j α) (succ : M.SuccessorOf j i) :
    ∃ k c d b f p κ ρ F X R Y S,
      It_pred_d T k j ∧ Rd_entry_d i c Q ∧ Rd_entry_d k d Q ∧ Rd_entry_d j b Q ∧ It_map_d G k j f ∧
      Rd_entry_d i p E ∧ It_payload_d p κ ρ F ∧ Smem_d I c X R ∧ M.TransitiveSet X ∧ Smdl_d I d Y S ∧ It_active_d hZF ω c d b f p ∧
      Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ ρ X F ∧ Sc_inaccessible_d ω X ρ ∧ Rd_entry_d i ρ L := by
  obtain ⟨p, hp⟩ := (h.tree.move_domain i).mpr ⟨j, hj, succ⟩
  obtain ⟨κ, ρ, F, pay⟩ := h.active i p hp
  exact h.toIt_pnice_d.step_l hZF hj succ ⟨ρ, (h.levels i ρ).mpr ⟨p, κ, F, hp, pay⟩⟩

/-- 同一个真实扩展器添枝，同时延长其最大强度列。 -/
theorem it_pnice_apply_l {ω c₀ α ξ T Q G E L k c d b j X R κ ρ F p : M.Domain}
    (h : It_pnice_d hZF ω c₀ α T Q G E L) (hα : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c Q) (hd : Rd_entry_d k d Q) (mx : Smem_d I c X R) (xt : M.TransitiveSet X)
    (payload : It_payload_d p κ ρ F) (active : It_active_d hZF ω c d b j p)
    (source : It_source_d hZF ω b) (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ ρ X F)
    (inaccessible : Sc_inaccessible_d ω X ρ) (above : ∀ i φ, Rd_entry_d i φ L → M.mem φ ρ) :
    ∃ β U Q' G' E' L', It_pnice_d hZF ω c₀ β U Q' G' E' L' ∧
      It_extension_d α ξ k T Q G E β U Q' G' E' ∧ Rd_entry_d α b Q' ∧ It_map_d G' k α j ∧
      Rd_entry_d ξ p E' ∧ Rd_entry_d ξ ρ L' := by
  classical
  obtain ⟨β, U, Q', G', E', tree, extension, hb, hj, hp, _⟩ :=
    it_apply_l hZF active h.tree hα hc hd source
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have old i q (hq : Rd_entry_d i q E) : M.mem i ξ := by
    obtain ⟨m, hm, sm⟩ := (h.tree.move_domain i).mp ⟨q, hq⟩
    rcases (hα m).mp hm with hm | eq
    · exact (h.tree.diagram.order.ordinal.mem hα.predecessor_mem).transitive m hm i sm.predecessor_mem
    · exact (hZF.1.eq_of_same_members m ξ eq) ▸ sm.predecessor_mem
  have fresh q (hq : Rd_entry_d ξ q L) : False := by
    obtain ⟨p, _, _, hp, _⟩ := (h.levels ξ q).mp hq
    exact ir ξ (old ξ p hp)
  obtain ⟨L', lf, ls⟩ := it_move_push_l (ZF.modelsKP hZF) h.function fresh (p := ρ)
  have moves i q : Rd_entry_d i q E' ↔ Rd_entry_d i q E ∨ i = ξ ∧ q = p := by
    by_cases eq : i = ξ
    · subst i
      exact ⟨fun hq => Or.inr ⟨rfl, tree.move_function.2 ξ q p hq hp⟩,
        fun hq => hq.elim (extension.2.2.2.2.1 ξ q) (fun e => e.2.symm ▸ hp)⟩
    · exact (extension.2.2.2.2.2 i q eq).trans ⟨Or.inl, fun hh => hh.elim id (fun hh => (eq hh.1).elim)⟩
  have levels i φ : Rd_entry_d i φ L' ↔ ∃ q μ H, Rd_entry_d i q E' ∧ It_payload_d q μ φ H := by
    rw [ls]
    constructor
    · rintro (hi | ⟨rfl, rfl⟩)
      · obtain ⟨q, μ, H, hi, pay⟩ := (h.levels i φ).mp hi
        exact ⟨q, μ, H, (moves i q).mpr (Or.inl hi), pay⟩
      · exact ⟨p, κ, F, hp, payload⟩
    · rintro ⟨q, μ, H, hq, pay⟩
      rcases (moves i q).mp hq with hq | ⟨rfl, rfl⟩
      · exact Or.inl ((h.levels i φ).mpr ⟨q, μ, H, hq, pay⟩)
      · exact Or.inr ⟨rfl, (payload.unique_l pay).2.1.symm⟩
  refine ⟨β, U, Q', G', E', L', ⟨tree, lf, levels, ?_, ?_⟩,
    extension, hb, hj, hp, (ls ξ ρ).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro i q μ φ H hq pay
    rcases (moves i q).mp hq with hq | ⟨rfl, rfl⟩
    · obtain ⟨a, N, V, ha, mn, nt, strong, card⟩ := h.exactness i q μ φ H hq pay
      exact ⟨a, N, V, extension.2.2.1 i a ha, mn, nt, strong, card⟩
    · obtain ⟨rfl, rfl, rfl⟩ := payload.unique_l pay
      exact ⟨c, X, R, extension.2.2.1 i c hc, mx, xt, strength, inaccessible⟩
  · intro i m φ ψ hi hm him
    rcases (ls i φ).mp hi with hi | ⟨rfl, rfl⟩
    · rcases (ls m ψ).mp hm with hm | ⟨rfl, rfl⟩
      · exact h.increasing i m φ ψ hi hm him
      · exact above i φ hi
    · rcases (ls m ψ).mp hm with hm | ⟨rfl, rfl⟩
      · obtain ⟨q, _, _, hq, _⟩ := (h.levels m ψ).mp hm
        exact (ir _ ((h.tree.diagram.order.ordinal.mem hα.predecessor_mem).transitive m (old m q hq) _ him)).elim
      · exact (ir _ him).elim

/-- 恒等延长保存原模型与全部旧图，支撑列保持原值。 -/
theorem It_pnice_d.pad_l {ω c₀ α ξ T Q G E L : M.Domain}
    (h : It_pnice_d hZF ω c₀ α T Q G E L) (succ : M.SuccessorOf α ξ) :
    ∃ β U Q' G' E' c j, It_pnice_d hZF ω c₀ β U Q' G' E' L ∧
      It_extension_d α ξ ξ T Q G E β U Q' G' E' ∧ Rd_entry_d ξ c Q ∧ Rd_entry_d α c Q' ∧
      It_map_d G' ξ α j ∧ (∀ x y, Rd_entry_d x y j → x = y) ∧
      ∀ p, Rd_entry_d ξ p E' → ∀ x, ¬ M.mem x p := by
  classical
  obtain ⟨β, U, Q', G', E', c, j, _, tree, ext, hc, hc', edge, identity, keep, empty⟩ := it_pad_l hZF h.tree succ
  have old {i p κ ρ F} (hp : Rd_entry_d i p E') (pay : It_payload_d p κ ρ F) : Rd_entry_d i p E := by
    by_cases eq : i = ξ
    · subst i
      obtain ⟨r, ⟨u, v, _, _, pair⟩, _⟩ := pay
      exact (empty p hp u ((pair u).mpr (Or.inl rfl))).elim
    · exact (ext.2.2.2.2.2 i p eq).mp hp
  refine ⟨β, U, Q', G', E', c, j, ⟨tree, h.function, ?_, ?_, h.increasing⟩,
    ext, hc, hc', edge, identity, empty⟩
  · intro i ρ
    exact (h.levels i ρ).trans ⟨fun ⟨p, κ, F, hp, pay⟩ => ⟨p, κ, F, keep i p hp, pay⟩,
      fun ⟨p, κ, F, hp, pay⟩ => ⟨p, κ, F, old hp pay, pay⟩⟩
  · intro i p κ ρ F hp pay
    obtain ⟨a, X, R, ha, mx, xt, strong, card⟩ := h.exactness i p κ ρ F (old hp pay) pay
    exact ⟨a, X, R, ext.2.2.1 i a ha, mx, xt, strong, card⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 拥有的列图与操作三元组回拉

列的全定义域由原图反射；条目与操作码保留给定大图中的原值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem _root_.YesMetaZFC.SetTheory.Internal.Smap_d.column_l
    {ω B R b U S u π C V A A' f g : M.Domain} (hω : M.IsOmega ω)
    (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (vt : M.TransitiveSet V)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hCV : Rd_entry_d C V π) (hAA : Rd_entry_d A A' π) (hfg : Rd_entry_d f g π)
    (hf : M.mem f C) (gf : M.IsSetFunction I g) (gd : M.IsDomainOf I A' g) : Fn0_d A C f := by
  have hg := (hj.member_l I hZF hω mb mu hfg hCV).mp hf
  exact (hj.function_l hZF hω bt ut mb mu hAA hCV hfg).mpr
    (fn0_of_function_l (ZF.modelsKP hZF) ⟨gf, gd, fun i hi => by
      obtain ⟨x, hx⟩ := (gd i).mp hi
      exact ⟨x, (rd_entry_transitive_l vt hg hx).2, hx⟩⟩)

theorem _root_.YesMetaZFC.SetTheory.Internal.Smap_d.entry_preimage_l
    {ω B R b U S u π D C f g i i' y : M.Domain} (hω : M.IsOmega ω)
    (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (mb : Smem_d I b B R) (mu : Smem_d I u U S)
    (hj : Smap_d I ω b u B U π) (cb : M.MemberSubset C B) (ff : Fn0_d D C f)
    (gf : M.IsSetFunction I g) (hf : Rd_entry_d f g π) (hi : Rd_entry_d i i' π)
    (hiD : M.mem i D) (hy : Rd_entry_d i' y g) : ∃ x, M.mem x C ∧ Rd_entry_d i x f ∧ Rd_entry_d x y π := by
  obtain ⟨x, hx, hix⟩ := ff.2.1 i hiD
  obtain ⟨z, _, hxz⟩ := hj.1.1.2.2 x (cb x hx)
  have eq := gf.2 i' z y ((hj.entry_l hZF hω bt ut mb mu hi hxz hf).mp hix) hy
  exact ⟨x, hx, hix, eq ▸ hxz⟩

theorem it_payload_pull_l {ω B R b U S u π p p' κ' L' F' : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hpp : Rd_entry_d p p' π) (big : It_payload_d p' κ' L' F') :
    ∃ κ L F, It_payload_d p κ L F ∧ Rd_entry_d κ κ' π ∧ Rd_entry_d L L' π ∧ Rd_entry_d F F' π := by
  obtain ⟨r', hp, hr⟩ := big
  obtain ⟨κ, r, _, _, pair, hk, hrr⟩ := hj.kpair_preimage_l hZF hω bt ut mb mu hpp hp
  obtain ⟨L, F, _, _, pair', hl, hf⟩ := hj.kpair_preimage_l hZF hω bt ut mb mu hrr hr
  exact ⟨κ, L, F, ⟨r, pair, pair'⟩, hk, hl, hf⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 工作模型中的实际正则秩段列 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure It_cut_d (ω α Q E A D : M.Domain) : Prop where
  heights : M.IsSetFunction I A
  height_domain : M.IsDomainOf I α A
  codes : M.IsSetFunction I D
  code_domain : M.IsDomainOf I α D
  models : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smem_d I c X R ∧ M.TransitiveSet X
  ranks : ∀ i c a β X R, Rd_entry_d i c Q → Rd_entry_d i a D → Rd_entry_d i β A → Smem_d I c X R →
    ∃ V S, Smem_d I a V S ∧ M.mem V X ∧ Vr_d X β V ∧ Sc_regular_d X β ∧ M.mem ω V
  contains : ∀ i p κ ρ F a V S, Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d i a D →
    Smem_d I a V S → M.mem ρ V ∧ M.mem F V
  next : ∀ i j p κ ρ F a V S, M.SuccessorOf j i → Rd_entry_d i p E → It_payload_d p κ ρ F → Rd_entry_d j a D →
    Smem_d I a V S → M.mem ρ V

/-- 单根的实际严格正则秩段给出高度列和结构码列的原生实例。 -/
theorem it_root_cut_l {ω c X R K β V : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K X R)
    (model : Smem_d I c X R) (hV : M.mem V X) (rank : Vr_d X β V) (regular : Sc_regular_d X β)
    (hω : M.mem ω V) : ∃ z α T Q G A D a S,
      (∀ x, ¬ M.mem x z) ∧ M.SuccessorOf α z ∧ It_nice_d hZF ω c α T Q G z z ∧
      It_cut_d hZF ω α Q z A D ∧ Rd_entry_d z a D ∧ Smem_d I a V S := by
  obtain ⟨z, α, T, Q, G, hz, hα, nice⟩ := it_nice_root_l hZF (it_source_mem_l hZF model source)
  obtain ⟨a, S, code⟩ := smdl_membership_l I hZF ⟨ω, hω⟩
  obtain ⟨C, cs⟩ := KP.exists_singleton (ZF.modelsKP hZF) β
  obtain ⟨A, af, as⟩ := ZF.exists_constantFunction hZF I (source := α) ((cs β).mpr rfl)
  obtain ⟨B, bs⟩ := KP.exists_singleton (ZF.modelsKP hZF) a
  obtain ⟨D, df, ds⟩ := ZF.exists_constantFunction hZF I (source := α) ((bs a).mpr rfl)
  refine ⟨z, α, T, Q, G, A, D, a, S, hz, hα, nice, ⟨af.1, af.2.1, df.1, df.2.1, ?_, ?_, ?_, ?_⟩,
    (ds z a).mpr ⟨hα.predecessor_mem, rfl⟩, code⟩
  · intro i d hd
    have hi := (nice.tree.diagram.model_domain i).mpr ⟨d,hd⟩
    have eq := ((hα i).mp hi).elim (fun hi => (hz i hi).elim) (hZF.1.eq_of_same_members i z)
    subst i
    have eq := nice.tree.diagram.model_function.2 z d c hd (nice.tree.root z hz)
    subst d
    exact ⟨X,R,model,source.transitive⟩
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


end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际终点向前恢复有限 nice 树的隶属呈示

归纳只向已给定的实际终点回溯。活动步的所属证书给出前一节点，padding 保留
同一模型码；因此无需假定一般原关系树的活动目标本身已经坍塌。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def it_mem0_m {d} (c : Term d) : Formula 1 d := set[d] ⟪∃ X R,
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ,X,R) ∧ Trans(X)⟫
derive_free_closed it_mem0_m

private theorem it_mem0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (c : Term d) :
    Formula.satisfies ρ (it_mem0_m c) ↔ It_mem_d (kp_pair_l hKP) (c.eval ρ) := by
  simp only [it_mem0_m,It_mem_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    smem_sat_l (kp_pair_l hKP),Formula.satisfies_isTransitive_iff,Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 每个内部有限实际终点以前的节点，均由原活动所属或同码 padding 恢复。 -/
theorem It_pnice_d.models_before_l {ω c α T Q G E L n b : M.Domain}
    (nice : It_pnice_d hZF ω c α T Q G E L) (hn : M.mem n ω)
    (hb : Rd_entry_d n b Q) (model : It_mem_d I b) :
    ∀ i a, (i = n ∨ M.mem i n) → Rd_entry_d i a Q → It_mem_d I a := by
  let ρ : Env M 2 := ⟨Fin.cases Q (fun _ => α),fun _ => α⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪
    ⌜(.newest : Term 3)⌝ₛ ∈ ⌜(.bound 2 : Term 3)⌝ₛ → ∀ b,
      ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 3)⌝ₛ,b,⌜(.bound 1 : Term 3)⌝ₛ) → ⌜it_mem0_m⌝ₚ(b) →
      ∀ i a, (i = ⌜(.newest : Term 3)⌝ₛ ∨ i ∈ ⌜(.newest : Term 3)⌝ₛ) →
        ⌜rd_entry0_m⌝ₚ(i,a,⌜(.bound 1 : Term 3)⌝ₛ) → ⌜it_mem0_m⌝ₚ(a)⟫ }
  have sat m : φ.denote ρ m ↔ M.mem m α → ∀ b, Rd_entry_d m b Q → It_mem_d I b →
      ∀ i a, (i = m ∨ M.mem i m) → Rd_entry_d i a Q → It_mem_d I a := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff,Formula.satisfies_disj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      rd_entry0_sat_l hZF.1,it_mem0_sat_l (ZF.modelsKP hZF),Definitional.Term.eval_weaken]; rfl
  have all : ∀ m, M.mem m ω → M.mem m α → ∀ b, Rd_entry_d m b Q → It_mem_d I b →
      ∀ i a, (i = m ∨ M.mem i m) → Rd_entry_d i a Q → It_mem_d I a := by
    apply nice.tree.omega.induction
    · obtain ⟨D,ds⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨D,fun m => (ds m).trans (and_congr_right fun _ => sat m)⟩
    · intro m empty _ b hb mb i a bound ha
      rcases bound with eq | hi
      · subst i
        exact (nice.tree.diagram.model_function.2 m a b ha hb).symm ▸ mb
      · exact (empty i hi).elim
    · intro m hm ih s succ hs b hb mb
      obtain ⟨k,d,a,e,f,p,_,hd,_,he,_,hp,step⟩ := nice.tree.steps m s hs succ
      have before : It_mem_d I d := by
        rcases step with ⟨_,_,same,_⟩ | ⟨κ,ℓ,F,_,_,_,_,pay,_⟩
        · exact same ▸ (nice.tree.diagram.model_function.2 s e b he hb).symm ▸ mb
        · obtain ⟨d',X,R,hd',mx,xt,_⟩ := nice.exactness m p κ ℓ F hp pay
          exact nice.tree.diagram.model_function.2 m d' d hd' hd ▸ ⟨X,R,mx,xt⟩
      intro i a bound ha
      rcases bound with eq | hi
      · subst i
        exact (nice.tree.diagram.model_function.2 s a b ha hb).symm ▸ mb
      · apply ih (nice.tree.diagram.order.ordinal.transitive s hs m succ.predecessor_mem) d hd before i a
        · exact ((succ i).mp hi).elim Or.inr (fun eq => Or.inl (hZF.1.eq_of_same_members i m eq))
        · exact ha
  exact all n hn ((nice.tree.diagram.model_domain n).mpr ⟨b,hb⟩) b hb model

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原树延伸保持旧图及支撑列

四张树图的保持只用原树和实际延伸。支撑列另由操作载荷回读，不需要原树的nice假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem It_tree_d.extension_keep_l {ω c α T Q G E β T' Q' G' E' ξ k : M.Domain}
    (h : It_tree_d hZF ω c α T Q G E) (e : It_extension_d α ξ k T Q G E β T' Q' G' E') :
    (∀ i j, M.mem j α → (Rd_entry_d i j T' ↔ Rd_entry_d i j T)) ∧
    M.MemberSubset T T' ∧ M.MemberSubset Q Q' ∧ M.MemberSubset G G' ∧ M.MemberSubset E E' := by
  have sub {A B : M.Domain} (rel : ∀ p, M.mem p A → ∃ i j, KPair_d M p i j)
      (keep : ∀ i j, Rd_entry_d i j A → Rd_entry_d i j B) : M.MemberSubset A B := by
    intro p hp
    obtain ⟨i,j,pair⟩ := rel p hp
    obtain ⟨q,qp,hq⟩ := keep i j ⟨p,pair,hp⟩
    exact kpair_unique_l M hZF.1 qp pair ▸ hq
  refine ⟨fun i j hj => (e.2.1 i j).trans ⟨fun h => h.elim id (fun ⟨eq,_⟩ =>
    (KP.mem_irrefl_d (ZF.modelsKP hZF) α (eq ▸ hj)).elim),Or.inl⟩,
    sub h.diagram.order.relation (fun i j hij => (e.2.1 i j).mpr (Or.inl hij)),
    sub h.diagram.model_function.1 e.2.2.1,sub h.diagram.map_function.1 ?_,
    sub h.move_function.1 e.2.2.2.2.1⟩
  intro r f hr
  obtain ⟨i,j,pair⟩ := h.diagram.order.relation r ((h.diagram.map_domain r).mpr ⟨f,hr⟩)
  obtain ⟨r',pair',hf⟩ := (e.2.2.2.1 i j f (h.diagram.order.bound i j
    ⟨r,pair,(h.diagram.map_domain r).mpr ⟨f,hr⟩⟩).2).mpr ⟨r,pair,hr⟩
  exact kpair_unique_l M hZF.1 pair' pair ▸ hf

theorem it_levels_subset_l (hE : Extensional M) {E E' L L' : M.Domain}
    (rel : ∀ p, M.mem p L → ∃ i l, KPair_d M p i l)
    (old : ∀ i l, Rd_entry_d i l L → ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ l F)
    (next : ∀ i l, (∃ p κ F, Rd_entry_d i p E' ∧ It_payload_d p κ l F) → Rd_entry_d i l L')
    (keep : M.MemberSubset E E') : M.MemberSubset L L' := by
  intro p hp
  obtain ⟨i,l,pair⟩ := rel p hp
  obtain ⟨q,κ,F,⟨r,rp,hr⟩,payload⟩ := old i l ⟨p,pair,hp⟩
  obtain ⟨p',pc,hp'⟩ := next i l ⟨q,κ,F,⟨r,rp,keep r hr⟩,payload⟩
  exact kpair_unique_l M hE pc pair ▸ hp'

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限树框架及其记录之间的保持关系

框架只读取前十四个数学坐标。记录的其余坐标由实际索引映射保留，
同一证明同时用于旧记录和完整75项原关系状态。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_tree_keep_d (v w : Fin 14 → M.Domain) : Prop :=
  M.MemberSubset (v 6) (w 6) ∧
  (∀ i j, M.mem j (v 6) → (Rd_entry_d i j (w 8) ↔ Rd_entry_d i j (v 8))) ∧
  (∀ a : Fin 6, M.MemberSubset (v ⟨8+a.val,by omega⟩) (w ⟨8+a.val,by omega⟩)) ∧
  ∀ i, Rd_entry_d i (v 7) (v 8) → Rd_entry_d i (w 7) (w 8)

def tg_tree_keep_m {d} (v w : Fin 14 → Term d) : Formula 1 d :=
  .conj (Formula.subset (v 6) (w 6)) (.conj
    (set[d] ⟪∀ i j, j ∈ ⌜v 6⌝ₛ → (⌜rd_entry0_m⌝ₚ(i,j,⌜w 8⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(i,j,⌜v 8⌝ₛ))⟫)
    (.conj (rb_conj_m (fun a : Fin 6 => Formula.subset (v ⟨8+a.val,by omega⟩) (w ⟨8+a.val,by omega⟩)))
      (set[d] ⟪∀ i, ⌜rd_entry0_m⌝ₚ(i,⌜v 7⌝ₛ,⌜v 8⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i,⌜w 7⌝ₛ,⌜w 8⌝ₛ)⟫)))

@[simp] theorem tg_tree_keep_closed_l {d} (v w : Fin 14 → Term d)
    (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = []) : (tg_tree_keep_m v w).FreeClosed := by
  simp -implicitDefEqProofs [tg_tree_keep_m,Definitional.Formula.FreeClosed,hv,hw]

theorem tg_tree_keep_sat_l (hE : Extensional M) {d} (η : Env M d) (v w : Fin 14 → Term d) :
    Formula.satisfies η (tg_tree_keep_m v w) ↔ Tg_tree_keep_d (fun i => (v i).eval η) (fun i => (w i).eval η) := by
  simp only [tg_tree_keep_m,Tg_tree_keep_d,Formula.satisfies_conj_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_iff_iff,rd_entry0_sat_l hE,rb_conj_sat_l,Definitional.Term.eval_weaken]
  rfl

theorem Tg_tree_keep_d.refl_l (v : Fin 14 → M.Domain) : Tg_tree_keep_d v v :=
  ⟨fun _ h => h,fun _ _ _ => Iff.rfl,fun _ _ h => h,fun _ h => h⟩

theorem Tg_tree_keep_d.trans_l {v w z : Fin 14 → M.Domain} (h : Tg_tree_keep_d v w) (g : Tg_tree_keep_d w z) :
    Tg_tree_keep_d v z := ⟨fun x hx => g.1 x (h.1 x hx),
  fun i j hj => (g.2.1 i j (h.1 j hj)).trans (h.2.1 i j hj),
  fun a x hx => g.2.2.1 a x (h.2.2.1 a x hx),fun i hi => g.2.2.2 i (h.2.2.2 i hi)⟩

def Tg_run_keep_d {n} (idx : Fin 14 → Fin (n+1)) (s t : M.Domain) : Prop := ∃ v w : Fin (n+1) → M.Domain,
  Rt_tuple_d v s ∧ Rt_tuple_d w t ∧ Tg_tree_keep_d (fun i => v (idx i)) (fun i => w (idx i))

def tg_run_keep_m {d n} (idx : Fin 14 → Fin (n+1)) (s t : Term d) : Formula 1 d :=
  let e : Term d → Term ((n+1)+d) := fun x => x.rename (Fin.natAdd (n+1))
  let f : Term ((n+1)+d) → Term ((n+1)+((n+1)+d)) := fun x => x.rename (Fin.natAdd (n+1))
  let v : Fin (n+1) → Term ((n+1)+((n+1)+d)) := fun i => f (.bound (i.castAdd d))
  let w : Fin (n+1) → Term ((n+1)+((n+1)+d)) := fun i => .bound (i.castAdd ((n+1)+d))
  rb_exists_m (n := n+1) (rb_exists_m (n := n+1) (.conj (rt_tuple_m v (f (e s)))
    (.conj (rt_tuple_m w (f (e t))) (tg_tree_keep_m (fun i => v (idx i)) (fun i => w (idx i))))))

@[simp] theorem tg_run_keep_closed_l {d n} (idx : Fin 14 → Fin (n+1)) (s t : Term d)
    (hs : s.freeSupport = []) (ht : t.freeSupport = []) : (tg_run_keep_m idx s t).FreeClosed := by
  simp -implicitDefEqProofs [tg_run_keep_m,Definitional.Formula.FreeClosed]
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs),
    rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using ht)⟩

theorem tg_run_keep_sat_l (hE : Extensional M) {d n} (η : Env M d) (idx : Fin 14 → Fin (n+1)) (s t : Term d) :
    Formula.satisfies η (tg_run_keep_m idx s t) ↔ Tg_run_keep_d idx (s.eval η) (t.eval η) := by
  simp only [tg_run_keep_m,Tg_run_keep_d,rb_exists_sat_l,Formula.satisfies_conj_iff,rt_tuple_sat_l hE,
    tg_tree_keep_sat_l hE,Definitional.Term.eval_rename,Env.reindex,Function.comp_def,
    Term.eval_bound,Fin.addCases_left,Fin.addCases_right]

theorem Tg_run_keep_d.trans_l {n} {idx : Fin 14 → Fin (n+1)} {s t u : M.Domain}
    (h : Tg_run_keep_d idx s t) (g : Tg_run_keep_d idx t u) : Tg_run_keep_d idx s u := by
  obtain ⟨v,w,vs,wt,h⟩ := h
  obtain ⟨w',z,wt',zu,g⟩ := g
  have eq := rt_tuple_inj_l wt' wt
  subst w'
  exact ⟨v,z,vs,zu,h.trans_l g⟩

/-- 可定义保持关系沿内部ω传播；两份记录在较晚的真实阶段共同比较。 -/
theorem Tg_run_keep_d.merge_l (hZF : M.Models ZF) {n} {idx : Fin 14 → Fin (n+1)}
    {ω D f : M.Domain} (hω : M.IsOmega ω) (hf : Fn0_d ω D f)
    (next : ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s f → Rd_entry_d j t f → Tg_run_keep_d idx s t)
    {i j s t} {v w : Fin (n+1) → M.Domain}
    (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    ∃ k r, ∃ z : Fin (n+1) → M.Domain, Rd_entry_d k r f ∧ Rt_tuple_d z r ∧
      Tg_tree_keep_d (fun a => v (idx a)) (fun a => z (idx a)) ∧
      Tg_tree_keep_d (fun a => w (idx a)) (fun a => z (idx a)) := by
  let η : Env M 0 := ⟨Fin.elim0, fun _ => f⟩
  let φ : BinarySchema 0 := { body := tg_run_keep_m idx (.bound 1) .newest }
  have sat s t : φ.denote η s t ↔ Tg_run_keep_d idx s t := tg_run_keep_sat_l hZF.1 ..
  have chain := ZF.rel_chain_l (kp_pair_l (ZF.modelsKP hZF)) hZF φ η hω (fn0_function_l (ZF.modelsKP hZF) hf)
    (fun _ _ _ _ _ _ a b => (sat _ _).mpr (((sat _ _).mp a).trans_l ((sat _ _).mp b)))
    (fun _ _ _ _ ij hs ht => (sat _ _).mpr (next _ _ _ _ ij hs ht))
  have mono {i j s t} {v w : Fin (n+1) → M.Domain} (ij : M.mem i j)
      (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) : Tg_tree_keep_d (fun i => v (idx i)) (fun i => w (idx i)) := by
    obtain ⟨v', w', ps', pt', keep⟩ := (sat _ _).mp (chain i j s t ij hs ht)
    have ev := rt_tuple_inj_l ps' ps
    have ew := rt_tuple_inj_l pt' pt
    exact ev ▸ ew ▸ keep
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i (hf.bound_l hs).1 j (hf.bound_l ht).1 with eq | ij | ji
  · have eq := hZF.1.eq_of_same_members i j eq
    subst j
    have eq := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 i t s ht hs
    subst t
    have eq := rt_tuple_inj_l pt ps
    subst w
    exact ⟨i, s, v, hs, ps, .refl_l (fun i => v (idx i)), .refl_l (fun i => v (idx i))⟩
  · exact ⟨j, t, w, ht, pt, mono ij hs ht ps pt, .refl_l (fun i => w (idx i))⟩
  · exact ⟨i, s, v, hs, ps, .refl_l (fun i => v (idx i)), mono ji ht hs pt ps⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共尾有限树框架的内部并

所有原图都来自同一实际记录列。两个阶段在共同后继比较，旧终点的完整前驱保持
使并树在每个原阶段上的限制精确恢复；工作性质不作为原树的额外前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 固定记录坐标中的集合取并；元数不限制模型内部的阶段数。 -/
def Tg_run_value_d {n} (a : Fin (n+1)) (f x : M.Domain) : Prop := ∃ v : Fin (n+1) → M.Domain,
  ∃ i s, Rd_entry_d i s f ∧ Rt_tuple_d v s ∧ M.mem x (v a)

def tg_run_value0_m {n} (a : Fin (n+1)) : Formula 1 2 :=
  let v : Fin (n+1) → Term ((n+1)+2) := fun i => .bound (i.castAdd 2)
  let f : Term ((n+1)+2) := .bound (Fin.natAdd (n+1) (0 : Fin 2))
  let x : Term ((n+1)+2) := .bound (Fin.natAdd (n+1) (1 : Fin 2))
  rb_exists_m (n := n+1) (.existsE (.existsE
    (.conj (rd_entry0_m (.bound 1) .newest f.weaken.weaken)
      (.conj (rt_tuple_m (fun i => (v i).weaken.weaken) .newest) (.mem x.weaken.weaken (v a).weaken.weaken)))))

theorem tg_run_value0_closed_l {n} (a : Fin (n+1)) : (tg_run_value0_m a).FreeClosed := by
  simp -implicitDefEqProofs [tg_run_value0_m,Definitional.Formula.FreeClosed]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

theorem tg_run_value0_sat_l (hE : Extensional M) {n} (a : Fin (n+1)) (η : Env M 2) :
    Formula.satisfies η (tg_run_value0_m a) ↔ Tg_run_value_d a (η.bound 0) (η.bound 1) := by
  simp only [tg_run_value0_m,Tg_run_value_d,rb_exists_sat_l,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,rd_entry0_sat_l hE,rt_tuple_sat_l hE,Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken,Term.eval_bound,Definitional.Term.eval_newest,
    Fin.addCases_left,Fin.addCases_right]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure It_frame_d (ω c i : M.Domain) (v : Fin 14 → M.Domain) : Prop where
  tree : It_tree_d hZF ω c (v 6) (v 8) (v 9) (v 10) (v 11)
  finite : M.mem (v 6) ω
  span : M.mem i (v 6)
  levels_function : M.IsSetFunction I (v 12)
  levels : ∀ j L, Rd_entry_d j L (v 12) ↔ ∃ p κ F, Rd_entry_d j p (v 11) ∧ It_payload_d p κ L F
  archive_function : M.IsSetFunction I (v 13)

structure It_frames_d {n} (idx : Fin 14 → Fin (n+1)) (ω c D f : M.Domain) : Prop where
  function : Fn0_d ω D f
  rows : ∀ i s, Rd_entry_d i s f → ∃ v : Fin (n+1) → M.Domain,
    Rt_tuple_d v s ∧ It_frame_d hZF ω c i (fun j => v (idx j))
  merge : ∀ i j s t (v w : Fin (n+1) → M.Domain), Rd_entry_d i s f → Rd_entry_d j t f →
    Rt_tuple_d v s → Rt_tuple_d w t → ∃ k r, ∃ z : Fin (n+1) → M.Domain,
      Rd_entry_d k r f ∧ Rt_tuple_d z r ∧ Tg_tree_keep_d (fun a => v (idx a)) (fun a => z (idx a)) ∧
        Tg_tree_keep_d (fun a => w (idx a)) (fun a => z (idx a))

variable {n : Nat} {idx : Fin 14 → Fin (n+1)}

theorem It_frames_d.read_l {ω c D f i s : M.Domain} (h : It_frames_d hZF idx ω c D f)
    (v : Fin (n+1) → M.Domain) (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) :
    It_frame_d hZF ω c i (fun j => v (idx j)) := by
  obtain ⟨w,pack,frame⟩ := h.rows i s hs
  exact rt_tuple_inj_l pack code ▸ frame

/-- 合并不会在任何旧终点之前加入新的前驱。 -/
theorem It_frames_d.order_l {ω c D f i s x y : M.Domain} {U : Fin 6 → M.Domain}
    {v : Fin (n+1) → M.Domain} (h : It_frames_d hZF idx ω c D f)
    (columns : ∀ a z, M.mem z (U a) ↔ Tg_run_value_d (idx ⟨8+a.val,by omega⟩) f z)
    (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (hy : M.mem y (v (idx 6))) :
    Rd_entry_d x y (U 0) ↔ Rd_entry_d x y (v (idx 8)) := by
  constructor
  · rintro ⟨p,pair,hp⟩
    obtain ⟨w,j,t,ht,pt,hp⟩ := (columns 0 p).mp hp
    obtain ⟨_,_,_,_,_,keep,keep'⟩ := h.merge i j s t v w hs ht code pt
    exact (keep.2.1 x y hy).mp ⟨p,pair,keep'.2.2.1 0 p hp⟩
  · rintro ⟨p,pair,hp⟩
    exact ⟨p,pair,(columns 0 p).mpr ⟨v,i,s,hs,code,hp⟩⟩

theorem It_frames_d.union_l {ω c D f : M.Domain} (h : It_frames_d hZF idx ω c D f)
    (hω : M.IsOmega ω) : ∃ U : Fin 6 → M.Domain,
    It_tree_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) ∧ M.IsSetFunction I (U 4) ∧
    (∀ i L, Rd_entry_d i L (U 4) ↔ ∃ p κ F, Rd_entry_d i p (U 3) ∧ It_payload_d p κ L F) ∧
    M.IsSetFunction I (U 5) ∧ ∀ a x, M.mem x (U a) ↔ Tg_run_value_d (idx ⟨8+a.val,by omega⟩) f x := by
  have read {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) := h.read_l hZF v hs code
  have finite {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) := (read hs code).finite
  have merge {i j s t} {v w : Fin (n+1) → M.Domain}
      (hs : Rd_entry_d i s f) (ht : Rd_entry_d j t f) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :=
    h.merge i j s t v w hs ht ps pt
  obtain ⟨B, bt, hDB, _⟩ := ZF.tc_exists_l I hZF D
  have collect (a : Fin 6) : ∃ U, ∀ x, M.mem x U ↔ Tg_run_value_d (idx ⟨8+a.val, by omega⟩) f x := by
    let ψ : UnarySchema 1 := {
      body := (tg_run_value0_m (idx ⟨8+a.val, by omega⟩)).bind (Fin.cases (.bound 1) (fun _ => .newest))
      freeClosed := (Definitional.Formula.freeClosed_bind_iff_of_closed _ (Fin.cases rfl (fun _ => rfl)) _).mpr (tg_run_value0_closed_l _) }
    let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
    have value x : ψ.denote ρ x ↔ Tg_run_value_d (idx ⟨8+a.val, by omega⟩) f x := by
      rw [UnarySchema.denote, Formula.satisfies_bind, tg_run_value0_sat_l hZF.1]; rfl
    obtain ⟨U, us⟩ := ZF.separation_exists_d hZF ψ ρ B
    refine ⟨U, fun x => (us x).trans ((and_congr_right fun _ => value x).trans ⟨And.right, fun hx => ⟨?_, hx⟩⟩)⟩
    obtain ⟨q, i, s, hs, code, hx⟩ := hx
    exact bt _ (Rt_tuple_d.members_l (v := q) code bt (bt D hDB s (h.function.bound_l hs).2) _) x hx
  obtain ⟨T, ts⟩ := collect 0
  obtain ⟨Q, qs⟩ := collect 1
  obtain ⟨G, gs⟩ := collect 2
  obtain ⟨E, es⟩ := collect 3
  obtain ⟨L, ls⟩ := collect 4
  obtain ⟨H, hs⟩ := collect 5
  let U : Fin 6 → M.Domain := Fin.cases T (Fin.cases Q (Fin.cases G (Fin.cases E (Fin.cases L (fun _ => H)))))
  have us (a : Fin 6) (x) : M.mem x (U a) ↔ Tg_run_value_d (idx ⟨8+a.val, by omega⟩) f x :=
    Fin.cases (ts x) (Fin.cases (qs x) (Fin.cases (gs x) (Fin.cases (es x)
      (Fin.cases (ls x) (Fin.cases (hs x) (fun i => Fin.elim0 i)))))) a
  have entries (a : Fin 6) (x y) : Rd_entry_d x y (U a) ↔ ∃ i s, ∃ v : Fin (n+1) → M.Domain,
      Rd_entry_d i s f ∧ Rt_tuple_d v s ∧ Rd_entry_d x y (v (idx ⟨8+a.val, by omega⟩)) := by
    refine ⟨fun ⟨p, pair, hp⟩ => ?_, fun ⟨i, s, v, hs, code, p, pair, hp⟩ => ?_⟩
    · obtain ⟨v, i, s, hs, code, hp⟩ := (us a p).mp hp
      exact ⟨i, s, v, hs, code, p, pair, hp⟩
    · exact ⟨p, pair, (us a p).mpr ⟨v, i, s, hs, code, hp⟩⟩
  have part {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (a : Fin 5) :
      M.IsSetFunction I (v (idx ⟨8+a.succ.val, by omega⟩)) := by
    have run := (read hs code)
    exact Fin.cases run.tree.diagram.model_function (Fin.cases run.tree.diagram.map_function
      (Fin.cases run.tree.move_function (Fin.cases run.levels_function
        (Fin.cases run.archive_function (fun i => Fin.elim0 i))))) a
  have functions (a : Fin 5) : M.IsSetFunction I (U a.succ) := by
    refine ⟨fun p hp => ?_, fun x y z hy hz => ?_⟩
    · obtain ⟨v, i, s, hs, code, hp⟩ := (us a.succ p).mp hp
      exact (part hs code a).1 p hp
    · obtain ⟨i, s, v, hs, ps, p, pair, hp⟩ := (entries a.succ x y).mp hy
      obtain ⟨j, t, w, ht, pt, q, qp, hq⟩ := (entries a.succ x z).mp hz
      obtain ⟨k, r, u, hr, pr, su, tu⟩ := merge hs ht ps pt
      exact (part hr pr a).2 x y z ⟨p, pair, su.2.2.1 a.succ p hp⟩ ⟨q, qp, tu.2.2.1 a.succ q hq⟩
  have inside {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (a : Fin 6) :
      M.MemberSubset (v (idx ⟨8+a.val, by omega⟩)) (U a) := fun x hx => (us a x).mpr ⟨v, i, s, hs, code, hx⟩
  have keeps {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s) (a : Fin 6)
      {x y} (xy : Rd_entry_d x y (v (idx ⟨8+a.val, by omega⟩))) : Rd_entry_d x y (U a) :=
    (entries a x y).mpr ⟨i, s, v, hs, code, xy⟩
  have orderOld {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      {x y} (hy : M.mem y (v (idx 6))) : Rd_entry_d x y (U 0) ↔ Rd_entry_d x y (v (idx 8)) :=
    h.order_l hZF us hs code hy
  have bound {i j} (ij : Rd_entry_d i j (U 0)) : M.mem i ω ∧ M.mem j ω := by
    obtain ⟨k, s, v, hs, code, ij⟩ := (entries 0 i j).mp ij
    have bounds := (read hs code).tree.diagram.order.bound i j ij
    exact ⟨hω.transitive (ZF.modelsKP hZF) _ (finite hs code) i bounds.1, hω.transitive (ZF.modelsKP hZF) _ (finite hs code) j bounds.2⟩
  have stage (i) (hi : M.mem i ω) : ∃ s, ∃ v : Fin (n+1) → M.Domain, Rd_entry_d i s f ∧ Rt_tuple_d v s := by
    obtain ⟨s, _, hs⟩ := h.function.2.1 i hi
    obtain ⟨v, code, _⟩ := h.rows i s hs
    exact ⟨s, v, hs, code⟩
  -- 以下只在包含终点的旧阶段核验序、模型、箭头与扩展器。
  have order : It_order_d ω (U 0) := by
    refine ⟨hω.isOrdinal (ZF.modelsKP hZF), ?_, fun _ _ ij => bound ij, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨v, i, s, hs, code, hp⟩ := (us 0 p).mp hp
      exact (read hs code).tree.diagram.order.relation p hp
    · intro i hi
      obtain ⟨s, v, hs, code⟩ := stage i hi
      exact keeps hs code 0 ((read hs code).tree.diagram.order.refl i (read hs code).span)
    · intro i j k ij jk
      obtain ⟨s, v, hs, code⟩ := stage k (bound jk).2
      have st := (read hs code).tree.diagram.order
      have jk' := (orderOld hs code (read hs code).span).mp jk
      exact (orderOld hs code (read hs code).span).mpr (st.trans i j k
        ((orderOld hs code (st.bound j k jk').1).mp ij) jk')
    · intro i j ij
      obtain ⟨k, s, v, hs, code, ij⟩ := (entries 0 i j).mp ij
      exact (read hs code).tree.diagram.order.forward i j ij
    · intro i j k ik jk
      obtain ⟨s, v, hs, code⟩ := stage k (bound ik).2
      exact ((read hs code).tree.diagram.order.chain i j k
        ((orderOld hs code (read hs code).span).mp ik) ((orderOld hs code (read hs code).span).mp jk)).imp
          (keeps hs code 0) (keeps hs code 0)
    · intro i j hj succ
      obtain ⟨s, v, hs, code⟩ := stage j hj
      have st := (read hs code).tree.diagram.order
      obtain ⟨k, kj, pred⟩ := st.predecessor i j (read hs code).span succ
      exact ⟨k, kj, fun l => (orderOld hs code (read hs code).span).trans
        ((pred l).trans (or_congr Iff.rfl (orderOld hs code (st.ordinal.transitive j (read hs code).span k kj)).symm))⟩
    · intro δ hd limit
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) δ (hω.subset_limitOrdinal (ZF.modelsKP hZF) limit δ hd)).elim
  have qdom : M.IsDomainOf I ω (U 1) := by
    intro i
    refine ⟨fun hi => ?_, fun ⟨a, ha⟩ => ?_⟩
    · obtain ⟨s, v, hs, code⟩ := stage i hi
      obtain ⟨a, ha⟩ := ((read hs code).tree.diagram.model_domain i).mp (read hs code).span
      exact ⟨a, keeps hs code 1 ha⟩
    · obtain ⟨k, s, v, hs, code, ha⟩ := (entries 1 i a).mp ha
      exact hω.transitive (ZF.modelsKP hZF) _ (finite hs code) i (((read hs code).tree.diagram.model_domain i).mpr ⟨a, ha⟩)
  have oldFunction {B A X : M.Domain} (af : M.IsSetFunction I A) (bd : M.IsDomainOf I X B)
      (sub : M.MemberSubset B A) {i} (hi : M.mem i X) (x) : Rd_entry_d i x A ↔ Rd_entry_d i x B := by
    refine ⟨fun hx => ?_, fun ⟨p, pair, hp⟩ => ⟨p, pair, sub p hp⟩⟩
    obtain ⟨y, p, pair, hp⟩ := (bd i).mp hi
    exact af.2 i y x ⟨p, pair, sub p hp⟩ hx ▸ (show Rd_entry_d i y B from ⟨p, pair, hp⟩)
  have modelOld {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      {j} (hj : M.mem j (v (idx 6))) (a) : Rd_entry_d j a (U 1) ↔ Rd_entry_d j a (v (idx 9)) :=
    oldFunction (functions 0) (read hs code).tree.diagram.model_domain (inside hs code 1) hj a
  have pairMem {r i j B} (p : KPair_d M r i j) (h : Rd_entry_d i j B) : M.mem r B := by
    obtain ⟨q, qp, hq⟩ := h
    exact kpair_unique_l M hZF.1 qp p ▸ hq
  have maps i j g : It_map_d (U 2) i j g ↔ ∃ k s, ∃ v : Fin (n+1) → M.Domain,
      Rd_entry_d k s f ∧ Rt_tuple_d v s ∧ It_map_d (v (idx 10)) i j g := by
    refine ⟨fun ⟨r, pair, hr⟩ => ?_, fun ⟨k, s, v, hs, code, r, pair, hr⟩ => ?_⟩
    · obtain ⟨k, s, v, hs, code, hr⟩ := (entries 2 r g).mp hr
      exact ⟨k, s, v, hs, code, r, pair, hr⟩
    · exact ⟨r, pair, keeps hs code 2 hr⟩
  have gdom : M.IsDomainOf I (U 0) (U 2) := by
    intro r
    refine ⟨fun hr => ?_, fun ⟨g, hr⟩ => ?_⟩
    · obtain ⟨v, i, s, hs, code, hr⟩ := (us 0 r).mp hr
      obtain ⟨g, hg⟩ := ((read hs code).tree.diagram.map_domain r).mp hr
      exact ⟨g, keeps hs code 2 hg⟩
    · obtain ⟨k, s, v, hs, code, hr⟩ := (entries 2 r g).mp hr
      exact inside hs code 0 r (((read hs code).tree.diagram.map_domain r).mpr ⟨g, hr⟩)
  have mapBound {i j g} (hg : It_map_d (U 2) i j g) : Rd_entry_d i j (U 0) := by
    obtain ⟨r, pair, hr⟩ := hg
    exact ⟨r, pair, (gdom r).mpr ⟨g, hr⟩⟩
  have mapOld {i s} {v : Fin (n+1) → M.Domain} (hs : Rd_entry_d i s f) (code : Rt_tuple_d v s)
      {j k} (hk : M.mem k (v (idx 6))) (g) : It_map_d (U 2) j k g ↔ It_map_d (v (idx 10)) j k g := by
    refine ⟨fun ⟨r, pair, hr⟩ => ?_, fun hg => (maps j k g).mpr ⟨i, s, v, hs, code, hg⟩⟩
    exact ⟨r, pair, (oldFunction (functions 1) (read hs code).tree.diagram.map_domain (inside hs code 2)
      (pairMem pair ((orderOld hs code hk).mp (mapBound ⟨r, pair, hr⟩))) g).mp hr⟩
  have small {i j} {v : Fin (n+1) → M.Domain} (st : It_order_d (v (idx 6)) (v (idx 8))) (hj : M.mem j (v (idx 6)))
      (ij : Rd_entry_d i j (U 0)) : M.mem i (v (idx 6)) := (order.forward i j ij).elim (fun eq => eq.symm ▸ hj) (st.ordinal.transitive j hj i)
  have diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω (U 0) (U 1) (U 2) := by
    refine ⟨order, functions 0, qdom, ?_, functions 1, gdom, ?_, ?_, ?_⟩
    · intro i a ha
      obtain ⟨k, s, v, hs, code, ha⟩ := (entries 1 i a).mp ha
      exact (read hs code).tree.diagram.models i a ha
    · intro i j g a X R b Y S hg ha hb ma mb
      obtain ⟨s, v, hs, code⟩ := stage j (bound (mapBound hg)).2
      have st := (read hs code).tree.diagram
      exact st.elementary i j g a X R b Y S ((mapOld hs code (read hs code).span g).mp hg)
        ((modelOld hs code (small st.order (read hs code).span (mapBound hg)) a).mp ha)
        ((modelOld hs code (read hs code).span b).mp hb) ma mb
    · intro i g hg x y hxy
      obtain ⟨k, s, v, hs, code, hg⟩ := (maps i i g).mp hg
      exact (read hs code).tree.diagram.identity i g hg x y hxy
    · intro i j k a b d ha hb hd x y z hxy hyz
      obtain ⟨s, v, hs, code⟩ := stage k (bound (mapBound hb)).2
      have st := (read hs code).tree.diagram
      exact st.comp i j k a b d ((mapOld hs code (small st.order (read hs code).span (mapBound hb)) a).mp ha)
        ((mapOld hs code (read hs code).span b).mp hb) ((mapOld hs code (read hs code).span d).mp hd) x y z hxy hyz
  have sources i a (ha : Rd_entry_d i a (U 1)) : It_source_d hZF ω a := by
    obtain ⟨k, s, v, hs, code, ha⟩ := (entries 1 i a).mp ha
    exact (read hs code).tree.sources i a ha
  have edom i : (∃ p, Rd_entry_d i p (U 3)) ↔ ∃ j, M.mem j ω ∧ M.SuccessorOf j i := by
    refine ⟨fun ⟨p, hp⟩ => ?_, fun ⟨j, hj, succ⟩ => ?_⟩
    · obtain ⟨k, s, v, hs, code, hp⟩ := (entries 3 i p).mp hp
      obtain ⟨j, hj, succ⟩ := ((read hs code).tree.move_domain i).mp ⟨p, hp⟩
      exact ⟨j, hω.transitive (ZF.modelsKP hZF) _ (finite hs code) j hj, succ⟩
    · obtain ⟨s, v, hs, code⟩ := stage j hj
      obtain ⟨p, hp⟩ := ((read hs code).tree.move_domain i).mpr ⟨j, (read hs code).span, succ⟩
      exact ⟨p, keeps hs code 3 hp⟩
  have tree : It_tree_d hZF ω c ω (U 0) (U 1) (U 2) (U 3) := by
    refine {
      omega := hω
      diagram := diagram
      root := ?_
      move_function := functions 2
      move_domain := edom
      steps := ?_
      limits := ?_
      sources := sources }
    · intro e he
      obtain ⟨s, v, hs, code⟩ := stage e (num_mem_l hZF.1 hω (show Num_d 0 e from he))
      exact keeps hs code 1 ((read hs code).tree.root e he)
    · intro i j hj succ
      obtain ⟨s, v, hs, code⟩ := stage j hj
      have st := (read hs code).tree
      obtain ⟨k, a, b, d, g, p, ⟨kj, pred⟩, ha, hb, hd, hg, hp, step⟩ := st.steps i j (read hs code).span succ
      refine ⟨k, a, b, d, g, p, ⟨kj, fun l => (orderOld hs code (read hs code).span).trans
        ((pred l).trans (or_congr Iff.rfl (orderOld hs code (st.diagram.order.ordinal.transitive j (read hs code).span k kj)).symm))⟩,
        keeps hs code 1 ha, keeps hs code 1 hb, keeps hs code 1 hd, (maps k j g).mpr ⟨j, s, v, hs, code, hg⟩,
        keeps hs code 3 hp, step⟩
    · intro δ hd limit
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) δ (hω.subset_limitOrdinal (ZF.modelsKP hZF) limit δ hd)).elim
  have levels i ρ : Rd_entry_d i ρ (U 4) ↔ ∃ p κ F, Rd_entry_d i p (U 3) ∧ It_payload_d p κ ρ F := by
    refine ⟨fun hi => ?_, fun ⟨p, κ, F, hp, payload⟩ => ?_⟩
    · obtain ⟨k, s, v, hs, code, hi⟩ := (entries 4 i ρ).mp hi
      obtain ⟨p, κ, F, hp, payload⟩ := ((read hs code).levels i ρ).mp hi
      exact ⟨p, κ, F, keeps hs code 3 hp, payload⟩
    · obtain ⟨k, s, v, hs, code, hp⟩ := (entries 3 i p).mp hp
      exact keeps hs code 4 (((read hs code).levels i ρ).mpr ⟨p, κ, F, hp, payload⟩)
  exact ⟨U,tree,functions 3,levels,functions 4,us⟩

end YesMetaZFC.SetTheory.LargeCardinal

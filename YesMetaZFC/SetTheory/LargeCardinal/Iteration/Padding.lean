import YesMetaZFC.SetTheory.LargeCardinal.Iteration.LimitDiagram
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.ReturnFactor
import YesMetaZFC.Model.SetTheory.DirectedSystem.Isomorphism

/-! # 极限处的迭代树扩张

新顶点的严格前驱恰是指定共尾树枝；旧模型、嵌入、扩展器操作与极限
条件逐项保留。当前长度是极限，故本次不添加扩展器或 pad 操作。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem it_tree_limit_l {ω c₀ α T Q G E B d N W P : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hl : M.IsLimitOrdinal α) (b : It_branch_d α T B)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P) (source : It_source_d hZF ω d) :
    ∃ β U Q' G', M.SuccessorOf β α ∧ It_tree_d hZF ω c₀ β U Q' G' E ∧
      (∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B)) ∧
      (∀ i c, Rd_entry_d i c Q' ↔ Rd_entry_d i c Q ∨ i = α ∧ c = d) ∧
      (∀ i j f, M.mem j α → (It_map_d G' i j f ↔ It_map_d G i j f)) ∧
      ∀ i f, M.mem i α → (It_map_d G' i α f ↔ Rd_entry_d i f P) := by
  have h := tree.diagram
  have no : ¬ M.mem α α := fun ha => h.order.ordinal.wellOrder.linear.irrefl α ha ha
  obtain ⟨β, U, Q', G', e, hβ, diagram, us, qs, gs⟩ := it_limit_diagram_l hZF tree.omega h hl b cone
  have older i (hi : M.mem i β) : M.mem i α ∨ i = α := ((hβ i).mp hi).imp id (hZF.1.eq_of_same_members i α)
  have old i j (hj : M.mem j α) : Rd_entry_d i j U ↔ Rd_entry_d i j T := (us i j).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have qold i c (hi : M.mem i α) : Rd_entry_d i c Q' ↔ Rd_entry_d i c Q := (qs i c).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have gold i j f (hj : M.mem j α) : It_map_d G' i j f ↔ It_map_d G i j f := (gs i j f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hj)).elim), Or.inl⟩
  have gtip i f (hi : M.mem i α) : It_map_d G' i α f ↔ Rd_entry_d i f P := (gs i α f).trans
    ⟨fun hh => hh.elim (fun hh => (no (h.order.bound i α (h.map_bound_l hZF hh)).2).elim)
      (fun hh => hh.2.elim (fun hh => (no (hh.1 ▸ hi)).elim) id), fun hh => Or.inr ⟨rfl, Or.inr hh⟩⟩
  have successor_old i j (hj : M.mem j β) (hs : M.SuccessorOf j i) : M.mem j α := by
    rcases older j hj with hj | rfl
    · exact hj
    · exact (it_successor_not_limit_l hZF.1 (h.order.ordinal.mem hs.predecessor_mem) hs hl).elim
  have domain i : (∃ p, Rd_entry_d i p E) ↔ ∃ j, M.mem j β ∧ M.SuccessorOf j i := (tree.move_domain i).trans
    ⟨fun ⟨j, hj, hs⟩ => ⟨j, (hβ j).mpr (Or.inl hj), hs⟩,
      fun ⟨j, hj, hs⟩ => ⟨j, successor_old i j hj hs, hs⟩⟩
  have steps i j (hj : M.mem j β) (hs : M.SuccessorOf j i) : It_step_d hZF ω U Q' G' E i j := by
    have hjα := successor_old i j hj hs
    obtain ⟨k, c, d, a, f, p, ⟨hkj, pred⟩, hc, hd, ha, hf, hp, valid⟩ := tree.steps i j hjα hs
    have hk := h.order.ordinal.transitive j hjα k hkj
    exact ⟨k, c, d, a, f, p, ⟨hkj, fun l => (old l j hjα).trans ((pred l).trans (or_congr Iff.rfl (old l k hk).symm))⟩,
      (qs i c).mpr (Or.inl hc), (qs k d).mpr (Or.inl hd), (qs j a).mpr (Or.inl ha),
      (gold k j f hjα).mpr hf, hp, valid⟩
  have limits δ (hδ : M.mem δ β) (limit : M.IsLimitOrdinal δ) : It_limit_d U Q' G' δ := by
    intro c X R hc hp y hy
    rcases older δ hδ with hδα | rfl
    · obtain ⟨i, hi, hiδ, f, hf, x, hxy⟩ := tree.limits δ hδα limit c X R ((qold δ c hδα).mp hc) hp y hy
      exact ⟨i, hi, (old i δ hδα).mpr hiδ, f, (gold i δ f hδα).mpr hf, x, hxy⟩
    · have eq : c = d := ((qs _ c).mp hc).elim
        (fun hh => (no ((h.model_domain _).mpr ⟨c, hh⟩)).elim) And.right
      subst c
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp cone.model.1
      obtain ⟨i, f, x, hf, hxy⟩ := cone.cover y hy
      have hiB := (cone.domain i).mpr ⟨f, hf⟩
      exact ⟨i, b.subset i hiB, (us i _).mpr (Or.inr ⟨rfl, Or.inr hiB⟩), f,
        (gtip i f (b.subset i hiB)).mpr hf, x, hxy⟩
  exact ⟨β, U, Q', G', hβ,
    { omega := tree.omega, diagram := diagram
      root := fun z hz => (qs z c₀).mpr (Or.inl (tree.root z hz))
      move_function := tree.move_function, move_domain := domain, steps := steps, limits := limits
      sources := fun i c hc => ((qs i c).mp hc).elim (tree.sources i c) (fun hh => hh.2.symm ▸ source) },
    us, qs, gold, gtip⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意原关系模型上的真实恒等填充核心

常模型、恒等嵌入及空操作直接作为背景集合图构造。整个论证只读取
背景时间序数与给定原模型，不要求原模型的自然数对象正确，也不附加
完整数字图或源求值证书。所有后继及极限条件均由实际常图方程验证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意非空序数长度的常模型 pad 树；每个操作都是真实空集。 -/
theorem it_padding_core_l {ω c X R α : M.Domain}
    (hw : M.IsOmega ω) (code : Smdl_d I c X R) (ho : M.IsOrdinal α) (ne : ∃ i, M.mem i α) :
    ∃ T Q G E P, It_tree_core_d hZF ω c α T Q G E ∧ It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω α Q G c X R P ∧
      (∀ i p, Rd_entry_d i p E → ∀ x, ¬ M.mem x p) ∧
      (∀ i j, Rd_entry_d i j T ↔ M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j)) := by
  obtain ⟨T, order, ts, pred⟩ := it_linear_order_l (ZF.modelsKP hZF) ho
  obtain ⟨C, hc⟩ := KP.exists_singleton (ZF.modelsKP hZF) c
  obtain ⟨Q, qf, qs⟩ := ZF.exists_constantFunction hZF I (source := α) ((hc c).mpr rfl)
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (c := c) (X := X) hw
  obtain ⟨D, hd⟩ := KP.exists_singleton (ZF.modelsKP hZF) e
  obtain ⟨G, gf, gs⟩ := ZF.exists_constantFunction hZF I (source := T) ((hd e).mpr rfl)
  obtain ⟨P, pf, ps⟩ := ZF.exists_constantFunction hZF I (source := α) ((hd e).mpr rfl)
  have maps i j f : It_map_d G i j f ↔ Rd_entry_d i j T ∧ f = e := by
    constructor
    · rintro ⟨r, hr, hrf⟩
      obtain ⟨hrT, eq⟩ := (gs r f).mp hrf
      exact ⟨⟨r, hr, hrT⟩, eq⟩
    · rintro ⟨⟨r, hr, hrT⟩, rfl⟩
      exact ⟨r, hr, (gs r _).mpr ⟨hrT, rfl⟩⟩
  have typed i b Y S (hb : Rd_entry_d i b Q) (my : Smdl_d I b Y S) : b = c ∧ Y = X := by
    have eq := ((qs i b).mp hb).2
    exact ⟨eq, (smdl_unique_l I (eq ▸ my) code).1⟩
  have ident f (hf : f = e) x y (hxy : Rd_entry_d x y f) : x = y := ((es x y).mp (hf ▸ hxy)).2
  have elem i f b Y S (hf : f = e) (hb : Rd_entry_d i b Q) (my : Smdl_d I b Y S) : Smap_d I ω b c Y X f := by
    obtain ⟨rfl, rfl⟩ := typed i b Y S hb my
    exact hf.symm ▸ he
  have diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G := by
    refine ⟨order, qf.1, qf.2.1,
      fun i b hb => ((qs i b).mp hb).2.symm ▸ ⟨X, R, code⟩, gf.1, gf.2.1, ?_,
      fun i f hf => ident f ((maps i i f).mp hf).2, ?_⟩
    · intro i j f b Y S d Z V hf hb hd my mz
      obtain ⟨rfl, rfl⟩ := typed j d Z V hd mz
      exact elem i f b Y S ((maps i j f).mp hf).2 hb my
    · intro i j k f g v hf hg hv x y z hxy hyz
      have eq := ((maps j k g).mp hg).2.trans ((maps i k v).mp hv).2.symm
      exact eq ▸ (ident f ((maps i j f).mp hf).2 x y hxy).symm ▸ hyz
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  let φ : UnarySchema 1 := { body := Formula.existsMem (.bound 1) (Formula.isSuccessor .newest (.bound 1)) }
  obtain ⟨J, js⟩ := ZF.separation_exists_d hZF φ ⟨fun _ => α, fun _ => α⟩ α
  have indices i : M.mem i J ↔ ∃ j, M.mem j α ∧ M.SuccessorOf j i := by
    have sat : φ.denote ⟨fun _ => α, fun _ => α⟩ i ↔ ∃ j, M.mem j α ∧ M.SuccessorOf j i := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_isSuccessor_iff]; rfl
    exact (js i).trans ((and_congr_right fun _ => sat).trans ⟨And.right,
      fun ⟨j, hj, hs⟩ => ⟨ho.transitive j hj i hs.predecessor_mem, j, hj, hs⟩⟩)
  obtain ⟨Z, hZ⟩ := KP.exists_singleton (ZF.modelsKP hZF) z
  obtain ⟨E, ef, es'⟩ := ZF.exists_constantFunction hZF I (source := J) ((hZ z).mpr rfl)
  have tree : It_tree_core_d hZF ω c α T Q G E := by
    refine {
      omega := hw
      diagram := diagram
      root := fun o hzero => (qs o c).mpr ⟨ho.empty_mem_of_nonempty (ZF.modelsKP hZF) ne hzero, rfl⟩
      move_function := ef.1
      move_domain := fun i => (ef.2.1 i).symm.trans (indices i)
      steps := ?_
      limits := ?_ }
    · intro i j hj hs
      have hi := ho.transitive j hj i hs.predecessor_mem
      exact ⟨i, c, c, c, e, z, pred i j hj hs, (qs i c).mpr ⟨hi, rfl⟩, (qs i c).mpr ⟨hi, rfl⟩,
        (qs j c).mpr ⟨hj, rfl⟩, (maps i j e).mpr ⟨(ts i j).mpr ⟨hi, hj, Or.inr hs.predecessor_mem⟩, rfl⟩,
        (es' i z).mpr ⟨(indices i).mpr ⟨j, hj, hs⟩, rfl⟩, Or.inl ⟨hz, rfl, rfl, ident e rfl⟩⟩
    · intro δ hδ hl b Y S hb hp y hy
      have eq := ((qs δ b).mp hb).2
      subst b
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp code.1
      obtain ⟨i, hi⟩ := hl.2.1
      have hiα := ho.transitive δ hδ i hi
      have hiδ := (ts i δ).mpr ⟨hiα, hδ, Or.inr hi⟩
      exact ⟨i, hi, hiδ, e, (maps i δ e).mpr ⟨hiδ, rfl⟩, y, (es y y).mpr ⟨hy, rfl⟩⟩
  have cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω α Q G c X R P := by
    refine ⟨⟨code, pf.1, pf.2.1,
      fun i f b Y S hf => elem i f b Y S ((ps i f).mp hf).2, ?_⟩, ?_⟩
    · intro i j f u v hf hu hv x y z hxy hyz
      have eq := ((ps j v).mp hv).2.trans ((ps i u).mp hu).2.symm
      exact eq ▸ (ident f ((maps i j f).mp hf).2 x y hxy).symm ▸ hyz
    · intro x hx
      obtain ⟨i, hi⟩ := ne
      exact ⟨i, e, x, (ps i e).mpr ⟨hi, rfl⟩, (es x x).mpr ⟨hx, rfl⟩⟩
  exact ⟨T,Q,G,E,P,tree,cone,fun i p hp x hx => hz x (((es' i p).mp hp).2 ▸ hx),ts⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从良基共尾树枝自动完成极限扩张

输出保留同一个带标号系统，坍塌后的新结点仍带有它的实际直接极限证书。
非可数共尾度与相容良基实现两种入口直接构造证书，再调用同一添枝定理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure It_limit_extension_d (hZF : M.Models ZF) (ω c₀ α T Q G E B β U Q' G' : M.Domain) : Prop where
  successor : M.SuccessorOf β α
  tree : It_tree_d hZF ω c₀ β U Q' G' E
  order : ∀ i j, Rd_entry_d i j U ↔ Rd_entry_d i j T ∨ j = α ∧ (i = α ∨ M.mem i B)
  old_maps : ∀ i j f, M.mem j α → (It_map_d G' i j f ↔ It_map_d G i j f)
  limit : ∃ L A p H R r d N W P,
    (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
    It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N W ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N W ∧ M.TransitiveSet N ∧ It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G d N W P ∧
    (∀ i c, Rd_entry_d i c Q' ↔ Rd_entry_d i c Q ∨ i = α ∧ c = d) ∧
    ∀ i f, M.mem i α → (It_map_d G' i α f ↔ Rd_entry_d i f P)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_wf_branch_extend_l {ω c₀ α T Q G E B : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (hl : M.IsLimitOrdinal α) (built : It_wf_branch_d hZF ω α T Q G B) :
    ∃ β U Q' G', It_limit_extension_d hZF ω c₀ α T Q G E B β U Q' G' := by
  obtain ⟨b, L, A, p, H, R, q, c, C, V, ls, s, elem, limit, model, wf⟩ := built
  obtain ⟨k, hk⟩ := hl.2.1
  obtain ⟨i, hi, _⟩ := b.cofinal k hk
  obtain ⟨a, X, S, ha, mx⟩ := tree.diagram.model_l hZF (b.subset i hi)
  have source := tree.sources i a ha
  obtain ⟨d, N, W, P, e, r, cone, ready, target, nt, _, bij, he, hr, rs, _⟩ :=
    it_limit_model_l hZF tree.diagram b.subset s elem limit model wf hi ha mx source
  have next_limit := di_limit_iso_l (ZF.modelsKP hZF) limit bij hr rs target.1.2.2
    (fun _ _ _ _ hx hy => he.relation_l I hZF tree.omega model target.1 hx hy)
  obtain ⟨β, U, Q', G', hβ, next, us, qs, old, tips⟩ := it_tree_limit_l hZF tree hl b cone ready
  exact ⟨β, U, Q', G', hβ, next, us, old, L, A, p, H, R, r, d, N, W, P, ls, s, next_limit, target, nt, cone, qs, tips⟩

/-- 非可数共尾度入口只读取枝上各分量已有的实际良基证书。 -/
theorem it_sigma_extend_l {ω c₀ α κ T Q G E B : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (b : It_branch_d α T B)
    (hκ : M.IsCofinality I κ α) (hωκ : M.mem ω κ) (dc : Dc_d I ω)
    (models : ∀ i c, M.mem i B → Rd_entry_d i c Q → It_wf_d I c) :
    ∃ β U Q' G', It_limit_extension_d hZF ω c₀ α T Q G E B β U Q' G' := by
  exact it_wf_branch_extend_l hZF tree (hκ.hasCofinalSequence.elim fun _ hf => hf.isLimitOrdinal)
    (it_sigma_branch_l hZF tree.omega tree.diagram b hκ hωκ dc models)

theorem it_pruned_extend_l {ω c₀ α T Q G E F a Y V P : M.Domain}
    (tree : It_tree_d hZF ω c₀ α T Q G E) (cf : M.IsCofinalOrdinalSequence I F ω α) (ha : M.mem a α)
    (pruned : ∀ i k, M.mem i α → M.mem k α → ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j))
    (realizer : It_realizer_d hZF α Q G Y V P) (wf : Wf_rel_d Y V) :
    ∃ B β U Q' G', It_wf_branch_d hZF ω α T Q G B ∧ M.mem a B ∧
      It_limit_extension_d hZF ω c₀ α T Q G E B β U Q' G' := by
  obtain ⟨B, b, haB⟩ := it_pruned_wf_branch_l hZF tree.omega tree.diagram cf ha pruned realizer wf
  obtain ⟨β, U, Q', G', ext⟩ := it_wf_branch_extend_l hZF tree cf.isLimitOrdinal b
  exact ⟨B, β, U, Q', G', b, haB, ext⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意非空内部序数长度的 padding 树

常模型、恒等嵌入和空操作由公共核心逐项编码；同一常值锥回拉实际源
证书，供原执行树及极限扩张使用。两种强度共用同一份构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_padding_l {ω c α : M.Domain} (ready : It_source_d hZF ω c)
    (ho : M.IsOrdinal α) (ne : ∃ i, M.mem i α) :
    ∃ T Q G E X R P, It_tree_d hZF ω c α T Q G E ∧ Smdl_d I c X R ∧
      It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω α Q G c X R P ∧
      (∀ i j, Rd_entry_d i j T ↔ M.mem i α ∧ M.mem j α ∧ (i = j ∨ M.mem i j)) := by
  obtain ⟨X,R,_,_,_,code,_⟩ := ready.objects
  obtain ⟨T,Q,G,E,P,core,cone,_,order⟩ := it_padding_core_l hZF ready.omega code ho ne
  have sources i b (hb : Rd_entry_d i b Q) : It_source_d hZF ω b := by
    obtain ⟨Y,S,model⟩ := core.diagram.models i b hb
    obtain ⟨j,leg⟩ := (cone.domain i).mp ((core.diagram.model_domain i).mpr ⟨b,hb⟩)
    exact ready.pull_l hZF model code (cone.elementary i j b Y S leg hb model)
  exact ⟨T,Q,G,E,X,R,P,{ toIt_tree_core_d := core, sources := sources },code,cone,order⟩

/-- 实际良基根在任意极限长度的恒等迭代，经一般商与坍塌得到极限添枝。 -/
theorem it_padding_limit_l {ω c α : M.Domain} (ready : It_source_d hZF ω c) (well : It_wf_d I c) (hl : M.IsLimitOrdinal α) :
    ∃ T Q G E β U Q' G', It_tree_d hZF ω c α T Q G E ∧ It_wf_branch_d hZF ω α T Q G α ∧
      It_limit_extension_d hZF ω c α T Q G E α β U Q' G' := by
  obtain ⟨T, Q, G, E, X, R, P, tree, code, cone, ts⟩ := it_padding_l hZF ready hl.1 hl.2.1
  have b : It_branch_d α T α := ⟨fun _ hx => hx, fun i j hi hj => by
    rcases hl.1.wellOrder.linear.compare i hi j hj with eq | hij | hji
    · exact Or.inl ((ts i j).mpr ⟨hi, hj, Or.inl (hZF.1.eq_of_same_members i j eq)⟩)
    · exact Or.inl ((ts i j).mpr ⟨hi, hj, Or.inr hij⟩)
    · exact Or.inr ((ts j i).mpr ⟨hj, hi, Or.inr hji⟩),
    fun i j hij _ => ((ts i j).mp hij).1, fun i hi => ⟨i, hi, Or.inl rfl⟩⟩
  have wf := well.read_l I code
  have built := it_realized_branch_l hZF tree.omega tree.diagram b hl.2.1 (cone.toIt_embedding_d.realizer_l hZF tree.omega) wf
  obtain ⟨β, U, Q', G', ext⟩ := it_wf_branch_extend_l hZF tree hl built
  exact ⟨T, Q, G, E, β, U, Q', G', tree, built, ext⟩

/-- 同一实例同时满足可数共尾枝选择的延伸条件，起点可指定为任意旧结点。 -/
theorem it_padding_pruned_l {ω c α F a : M.Domain} (ready : It_source_d hZF ω c) (well : It_wf_d I c)
    (cf : M.IsCofinalOrdinalSequence I F ω α) (ha : M.mem a α) :
    ∃ T Q G E B β U Q' G', It_tree_d hZF ω c α T Q G E ∧ M.mem a B ∧
      It_wf_branch_d hZF ω α T Q G B ∧ It_limit_extension_d hZF ω c α T Q G E B β U Q' G' := by
  obtain ⟨T, Q, G, E, X, R, P, tree, code, cone, ts⟩ := it_padding_l hZF ready cf.1.1 cf.1.2.1
  have pruned i k (hi : M.mem i α) (hk : M.mem k α) : ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j) := by
    rcases cf.1.1.wellOrder.linear.compare i hi k hk with eq | hik | hki
    · exact ⟨k, hk, (ts i k).mpr ⟨hi, hk, Or.inl (hZF.1.eq_of_same_members i k eq)⟩, Or.inl rfl⟩
    · exact ⟨k, hk, (ts i k).mpr ⟨hi, hk, Or.inr hik⟩, Or.inl rfl⟩
    · exact ⟨i, hi, tree.diagram.order.refl i hi, Or.inr hki⟩
  have wf := well.read_l I code
  obtain ⟨B, β, U, Q', G', built, haB, ext⟩ := it_pruned_extend_l hZF tree cf ha pruned (cone.toIt_embedding_d.realizer_l hZF tree.omega) wf
  exact ⟨T, Q, G, E, B, β, U, Q', G', tree, haB, built, ext⟩

/-! 同一 padding 树上的全部阶段一次选出良基共尾枝。
这里复用公共 `it_padding_l` 的同一 diagram、cone 和修剪证明，
避免逐点调用 `it_padding_pruned_l` 产生彼此不同的树。 -/
theorem it_padding_choice_l {ω c α F : M.Domain} (ready : It_source_d hZF ω c)
    (well : It_wf_d I c) (cf : M.IsCofinalOrdinalSequence I F ω α) :
    ∃ T Q G E X R P, It_tree_d hZF ω c α T Q G E ∧ Smdl_d I c X R ∧
      It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω α Q G c X R P ∧
      ∃ choose : M.Domain → M.Domain,
        ∀ a, M.mem a α → It_wf_branch_d hZF ω α T Q G (choose a) ∧ M.mem a (choose a) := by
  obtain ⟨T, Q, G, E, X, R, P, tree, code, cone, ts⟩ :=
    it_padding_l hZF ready cf.1.1 cf.1.2.1
  have pruned (i k : M.Domain) (hi : M.mem i α) (hk : M.mem k α) :
      ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j) := by
    rcases cf.1.1.wellOrder.linear.compare i hi k hk with eq | hik | hki
    · exact ⟨k, hk, (ts i k).mpr ⟨hi, hk, Or.inl (hZF.1.eq_of_same_members i k eq)⟩, Or.inl rfl⟩
    · exact ⟨k, hk, (ts i k).mpr ⟨hi, hk, Or.inr hik⟩, Or.inl rfl⟩
    · exact ⟨i, hi, tree.diagram.order.refl i hi, Or.inr hki⟩
  obtain ⟨choose, chosen⟩ := it_pruned_wf_branch_choice_l hZF tree.omega tree.diagram cf
    pruned (cone.toIt_embedding_d.realizer_l hZF tree.omega) (well.read_l I code)
  exact ⟨T, Q, G, E, X, R, P, tree, code, cone, ⟨choose, chosen⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

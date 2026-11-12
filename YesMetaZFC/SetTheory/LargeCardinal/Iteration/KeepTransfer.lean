import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableLimit
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedRankReals
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.Forcing.Ground.Collapse

/-! # 弱迭代的可数线性模型列及相容返回列

各个 ω 树的极限作为线性列中的下一模型；这里仅记录实际列及其不变量。
返回列保留每条旧箭头的交换律，供后继和可数极限共同消费。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

omit hZF in
structure Wi_models_d (J : kpair_convention_l.Interpretation M) (ω α T Q G : M.Domain) : Prop where
  diagram : It_diagram_d J ω α T Q G
  linear : ∀ i j, M.mem j α → M.mem i j → Rd_entry_d i j T
  sources : ∀ i c, Rd_entry_d i c Q → ∃ X R K, Smem_d J c X R ∧ Ep_source_d J ω ω K X R
  count : ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual J X ω

omit hZF in
structure Wi_state_d (J : kpair_convention_l.Interpretation M) (ω α T Q G a A S P : M.Domain) : Prop
    extends Wi_models_d J ω α T Q G where
  returns : It_embedding_d J ω α Q G a A S P

def Wi_extension_d (α Q G P β Q' G' P' : M.Domain) : Prop := M.SuccessorOf β α ∧
  (∀ i c, Rd_entry_d i c Q → Rd_entry_d i c Q') ∧
  (∀ i j f, M.mem j α → (It_map_d G' i j f ↔ It_map_d G i j f)) ∧
  ∀ i f, Rd_entry_d i f P → Rd_entry_d i f P'

/-- 原指标列的实际传递直接极限，包括同一商投影与规范腿。 -/
def Wi_limit_d (ω B Q G c N W P : M.Domain) : Prop := ∃ L A p H R r,
  It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N W ∧
    Smem_d I c N W ∧ It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G c N W P ∧
    ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f

/-! 保留极限指标关系与实际良基证书的增强返回证书。`Wi_limit_d`
只服务于旧的语法接口，而本证书供 5.23 的分支闭合消费。 -/
def Wi_limit_tree_d (ω B T Q G c N W P : M.Domain) : Prop := ∃ L A p H R r,
  It_system_d B L Q G A p H R ∧
    (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
    Di_limit_d A p H R r N W ∧ Smem_d I c N W ∧
    It_cone_d (kp_pair_l (ZF.modelsKP hZF)) ω B Q G c N W P ∧
    (∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f) ∧
    Wf_rel_d N W
/-- 给定根嵌入直接构造长度一的真实线性列与返回列。 -/
theorem wi_root_l {ω c X R K a A S π : M.Domain} (source : Ep_source_d I ω ω K X R)
    (mx : Smem_d I c X R) (count : M.CardinalLessOrEqual I X ω)
    (ma : Smem_d I a A S) (embed : Smap_d I ω c a X A π) :
    ∃ o α T Q G P, (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf α o ∧
      Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P ∧ Rd_entry_d o c Q ∧ Rd_entry_d o π P := by
  obtain ⟨o, α, T, Q, G, ho, hα, tree⟩ := it_root_l hZF (it_source_mem_l hZF mx source)
  have one i (hi : M.mem i α) : i = o := ((hα i).mp hi).elim (fun h => (ho i h).elim) (hZF.1.eq_of_same_members i o)
  obtain ⟨D, sd⟩ := KP.exists_singleton (ZF.modelsKP hZF) π
  obtain ⟨P, pf, ps⟩ := ZF.exists_constantFunction hZF I (source := α) ((sd π).mpr rfl)
  have code {i d} (hd : Rd_entry_d i d Q) : d = c := by
    have eq := one i ((tree.diagram.model_domain i).mpr ⟨d, hd⟩)
    exact tree.diagram.model_function.2 i d c hd (eq.symm ▸ tree.root o ho)
  refine ⟨o, α, T, Q, G, P, ho, hα, ⟨⟨tree.diagram, ?_, (fun i d hd => (code hd).symm ▸ ⟨X, R, K, mx, source⟩), ?_⟩, ⟨ma.1, pf.1, pf.2.1, ?_, ?_⟩⟩,
    tree.root o ho, (ps o π).mpr ⟨hα.predecessor_mem, rfl⟩⟩
  · intro i j hj hij
    exact (ho i (one j hj ▸ hij)).elim
  · intro i d Y W hd pair
    obtain ⟨eq, _⟩ := kpair_injective_l M (code hd ▸ pair) mx.1.1
    exact eq.symm ▸ count
  · intro i f d Y W hf hd my
    have eq := code hd
    have ef := ((ps i f).mp hf).2
    subst d f
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I my mx.1
    exact embed
  · intro i j f u v edge hu hv x y z hxy hyz
    have iu := (ps i u).mp hu
    have jv := (ps j v).mp hv
    have ei := one i iu.1
    have ej := one j jv.1
    subst i j
    exact iu.2.symm ▸ jv.2 ▸ (tree.diagram.identity o f edge x y hxy).symm ▸ hyz

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 反射壳固定原有限历史中的全部内部箭头

历史像中的每个模型都传递可数，故其原代码与载体被反坍塌固定。
内部箭头的两个端点逐点固定，因而整张箭头图固定。最后恢复原模型列
及箭头列；完整内部初等性直接来自背景中的真实历史像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem wi_reflected_fixed_l {ω B α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {k} {v : Fin k → M.Domain} (h : Rf_hull_d hZF ω B Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P)
    {n₀ T₀ Q₀ G₀ n T Q G : M.Domain}
    (state : Wi_models_d I ω n T Q G) (hn : M.mem n ω)
    (nn : Rd_entry_d n₀ n π) (tt : Rd_entry_d T₀ T π)
    (qq : Rd_entry_d Q₀ Q π) (gg : Rd_entry_d G₀ G π) :
    n₀ = n ∧ T₀ = T ∧ Q₀ = Q ∧ G₀ = G := by
  have vt := v_transitive_l I h.rank
  have nat := h.map.natural_l hZF hw h.transitive vt h.model h.target hω
  have inside i (hi : M.mem i n) := hw.transitive (ZF.modelsKP hZF) n hn i hi
  have en := h.map.1.2 n₀ n n nn (nat n hn)
  have et := h.map.relation_preimage_l hZF hw h.transitive vt h.model h.target (nat n hn)
    (fun i hi => nat i (inside i hi)) tt ⟨state.diagram.order.relation,state.diagram.order.bound⟩
  have recover {i b : M.Domain} (ib : Rd_entry_d i b Q) :
      ∃ X W K, Smem_d I b X W ∧ Ep_source_d I ω ω K X W ∧
        Rd_entry_d b b π ∧ Rd_entry_d X X π ∧ ∀ x, M.mem x X → Rd_entry_d x x π := by
    obtain ⟨X,W,K,model,source⟩ := state.sources i b ib
    obtain ⟨b₀,_,bb⟩ := h.map.value_preimage_l hZF hw h.transitive vt h.model h.target
      (nat i (inside i ((state.diagram.model_domain i).mpr ⟨b,ib⟩))) qq state.diagram.model_function ib
    exact ⟨X,W,K,model,source,h.model_fixed_l hZF hw hω bb model source.transitive
      (state.count i b X W ib model.1.1)⟩
  have eq := h.function_fixed_l hZF hw qq state.diagram.model_function
    (fun i b ib => nat i (inside i ((state.diagram.model_domain i).mpr ⟨b,ib⟩))) (by
      intro i b _ ib _
      obtain ⟨_,_,_,_,_,fixed,_,_⟩ := recover ib
      exact fixed)
  have eg := h.function_fixed_l hZF hw gg state.diagram.map_function (by
    intro p f pf
    have hp := (state.diagram.map_domain p).mpr ⟨f,pf⟩
    obtain ⟨i,j,pair⟩ := state.diagram.order.relation p hp
    have bounds := state.diagram.order.bound i j ⟨p,pair,hp⟩
    exact h.pair_fixed_l hZF hw pair (nat i (inside i bounds.1)) (nat j (inside j bounds.2))) (by
    intro p f f₀ pf ff
    have hp := (state.diagram.map_domain p).mpr ⟨f,pf⟩
    obtain ⟨i,j,pair⟩ := state.diagram.order.relation p hp
    have bounds := state.diagram.order.bound i j ⟨p,pair,hp⟩
    obtain ⟨b,ib⟩ := (state.diagram.model_domain i).mp bounds.1
    obtain ⟨e,je⟩ := (state.diagram.model_domain j).mp bounds.2
    obtain ⟨X,W,_,model,_,_,_,points⟩ := recover ib
    obtain ⟨Y,Z,_,target,_,_,_,points'⟩ := recover je
    have map := state.diagram.elementary i j f b X W e Y Z ⟨p,pair,pf⟩ ib je model.1 target.1
    have ef := h.function_fixed_l hZF hw ff map.1.1.1
      (fun x y xy => points x (map.1.1.input_mem_of_pairMember xy))
      (fun _ y _ xy _ => points' y (map.1.1.output_mem_of_pairMember xy))
    exact ef ▸ ff)
  exact ⟨en,et,eq,eg⟩

/-- 返回目标允许移动；原返回图通过反坍塌的完整初等限制因子分解。 -/
theorem wi_reflected_returns_l {ω B α V d S P c R π : M.Domain} {Φ : List Lr_formula}
    {k} {v : Fin k → M.Domain} (h : Rf_hull_d hZF ω B Φ v α V d S P c R π)
    (hw : M.IsOmega ω) (hω : M.mem ω P)
    {n T Q G a A U H a' A' U' H' : M.Domain}
    (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω n T Q G a' A' U' H') (hn : M.mem n ω)
    (qq : Rd_entry_d Q Q π) (aa : Rd_entry_d a a' π) (domain : Rd_entry_d A A' π)
    (relation : Rd_entry_d U U' π) (hh : Rd_entry_d H H' π) :
    It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω n Q G a A U H := by
  have vt := v_transitive_l I h.rank
  have nat := h.map.natural_l hZF hw h.transitive vt h.model h.target hω
  have inside i (hi : M.mem i n) := hw.transitive (ZF.modelsKP hZF) n hn i hi
  have model := h.map.smdl_preimage_l hZF hw h.transitive vt h.model h.target aa domain relation state.returns.model
  obtain ⟨j,embed,cut⟩ := h.restrict_l hZF hw hω model state.returns.model domain relation
  obtain ⟨fn,dom⟩ := h.map.function_preimage_l hZF hw h.transitive vt h.model h.target
    (nat n hn) hh state.returns.function state.returns.domain
  have fixed {i b X W : M.Domain} (ib : Rd_entry_d i b Q) (mx : Smdl_d I b X W) :
      Rd_entry_d X X π ∧ ∀ x, M.mem x X → Rd_entry_d x x π := by
    obtain ⟨Y,Z,K,my,src⟩ := state.sources i b ib
    obtain ⟨rfl,rfl⟩ := smdl_unique_l I my.1 mx
    obtain ⟨b₀,_,bb⟩ := h.map.value_preimage_l hZF hw h.transitive vt h.model h.target
      (nat i (inside i ((state.diagram.model_domain i).mpr ⟨b,ib⟩))) qq state.diagram.model_function ib
    exact (h.model_fixed_l hZF hw hω bb my src.transitive (state.count i b Y Z ib my.1.1)).2
  have image {i f : M.Domain} (edge : Rd_entry_d i f H) :
      ∃ f', Rd_entry_d f f' π ∧ Rd_entry_d i f' H' := by
    obtain ⟨p,pair,hp⟩ := edge
    have hf := (pair.mem_l M h.transitive (h.transitive H (h.map.1.1.input_mem_of_pairMember hh) p hp)).2
    obtain ⟨f',_,ff⟩ := h.map.1.1.2.2 f hf
    exact ⟨f',ff,(h.map.entry_l hZF hw h.transitive vt h.model h.target
      (nat i (inside i ((dom i).mpr ⟨f,⟨p,pair,hp⟩⟩))) ff hh).mp ⟨p,pair,hp⟩⟩
  have returns {i f b X W : M.Domain} (ir : Rd_entry_d i f H) (ib : Rd_entry_d i b Q)
      (mx : Smdl_d I b X W) : Smap_d I ω b a X A f := by
    obtain ⟨f',ff,ir'⟩ := image ir
    have next := state.returns.elementary i f' b X W ir' ib mx
    have fix := fixed ib mx
    have actual := fn0_function_l (ZF.modelsKP hZF)
      ((h.map.function_l hZF hw h.transitive vt h.model h.target fix.1 domain ff).mpr
        (fn0_of_function_l (ZF.modelsKP hZF) next.1.1))
    apply smap_factor_l I hZF next embed actual
    intro x y z xy yz
    exact (h.map.entry_l hZF hw h.transitive vt h.model h.target
      (fix.2 x (actual.input_mem_of_pairMember xy)) ((cut.2 y z).mp yz).2 ff).mp xy
  refine ⟨model,fn,dom,fun _ _ _ _ _ ir ib mx => returns ir ib mx,?_⟩
  intro i l g p q edge ip lq x y z xy yz
  have bounds := state.diagram.order.bound i l (state.diagram.map_bound_l hZF edge)
  obtain ⟨b,X,W,ib,mx⟩ := state.diagram.model_l hZF bounds.1
  obtain ⟨e,Y,Z,le,my⟩ := state.diagram.model_l hZF bounds.2
  have arrow := state.diagram.elementary i l g b X W e Y Z edge ib le mx my
  obtain ⟨p',pp,ip'⟩ := image ip
  obtain ⟨q',qq',lq'⟩ := image lq
  have hz := (returns lq le my).1.1.output_mem_of_pairMember yz
  obtain ⟨z',_,zz⟩ := h.map.1.1.2.2 z (h.transitive A (h.map.1.1.input_mem_of_pairMember domain) z hz)
  have target := (h.map.entry_l hZF hw h.transitive vt h.model h.target
    ((fixed le my).2 y (arrow.1.1.output_mem_of_pairMember xy)) zz qq').mp yz
  exact (h.map.entry_l hZF hw h.transitive vt h.model h.target
    ((fixed ib mx).2 x (arrow.1.1.input_mem_of_pairMember xy)) zz pp).mpr
      (state.returns.commute i l g p' q' edge ip' lq' x y z' xy target)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 线性模型列的返回因子随实际新结点延长 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_state_d.branch_l {ω α T Q G a A S P : M.Domain} (h : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P) :
    It_branch_d α T α := by
  refine ⟨fun _ hi => hi, ?_, fun i j hij _ => (h.diagram.order.bound i j hij).1, fun i hi => ⟨i, hi, Or.inl rfl⟩⟩
  intro i j hi hj
  rcases (h.diagram.order.ordinal.mem hi).trichotomy hZF.1 (h.diagram.order.ordinal.mem hj)
    (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) i j) with eq | lt | gt
  · exact Or.inl ((hZF.1.eq_of_same_members i j eq) ▸ h.diagram.order.refl i hi)
  · exact Or.inl (h.linear i j hj lt)
  · exact Or.inr (h.linear j i hi gt)

/-- 旧返回列只追加新因子；所有旧值和所有交换三角形都保留。 -/
theorem Wi_state_d.append_l {ω α T Q G a A S P β U Q' G' c N W σ : M.Domain}
    (h : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P) (hβ : M.SuccessorOf β α)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G')
    (order : ∀ i j, Rd_entry_d i j T → Rd_entry_d i j U)
    (tip : ∀ i, M.mem i α → Rd_entry_d i α U)
    (qs : ∀ i d, Rd_entry_d i d Q' ↔ Rd_entry_d i d Q ∨ i = α ∧ d = c)
    (gs : ∀ i j f, M.mem j α → (It_map_d G' i j f ↔ It_map_d G i j f))
    (mn : Smem_d I c N W) (source : ∃ K, Ep_source_d I ω ω K N W) (count : M.CardinalLessOrEqual I N ω)
    (hs : Smap_d I ω c a N A σ)
    (squares : ∀ i f j, Rd_entry_d i f P → It_map_d G' i α j → It_comp_d j σ f) :
    ∃ P', Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β U Q' G' a A S P' ∧
      ∀ i f, Rd_entry_d i f P' ↔ Rd_entry_d i f P ∨ i = α ∧ f = σ := by
  have no := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  obtain ⟨P', pf, ps⟩ := Structure.IsSequenceOfLength.exists_append (value := σ) (ZF.modelsKP hZF) I
    ⟨h.diagram.order.ordinal, h.returns.function, h.returns.domain⟩ diagram.order.ordinal hβ
  have old i f (hi : M.mem i α) : Rd_entry_d i f P' ↔ Rd_entry_d i f P := (ps i f).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  have qold i d (hi : M.mem i α) : Rd_entry_d i d Q' ↔ Rd_entry_d i d Q := (qs i d).trans
    ⟨fun hh => hh.elim id (fun hh => (no (hh.1 ▸ hi)).elim), Or.inl⟩
  refine ⟨P', ⟨⟨diagram, ?_, ?_, ?_⟩, ⟨h.returns.model, pf.2.1, pf.2.2, ?_, ?_⟩⟩, ps⟩
  · intro i j hj hij
    rcases (hβ j).mp hj with hj | eq
    · exact order i j (h.linear i j hj hij)
    · have eq := hZF.1.eq_of_same_members j α eq
      subst j
      exact tip i hij
  · intro i d hd
    exact ((qs i d).mp hd).elim (h.sources i d) (fun hh => hh.2.symm ▸ source.elim fun K s => ⟨N, W, K, mn, s⟩)
  · intro i d X R hd pair
    rcases (qs i d).mp hd with hd | ⟨_, rfl⟩
    · exact h.count i d X R hd pair
    · obtain ⟨eq, _⟩ := kpair_injective_l M pair mn.1.1
      exact eq.symm ▸ count
  · intro i f d X R hf hd mx
    rcases (ps i f).mp hf with hf | ⟨ei, ef⟩
    · exact h.returns.elementary i f d X R hf ((qold i d ((h.returns.domain i).mpr ⟨f, hf⟩)).mp hd) mx
    · subst i f
      have eq : d = c := ((qs α d).mp hd).elim
        (fun hd => (no ((h.diagram.model_domain α).mpr ⟨d, hd⟩)).elim) And.right
      subst d
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx mn.1
      exact hs
  · intro i j f u v edge hu hv x y z hxy hyz
    rcases (ps j v).mp hv with hv | ⟨ej, ev⟩
    · have edge := (gs i j f ((h.returns.domain j).mpr ⟨v, hv⟩)).mp edge
      have hi := (h.diagram.order.bound i j (h.diagram.map_bound_l hZF edge)).1
      exact h.returns.commute i j f u v edge ((old i u hi).mp hu) hv x y z hxy hyz
    · subst j v
      rcases (ps i u).mp hu with hu | ⟨ei, eu⟩
      · exact ((squares i u f hu edge).2 x z).mpr ⟨y, hxy, hyz⟩
      · subst i u
        exact (diagram.identity α f edge x y hxy).symm ▸ hyz

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 弱迭代历史保留所有此前列图

第 i 行存长度 i+1 的真实状态；每条早期条目在所有后来状态中保持原值。
这使极限取并只须回到含有有限多个指定条目的同一旧行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Wi_keep_d (Q G P Q' G' P' : M.Domain) : Prop :=
  (∀ i c, Rd_entry_d i c Q → Rd_entry_d i c Q') ∧
  (∀ i j f, It_map_d G i j f → It_map_d G' i j f) ∧
  ∀ i f, Rd_entry_d i f P → Rd_entry_d i f P'
def Wi_at_d (H i T Q G P : M.Domain) : Prop := ∃ s, Rd_entry_d i s H ∧ Rd_quad_d s T Q G P

theorem Wi_keep_d.refl_l (Q G P : M.Domain) : Wi_keep_d Q G P Q G P := ⟨fun _ _ h => h, fun _ _ _ h => h, fun _ _ h => h⟩
theorem Wi_keep_d.trans_l {Q G P Q' G' P' Q'' G'' P'' : M.Domain}
    (h : Wi_keep_d Q G P Q' G' P') (g : Wi_keep_d Q' G' P' Q'' G'' P'') : Wi_keep_d Q G P Q'' G'' P'' :=
  ⟨fun i c hc => g.1 i c (h.1 i c hc), fun i j f hf => g.2.1 i j f (h.2.1 i j f hf), fun i f hf => g.2.2 i f (h.2.2 i f hf)⟩

structure Wi_history_d (hZF : M.Models ZF) (ω a A S α D H : M.Domain) : Prop where
  function : Fn0_d α D H
  rows : ∀ i s, Rd_entry_d i s H → ∃ β T Q G P,
    M.SuccessorOf β i ∧ Rd_quad_d s T Q G P ∧ Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G a A S P
  past : ∀ i j T Q G P U Q' G' P', M.mem i j → Wi_at_d H i T Q G P → Wi_at_d H j U Q' G' P' → Wi_keep_d Q G P Q' G' P'

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Wi_extension_d.keep_l {ω α T Q G a A S P β Q' G' P' : M.Domain}
    (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P) (h : Wi_extension_d α Q G P β Q' G' P') : Wi_keep_d Q G P Q' G' P' :=
  ⟨h.2.1, fun i j f hf => (h.2.2.1 i j f (state.diagram.order.bound i j (state.diagram.map_bound_l hZF hf)).2).mpr hf, h.2.2.2⟩

theorem Wi_history_d.at_l {ω a A S α D H i T Q G P : M.Domain}
    (h : Wi_history_d hZF ω a A S α D H) (hi : Wi_at_d H i T Q G P) :
    ∃ β, M.SuccessorOf β i ∧ Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω β T Q G a A S P := by
  obtain ⟨s, hs, pack⟩ := hi
  obtain ⟨β, T₀, Q₀, G₀, P₀, hβ, pack₀, state⟩ := h.rows i s hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := pack₀.unique_l pack
  exact ⟨β, hβ, state⟩

theorem Wi_history_d.restrict_l {ω a A S α D H β J : M.Domain}
    (h : Wi_history_d hZF ω a A S α D H) (sub : M.MemberSubset β α)
    (r : M.IsRestrictionOf I J H β) : Wi_history_d hZF ω a A S β D J := by
  refine ⟨fn0_of_function_l (ZF.modelsKP hZF) (r.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) h.function) sub),
    fun i s hs => h.rows i s ((r.2 i s).mp hs).2, ?_⟩
  intro i j T Q G P U Q' G' P' hij ⟨s, hs, ps⟩ ⟨t, ht, pt⟩
  exact h.past i j T Q G P U Q' G' P' hij ⟨s, ((r.2 i s).mp hs).2, ps⟩ ⟨t, ((r.2 j t).mp ht).2, pt⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原历史包含关系的无模式向外保持

旧条目中的全部坐标由实际有序对成员路径留在测试壳。
因而三列保持只需传递性与外延性，不需要壳内替代、收集或初等图解码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (J : kpair_convention_l.Interpretation M) (hE : Extensional M)
  {c P R : M.Domain} (model : Smem_d J c P R) (trans : M.TransitiveSet P)
include hE trans

theorem wi_keep_outer_l
    {Q G U Q' G' U' : (smdl_structure_l J (R := R) model.1.2.1).Domain}
    (keep : Wi_keep_d Q G U Q' G' U') : Wi_keep_d Q.val G.val U.val Q'.val G'.val U'.val := by
  let N := smdl_structure_l J (R := R) model.1.2.1
  have ext := smem_ext_l J model.1 model.2 trans hE
  have full := smem_full_l J model trans
  have entry (a b f : N.Domain) : Rd_entry_d a b f ↔ Rd_entry_d a.val b.val f.val := by
    let ρ : Env N 3 := ⟨fun k => [a,b,f].get k,fun _ => a⟩
    exact (rd_entry0_sat_l ext ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((smem_delta_image_l J model trans (rd_entry0_delta_l ..) ρ).trans
        (rd_entry0_sat_l hE (image_env_l (M := N) (N := M) Subtype.val ρ) (.bound 0) (.bound 1) (.bound 2)))
  have bounds {a b : M.Domain} {f : N.Domain} (edge : Rd_entry_d a b f.val) : M.mem a P ∧ M.mem b P := by
    obtain ⟨p,pair,hp⟩ := edge
    exact pair.mem_l M trans (trans f.val f.property p hp)
  have move {f g : N.Domain} (preserve : ∀ a b : N.Domain, Rd_entry_d a b f → Rd_entry_d a b g)
      {a b : M.Domain} (edge : Rd_entry_d a b f.val) : Rd_entry_d a b g.val := by
    have bound := bounds (f := f) edge
    exact (entry ⟨a,bound.1⟩ ⟨b,bound.2⟩ g).mp
      (preserve ⟨a,bound.1⟩ ⟨b,bound.2⟩ ((entry ⟨a,bound.1⟩ ⟨b,bound.2⟩ f).mpr edge))
  refine ⟨fun _ _ edge => move keep.1 edge,?_,fun _ _ edge => move keep.2.2 edge⟩
  intro i j f ⟨p,pair,pf⟩
  have bound := bounds (f := G) pf
  have ij := pair.mem_l M trans bound.1
  let i₀ : N.Domain := ⟨i,ij.1⟩
  let j₀ : N.Domain := ⟨j,ij.2⟩
  let p₀ : N.Domain := ⟨p,bound.1⟩
  let f₀ : N.Domain := ⟨f,bound.2⟩
  let ρ : Env N 3 := ⟨fun k => [p₀,i₀,j₀].get k,fun _ => p₀⟩
  have pp : KPair_d N p₀ i₀ j₀ := (kpair0_sat_l ext ρ (.bound 0) (.bound 1) (.bound 2)).mp
    ((smem_delta_image_l J model trans (kpair0_delta_l ..) ρ).mpr
      ((kpair0_sat_l hE (image_env_l (M := N) (N := M) Subtype.val ρ) (.bound 0) (.bound 1) (.bound 2)).mpr pair))
  obtain ⟨q,qp,qf⟩ := keep.2.1 i₀ j₀ f₀ ⟨p₀,pp,(entry p₀ f₀ G).mpr pf⟩
  exact ⟨q.val,image_kpair_l (M := N) (N := M) Subtype.val full qp,(entry q f₀ G').mp qf⟩

end YesMetaZFC.SetTheory.LargeCardinal

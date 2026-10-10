import YesMetaZFC.SetTheory.LargeCardinal.IterationRoot
import YesMetaZFC.SetTheory.LargeCardinal.IterationCountableLimit

/-! # 弱迭代的可数线性模型列及相容返回列

各个 ω 树的极限作为线性列中的下一模型；这里仅记录实际列及其不变量。
返回列保留每条旧箭头的交换律，供后继和可数极限共同消费。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Wi_state_d (ω α T Q G a A S P : M.Domain) : Prop where
  diagram : It_diagram_d hZF ω α T Q G
  linear : ∀ i j, M.mem j α → M.mem i j → Rd_entry_d i j T
  sources : ∀ i c, Rd_entry_d i c Q → It_source_d hZF ω c
  count : ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.CardinalLessOrEqual I X ω
  returns : It_embedding_d hZF ω α Q G a A S P

def Wi_extension_d (α Q G P β Q' G' P' : M.Domain) : Prop := M.SuccessorOf β α ∧
  (∀ i c, Rd_entry_d i c Q → Rd_entry_d i c Q') ∧
  (∀ i j f, M.mem j α → (It_map_d G' i j f ↔ It_map_d G i j f)) ∧
  ∀ i f, Rd_entry_d i f P → Rd_entry_d i f P'

/-- 原指标列的实际传递直接极限，包括同一商投影与规范腿。 -/
def Wi_limit_d (ω B Q G c N W P : M.Domain) : Prop := ∃ L A p H R r,
  It_system_d B L Q G A p H R ∧ Di_limit_d A p H R r N W ∧
    Smem_d I c N W ∧ It_cone_d hZF ω B Q G c N W P ∧
    ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f

/-- 给定根嵌入直接构造长度一的真实线性列与返回列。 -/
theorem wi_root_l {ω c X R a A S π : M.Domain} (source : It_source_d hZF ω c)
    (mx : Smem_d I c X R) (count : M.CardinalLessOrEqual I X ω)
    (ma : Smem_d I a A S) (embed : Smap_d I ω c a X A π) :
    ∃ o α T Q G P, (∀ x, ¬ M.mem x o) ∧ M.SuccessorOf α o ∧
      Wi_state_d hZF ω α T Q G a A S P ∧ Rd_entry_d o c Q ∧ Rd_entry_d o π P := by
  obtain ⟨o, α, T, Q, G, ho, hα, tree⟩ := it_root_l hZF source
  have one i (hi : M.mem i α) : i = o := ((hα i).mp hi).elim (fun h => (ho i h).elim) (hZF.1.eq_of_same_members i o)
  obtain ⟨D, sd⟩ := KP.exists_singleton (ZF.modelsKP hZF) π
  obtain ⟨P, pf, ps⟩ := ZF.exists_constantFunction hZF I (source := α) ((sd π).mpr rfl)
  have code {i d} (hd : Rd_entry_d i d Q) : d = c := by
    have eq := one i ((tree.diagram.model_domain i).mpr ⟨d, hd⟩)
    exact tree.diagram.model_function.2 i d c hd (eq.symm ▸ tree.root o ho)
  refine ⟨o, α, T, Q, G, P, ho, hα, ⟨tree.diagram, ?_, tree.sources, ?_, ⟨ma.1, pf.1, pf.2.1, ?_, ?_⟩⟩,
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

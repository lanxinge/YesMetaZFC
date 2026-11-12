import YesMetaZFC.Model.SetTheory.Game.Graph

/-! # 任意有限排列后的双图恢复

中间坐标只按两组值的并集读取。标签的所属由右坐标所在的两个不交
值域确定，既不要求组内排序，也不预设旧图包含于新图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

/-- 两组标签合起来恰为树与高度端点之间的全部元组值。 -/
def Td_labels_d (I : kpair_convention_l.Interpretation M) (e l r a b : M.Domain) : Prop :=
  ∀ p, (M.mem p a ∨ M.mem p b) ↔ ∃ i, M.mem i l ∧ i ≠ e ∧ M.PairMember I i p r

variable (hE : Extensional M) (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
  (hirr : ∀ x, ¬ M.mem x x)
local notation "I" => kpair_interpretation_l M hE hP
include hirr

/-- 先恢复端点再读取树的最小字母域，端点识别不预设两组标签的值域。 -/
theorem td_node_endpoints_l {e j k l n X r T S s a b α β : M.Domain}
    (he : ∀ x, ¬ M.mem x e) (hk : M.SuccessorOf k j) (hn : M.SuccessorOf n l)
    (tuple : M.IsSetFunctionFromTo I r n X) (root : Rd_entry_d e T r) (last : Rd_entry_d l β r)
    (labels : Td_labels_d I e l r a b) (node : Tg_node_d I k T s a b)
    (hα : M.IsOrdinal α) (hS : M.mem e S) (ne : S ≠ α)
    (seenS : ∃ i, M.mem i n ∧ Rd_entry_d i S r)
    (seenα : ∃ i, M.mem i n ∧ Rd_entry_d i α r) : T = S ∧ β = α := by
  have slot i x (hi : M.mem i n) (hx : Rd_entry_d i x r) :
      x = T ∨ M.mem x a ∨ M.mem x b ∨ x = β := by
    rcases (hn i).mp hi with hi | eq
    · by_cases ie : i = e
      · exact Or.inl (tuple.1.2 e x T (ie ▸ hx) root)
      · exact ((labels x).mpr ⟨i,hi,ie,hx⟩).elim
          (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (tuple.1.2 l x β (hE.eq_of_same_members i l eq ▸ hx) last)))
  have endα : β = α := by
    obtain ⟨i,hi,hx⟩ := seenα
    rcases slot i α hi hx with eq | ha | hb | eq
    · exact (node.not_ordinal_l hE hP hirr hk.predecessor_mem (eq ▸ hα)).elim
    · obtain ⟨i,x,pair⟩ := node.2.1.1.1 α ha
      exact (pair.not_transitive_l M hirr hα.transitive).elim
    · obtain ⟨i,x,pair⟩ := node.2.2.1.1.1 α hb
      exact (pair.not_transitive_l M hirr hα.transitive).elim
    · exact eq.symm
  have startS : T = S := by
    obtain ⟨i,hi,hx⟩ := seenS
    rcases slot i S hi hx with eq | ha | hb | eq
    · exact eq.symm
    · obtain ⟨i,x,pair⟩ := node.2.1.1.1 S ha
      exact (KPair_d.empty_not_mem_l he pair hS).elim
    · obtain ⟨i,x,pair⟩ := node.2.2.1.1.1 S hb
      exact (KPair_d.empty_not_mem_l he pair hS).elim
    · exact (ne (eq.trans endα)).elim
  exact ⟨startS,endα⟩

/-- 真实出现的旧标签和指定待回应点恢复两个端点与两张精确追加图。 -/
theorem td_node_recover_l {e j k l n X r T S s a b a' b' U₁ U₂ z p α β : M.Domain}
    (he : ∀ x, ¬ M.mem x e) (hk : M.SuccessorOf k j) (hn : M.SuccessorOf n l)
    (tuple : M.IsSetFunctionFromTo I r n X) (root : Rd_entry_d e T r) (last : Rd_entry_d l β r)
    (labels : Td_labels_d I e l r a' b') (node : Tg_node_d I k T s a' b')
    (fa : M.IsSetFunctionFromTo I a j U₁) (fb : M.IsSetFunctionFromTo I b j U₂)
    (fa' : M.IsSetFunctionFromTo I a' k U₁) (fb' : M.IsSetFunctionFromTo I b' k U₂)
    (disjoint : ∀ x, M.mem x U₁ → ¬ M.mem x U₂)
    (hz : M.mem z U₁) (pending : KPair_d M p j z)
    (hα : M.IsOrdinal α) (hS : M.mem e S) (ne : S ≠ α)
    (seenS : ∃ i, M.mem i n ∧ Rd_entry_d i S r)
    (seenα : ∃ i, M.mem i n ∧ Rd_entry_d i α r)
    (seen : ∀ q, M.mem q a ∨ M.mem q b ∨ q = p → ∃ i, M.mem i n ∧ Rd_entry_d i q r) :
    T = S ∧ β = α ∧ M.MemberSubset a a' ∧ M.MemberSubset b b' ∧
      Rd_entry_d j z a' ∧ (∀ q, M.mem q a' ↔ M.mem q a ∨ KPair_d M q j z) ∧
      ∃ z', M.mem z' U₂ ∧ Rd_entry_d j z' b' ∧
        ∀ q, M.mem q b' ↔ M.mem q b ∨ KPair_d M q j z' := by
  obtain ⟨startS,endα⟩ := td_node_endpoints_l hE hP hirr he hk hn tuple root last labels node hα hS ne seenS seenα
  have slot i x (hi : M.mem i n) (hx : Rd_entry_d i x r) :
      x = T ∨ M.mem x a' ∨ M.mem x b' ∨ x = β := by
    rcases (hn i).mp hi with hi | eq
    · by_cases ie : i = e
      · exact Or.inl (tuple.1.2 e x T (ie ▸ hx) root)
      · exact ((labels x).mpr ⟨i,hi,ie,hx⟩).elim
          (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (tuple.1.2 l x β (hE.eq_of_same_members i l eq ▸ hx) last)))
  have middle q i x (pair : KPair_d M q i x)
      (old : M.mem q a ∨ M.mem q b ∨ q = p) : M.mem q a' ∨ M.mem q b' := by
    obtain ⟨v,hv,hq⟩ := seen q old
    rcases slot v q hv hq with eq | ha | hb | eq
    · exact (KPair_d.empty_not_mem_l he pair ((eq.trans startS).symm ▸ hS)).elim
    · exact Or.inl ha
    · exact Or.inr hb
    · exact (pair.not_transitive_l M hirr ((eq.trans endα).symm ▸ hα.transitive)).elim
  have suba : M.MemberSubset a a' := by
    intro q hq
    obtain ⟨i,x,pair⟩ := fa.1.1 q hq
    exact (middle q i x pair (Or.inl hq)).elim id (fun h =>
      (disjoint x (fa.output_mem_of_pairMember ⟨q,pair,hq⟩) (fb'.output_mem_of_pairMember ⟨q,pair,h⟩)).elim)
  have subb : M.MemberSubset b b' := by
    intro q hq
    obtain ⟨i,x,pair⟩ := fb.1.1 q hq
    exact (middle q i x pair (Or.inr (Or.inl hq))).elim (fun h =>
      (disjoint x (fa'.output_mem_of_pairMember ⟨q,pair,h⟩) (fb.output_mem_of_pairMember ⟨q,pair,hq⟩)).elim) id
  have point : Rd_entry_d j z a' := ⟨p,pending,
    (middle p j z pending (Or.inr (Or.inr rfl))).elim id (fun h =>
      (disjoint z hz (fb'.output_mem_of_pairMember ⟨p,pending,h⟩)).elim)⟩
  obtain ⟨v,hv,first⟩ := tg_graph_extend_l hE hP hk ⟨fa.1,fa.2.1⟩ ⟨fa'.1,fa'.2.1⟩ suba
  have eq := fa'.1.2 j v z hv point
  obtain ⟨z',hz',second⟩ := tg_graph_extend_l hE hP hk ⟨fb.1,fb.2.1⟩ ⟨fb'.1,fb'.2.1⟩ subb
  exact ⟨startS,endα,suba,subb,point,eq ▸ first,z',fb'.output_mem_of_pairMember hz',hz',second⟩

end YesMetaZFC.SetTheory.Internal

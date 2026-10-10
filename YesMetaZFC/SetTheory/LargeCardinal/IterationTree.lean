import YesMetaZFC.SetTheory.LargeCardinal.IterationStep

/-! # 带所属扩展器、超幂边及极限条件的迭代树

模型、嵌入和操作记录都是内部集合图。活动步从当前结点读取真正的
模型内短扩展器，施加到树前驱的源；pad 使用恒等边。极限结点由严格
前驱的嵌入像覆盖，完整初等性与交换律已由图证书保证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_payload_d (p κ L F : M.Domain) : Prop := ∃ r, KPair_d M p κ r ∧ KPair_d M r L F

def It_active_d (hZF : M.Models ZF) (ω c d b j p : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ κ L F X R Y S, It_payload_d p κ L F ∧ Smem_d I c X R ∧ Smem_d I d Y S ∧
    It_local_d ω X κ L F ∧ Ea_agree_d ω κ X Y ∧ It_ultra_d hZF ω κ L F d b j

def It_step_d (hZF : M.Models ZF) (ω T Q G E ξ η : M.Domain) : Prop := ∃ k c d b j p,
  It_pred_d T k η ∧ Rd_entry_d ξ c Q ∧ Rd_entry_d k d Q ∧ Rd_entry_d η b Q ∧
    It_map_d G k η j ∧ Rd_entry_d ξ p E ∧
    (((∀ x, ¬ M.mem x p) ∧ k = ξ ∧ b = c ∧ ∀ x y, Rd_entry_d x y j → x = y) ∨ It_active_d hZF ω c d b j p)

def It_limit_d (T Q G δ : M.Domain) : Prop := ∀ c X R,
  Rd_entry_d δ c Q → KPair_d M c X R → ∀ y, M.mem y X →
    ∃ i, M.mem i δ ∧ Rd_entry_d i δ T ∧ ∃ f, It_map_d G i δ f ∧ ∃ x, Rd_entry_d x y f

structure It_tree_d (hZF : M.Models ZF) (ω c₀ α T Q G E : M.Domain) : Prop where
  omega : M.IsOmega ω
  diagram : It_diagram_d hZF ω α T Q G
  root : ∀ z, (∀ x, ¬ M.mem x z) → Rd_entry_d z c₀ Q
  sources : ∀ i c, Rd_entry_d i c Q → It_source_d hZF ω c
  move_function : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) E
  move_domain : ∀ i, (∃ p, Rd_entry_d i p E) ↔ ∃ j, M.mem j α ∧ M.SuccessorOf j i
  steps : ∀ i j, M.mem j α → M.SuccessorOf j i → It_step_d hZF ω T Q G E i j
  limits : ∀ δ, M.mem δ α → M.IsLimitOrdinal δ → It_limit_d T Q G δ

def It_extension_d (α ξ k T Q G E β U Q' G' E' : M.Domain) : Prop := M.SuccessorOf β α ∧
  (∀ i l, Rd_entry_d i l U ↔ Rd_entry_d i l T ∨ l = α ∧ (i = α ∨ Rd_entry_d i k T)) ∧
  (∀ i a, Rd_entry_d i a Q → Rd_entry_d i a Q') ∧
  (∀ i l f, M.mem l α → (It_map_d G' i l f ↔ It_map_d G i l f)) ∧
  (∀ i a, Rd_entry_d i a E → Rd_entry_d i a E') ∧
  (∀ i a, i ≠ ξ → (Rd_entry_d i a E' ↔ Rd_entry_d i a E))


variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 操作列添加一项，已有图条目精确保留。 -/
theorem it_move_push_l {E ξ p : M.Domain} (hf : M.IsSetFunction I E)
    (fresh : ∀ x, ¬ Rd_entry_d ξ x E) : ∃ E', M.IsSetFunction I E' ∧
      ∀ i x, Rd_entry_d i x E' ↔ Rd_entry_d i x E ∨ i = ξ ∧ x = p := by
  obtain ⟨r, hr⟩ := (I).total ξ p
  obtain ⟨B, hb⟩ := KP.exists_singleton hKP r
  obtain ⟨E', he⟩ := KP.exists_unionOfTwo hKP E B
  have read i x : Rd_entry_d i x E' ↔ Rd_entry_d i x E ∨ i = ξ ∧ x = p := by
    constructor
    · rintro ⟨s, hs, hsE⟩
      rcases (he s).mp hsE with hsE | hsB
      · exact Or.inl ⟨s, hs, hsE⟩
      · exact Or.inr (kpair_injective_l M hs (((hb s).mp hsB).symm ▸ hr))
    · rintro (⟨s, hs, hsE⟩ | ⟨rfl, rfl⟩)
      · exact ⟨s, hs, (he s).mpr (Or.inl hsE)⟩
      · exact ⟨r, hr, (he r).mpr (Or.inr ((hb r).mpr rfl))⟩
  refine ⟨E', ⟨fun s hs => ?_, fun i x y hx hy => ?_⟩, read⟩
  · rcases (he s).mp hs with hs | hs
    · exact hf.1 s hs
    · exact ⟨ξ, p, ((hb s).mp hs).symm ▸ hr⟩
  · rcases (read i x).mp hx with hx | ⟨rfl, rfl⟩
    · rcases (read i y).mp hy with hy | ⟨rfl, _⟩
      · exact hf.2 i x y hx hy
      · exact (fresh x hx).elim
    · rcases (read _ y).mp hy with hy | ⟨_, eq⟩
      · exact (fresh y hy).elim
      · exact eq.symm

end YesMetaZFC.SetTheory.LargeCardinal

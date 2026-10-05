import YesMetaZFC.SetTheory.LargeCardinal.IterationLimitModel
import YesMetaZFC.SetTheory.Card.Cofinality.Boundedness

/-! # 共尾树枝的内部良基性

分量良基性直接来自隶属关系的正则公理。若时间长度的共尾度大于 ω，
内部可数指标族有界，共尾枝将其送到同一分量；ZF＋DC 因而排除下降链。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem It_tag_d.wf_l (hZF : M.Models ZF) {B Q A p R D H : M.Domain}
    (h : It_tag_d B Q A p R) (hq : Fn0_d D H Q)
    (models : ∀ i c, Rd_entry_d i c Q → ∃ X S, Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X S) :
    Di_wf_d A p R := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro i Z hz indexed hn
  obtain ⟨u, hu⟩ := hn
  obtain ⟨_, _, c, _, _, hc, _, _⟩ := h.label_l (indexed u hu)
  obtain ⟨X, S, model⟩ := models i c hc
  let φ : BinarySchema 1 := { body := kpair_m (.bound 1) (.bound 2) .newest }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have sat a x : φ.denote ρ a x ↔ KPair_d M a i x := kpair_sat_l M hZF.1 ..
  obtain ⟨f, hf, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Z) (target := X)
    (fun a ha => by
      obtain ⟨x, hx, _⟩ := h.label_l (indexed a ha)
      exact ⟨x, (sat a x).mpr hx⟩)
    (fun a _ x y hx hy => (kpair_injective_l M ((sat a x).mp hx) ((sat a y).mp hy)).2)
    (fun a x ha hx => (ep_at_read_l hq hc model.1.1).mp (h.at_l (hz a ha) ((sat a x).mp hx)))
  have wx : Wf_rel_d X S := fun Y _ nonempty => by
    obtain ⟨x, hx, minimal⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) nonempty
    exact ⟨x, hx, fun y hy rel => minimal y hy ((model.2 y x).mp rel).2.2⟩
  have wz : Wf_rel_d Z R := wf_of_map_l hZF wx (fn0_of_function_l (ZF.modelsKP hZF) hf) (by
    intro a b x y hab hax hby
    have ha := (sat a x).mp ((fs a x).mp hax).2
    have hb := (sat b y).mp ((fs b y).mp hby).2
    exact (ep_rel_read_l hq hc model.1.1).mp ((h.relation_l ha hb).mp hab).2.2)
  exact wz Z (fun _ hx => hx) ⟨u, hu⟩

theorem It_branch_d.forward_l {α T B i j : M.Domain} (h : It_order_d α T) (b : It_branch_d α T B)
    (hi : M.mem i B) (hj : M.mem j B) (below : i = j ∨ M.mem i j) : Rd_entry_d i j T := by
  rcases below with rfl | hij
  · exact h.refl _ (b.subset _ hj)
  · rcases b.chain i j hi hj with ht | ht
    · exact ht
    · rcases h.forward j i ht with rfl | hji
      · exact (h.ordinal.wellOrder.linear.irrefl _ (b.subset _ hi) hij).elim
      · exact (h.ordinal.wellOrder.linear.irrefl j (b.subset j hj)
          ((h.ordinal.mem (b.subset j hj)).transitive i hij j hji)).elim

theorem It_branch_d.sigma_l (hZF : M.Models ZF) {ω α κ T B L : M.Domain}
    (h : It_order_d α T) (b : It_branch_d α T B)
    (hκ : M.IsCofinality (kp_pair_l (ZF.modelsKP hZF)) κ α) (hωκ : M.mem ω κ)
    (ls : ∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) : Di_sigma_d ω B L := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro f hf
  have ff := fn0_function_l (ZF.modelsKP hZF) (hf.mono_target_l b.subset)
  obtain ⟨D, hd⟩ := ZF.exists_range_of_setFunction hZF I ff.1 ff.2.1
  obtain ⟨k, hk, upper⟩ := (hκ.range_bounded_of_domain_mem hZF I hωκ ff hd).exists_bound
  obtain ⟨j, hj, above⟩ := b.cofinal k hk
  refine ⟨j, hj, fun n i hni => (ls i j).mpr ⟨(hf.bound_l hni).2, hj, b.forward_l h (hf.bound_l hni).2 hj ?_⟩⟩
  rcases upper i ((hd i).mpr ⟨n, hni⟩) with rfl | hik
  · exact above
  · rcases above with rfl | hkj
    · exact Or.inr hik
    · exact Or.inr ((h.ordinal.mem (b.subset j hj)).transitive k hkj i hik)

/-- 证书记录实际树枝、实际带标号系统及其良基商；所有字段由下面的构造给出。 -/
def It_wf_branch_d (hZF : M.Models ZF) (ω α T Q G B : M.Domain) : Prop := It_branch_d α T B ∧
  ∃ L A p H R q c C V,
    (∀ i j, Rd_entry_d i j L ↔ M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T) ∧
    It_system_d B L Q G A p H R ∧ Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω L A p H R ∧
    Di_limit_d A p H R q C V ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V ∧ Wf_rel_d C V

theorem it_sigma_branch_l (hZF : M.Models ZF) {ω α κ T Q G B : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (b : It_branch_d α T B)
    (hκ : M.IsCofinality (kp_pair_l (ZF.modelsKP hZF)) κ α) (hωκ : M.mem ω κ)
    (dc : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (models : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) :
    It_wf_branch_d hZF ω α T Q G B := by
  obtain ⟨i, hi⟩ := hκ.hasCofinalSequence.elim fun _ hf => hf.1.2.1
  obtain ⟨j, hj, _⟩ := b.cofinal i hi
  obtain ⟨L, A, p, H, R, q, c, C, V, ls, s, elem, limit, model⟩ := it_branch_data_l hZF hω h b ⟨j, hj⟩
  obtain ⟨D, hq⟩ := h.family_l hZF
  exact ⟨b, L, A, p, H, R, q, c, C, V, ls, s, elem, limit, model,
    di_sigma_wf_l hZF hω dc s.system (b.sigma_l hZF h.order hκ hωκ ls) (s.tags.wf_l hZF hq models) limit⟩

end YesMetaZFC.SetTheory.LargeCardinal

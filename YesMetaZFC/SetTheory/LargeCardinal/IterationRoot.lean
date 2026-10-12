import YesMetaZFC.SetTheory.LargeCardinal.IterationTreeExtend

/-! # 单根迭代树及恒等延长的实际实例

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
  obtain ⟨X, R, K, code, source⟩ := ready
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨α, hα, hαω⟩ := source.omega.1.2 z hzω
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
  obtain ⟨e, he, es⟩ := smap_identity_l I hZF (c := c) (X := X) source.omega
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
  have order : It_order_d α T := ⟨source.omega.members_areOrdinals hZF α hαω, ht.1.1,
    fun i j hij => ⟨ht.input_mem_of_pairMember hij, ht.output_mem_of_pairMember hij⟩,
    fun i hi => (ts i i).mpr ⟨hi, rfl⟩,
    fun i j k hij hjk => (ts i k).mpr ⟨((ts i j).mp hij).1, ((ts i j).mp hij).2.trans ((ts j k).mp hjk).2⟩,
    fun i j hij => Or.inl ((ts i j).mp hij).2,
    fun i j k hik hjk => Or.inl ((ts i j).mpr ⟨((ts i k).mp hik).1, ((ts i k).mp hik).2.trans ((ts j k).mp hjk).2.symm⟩),
    fun i j hj hs => (impossible i j hj hs).elim, fun i hi hl => (no_limit i hi hl).elim⟩
  have diagram : It_diagram_d hZF ω α T Q G := by
    refine ⟨order, hQ.1, hQ.2.1, fun i b hb => ?_, hG.1, hG.2.1, ?_, ?_, ?_⟩
    · exact ((qs i b).mp hb).2.symm ▸ ⟨X, R, code.1⟩
    · intro i j f b Y S d Z V hf hb hd mb md
      have eb := ((qs i b).mp hb).2
      have ed := ((qs j d).mp hd).2
      have ef := ((maps i j f).mp hf).2
      subst b d f
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I mb code.1
      obtain ⟨rfl, rfl⟩ := smdl_unique_l I md code.1
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
  refine ⟨z, α, T, Q, G, hz, hα, ⟨source.omega, diagram, ?_, ?_,
    ⟨fun p hp => (hz p hp).elim, fun i x _ hix _ => (empty i x hix).elim⟩, ?_,
    fun i j hj hs => (impossible i j hj hs).elim, fun i hi hl => (no_limit i hi hl).elim⟩⟩
  · intro z' hz'
    have eq := hZF.1.eq_of_same_members z' z fun x => iff_of_false (hz' x) (hz x)
    exact (qs z' c).mpr ⟨eq.symm ▸ hα.predecessor_mem, rfl⟩
  · intro i b hb
    exact ((qs i b).mp hb).2.symm ▸ (show It_source_d hZF ω c from ⟨X, R, K, code, source⟩)
  · intro i
    exact ⟨fun ⟨x, hx⟩ => (empty i x hx).elim, fun ⟨j, hj, hs⟩ => (impossible i j hj hs).elim⟩

theorem it_pad_l {ω c₀ α ξ T Q G E : M.Domain} (tree : It_tree_d hZF ω c₀ α T Q G E)
    (hα : M.SuccessorOf α ξ) : ∃ β U Q' G' E' c j, M.SuccessorOf β α ∧ It_tree_d hZF ω c₀ β U Q' G' E' ∧
      It_extension_d α ξ ξ T Q G E β U Q' G' E' ∧ Rd_entry_d ξ c Q ∧ Rd_entry_d α c Q' ∧ It_map_d G' ξ α j ∧
      (∀ x y, Rd_entry_d x y j → x = y) ∧ (∀ i f, Rd_entry_d i f E → Rd_entry_d i f E') ∧
      ∀ p, Rd_entry_d ξ p E' → ∀ x, ¬ M.mem x p := by
  obtain ⟨c, hc⟩ := (tree.diagram.model_domain ξ).mp hα.predecessor_mem
  obtain ⟨X, R, K, code, source⟩ := tree.sources ξ c hc
  obtain ⟨j, hj, js⟩ := smap_identity_l I hZF (c := c) (X := X) tree.omega
  obtain ⟨p, hp⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have idj x y (hxy : Rd_entry_d x y j) := ((js x y).mp hxy).2
  obtain ⟨β, U, Q', G', E', hβ, h', us, qs, gs, es, edge⟩ := it_tree_extend_l hZF tree hα hc hc code.1 code.1 hj
    ⟨X, R, K, code, source⟩ (Or.inl ⟨hp, rfl, rfl, idj⟩)
  refine ⟨β, U, Q', G', E', c, j, hβ, h', ⟨hβ, us, fun i a hi => (qs i a).mpr (Or.inl hi), gs,
    fun i a hi => (es i a).mpr (Or.inl hi), ?_⟩, hc, (qs α c).mpr (Or.inr ⟨rfl, rfl⟩), edge, idj,
    fun i f hi => (es i f).mpr (Or.inl hi), ?_⟩
  · exact fun i a hi => (es i a).trans ⟨fun hh => hh.elim id (fun hh => (hi hh.1).elim), Or.inl⟩
  · intro q hq
    have eq := h'.move_function.2 ξ q p hq ((es ξ p).mpr (Or.inr ⟨rfl, rfl⟩))
    exact eq.symm ▸ hp

end YesMetaZFC.SetTheory.LargeCardinal

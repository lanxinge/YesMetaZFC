import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEmbeddingTree
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttemptDecode
import YesMetaZFC.Model.SetTheory.Internal.SourceFunctionSize

/-! # 源内可数域上的完整初等嵌入回收

内部单射给出带默认值的实际枚举，尝试树给出源内总枝，复合图解码为
完整初等嵌入。最后连同嵌入图到 ω 的源内单射一起返回，保留指定限制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.countable_enum_l {ω κ K Z W A ι : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (hA : M.mem A Z) (hιZ : M.mem ι Z)
    (hι : M.IsSetInjectionFromTo I ι A ω) (hne : ∃ a, M.mem a A) :
    ∃ e, M.mem e Z ∧ Fn0_d ω A e ∧ ∀ x i, Rd_entry_d x i ι → Rd_entry_d i x e := by
  classical
  obtain ⟨a, ha⟩ := hne
  obtain ⟨c, hc⟩ := source.code
  let ρ : Env M 3 := ⟨Fin.cases A (Fin.cases ι (fun _ => a)), fun _ => a⟩
  let φ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 2)) (.disj (rd_entry0_m .newest (.bound 1) (.bound 3))
      (.conj (.neg (Formula.existsMem (.bound 2) (rd_entry0_m .newest (.bound 2) (.bound 4))))
        (Formula.extensionalEq .newest (.bound 4)))) }
  have sat i x : φ.denote ρ i x ↔ M.mem x A ∧
      (Rd_entry_d x i ι ∨ (¬ (∃ y, M.mem y A ∧ Rd_entry_d y i ι) ∧ x = a)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_existsMem_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨e, heZ, he, select⟩ := sc_uniform_source_l hZF source.omega source.transitive hc source.theory φ
    (.conj (.mem _ _) (.disj (rd_entry0_delta_l ..)
      (.conj (.neg (.existsMem _ (rd_entry0_delta_l ..))) (.atom _ _ _))))
    ρ (Fin.cases hA (Fin.cases hιZ (fun _ => source.transitive A hA a ha))) source.omega_mem hA (fun i _ => by
      by_cases h : ∃ x, M.mem x A ∧ Rd_entry_d x i ι
      · obtain ⟨x, hx, hxi⟩ := h
        exact ⟨x, hx, (sat i x).mpr ⟨hx, Or.inl hxi⟩⟩
      · exact ⟨a, ha, (sat i a).mpr ⟨ha, Or.inr ⟨h, rfl⟩⟩⟩)
  refine ⟨e, heZ, he, fun x i hxi => ?_⟩
  obtain ⟨y, _, hiy⟩ := he.2.1 i (hι.1.output_mem_of_pairMember hxi)
  rcases ((sat i y).mp (select i y hiy)).2 with hyi | hy
  · exact (hι.2 y x i hyi hxi) ▸ hiy
  · exact (hy.1 ⟨x, hι.1.input_mem_of_pairMember hxi, hxi⟩).elim

/-- 外部完整初等嵌入在源内可数域上的回收；指定图、嵌入图与其可数性都有实际集合见证。 -/
theorem Ep_source_d.countable_embedding_l {ω κ K Z W c d A R B S τ ι j : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (branches : Sc_branch_d ω Z) (hA : M.mem A Z) (hR : M.mem R Z)
    (hB : M.mem B Z) (hS : M.mem S Z) (hτ : M.mem τ Z) (hιZ : M.mem ι Z)
    (hm : Smdl_d I c A R) (hn : Smdl_d I d B S) (hι : M.IsSetInjectionFromTo I ι A ω)
    (hj : Smap_d I ω c d A B j) (hτj : ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y j) :
    ∃ k η, M.mem k Z ∧ M.mem η Z ∧ Smap_d I ω c d A B k ∧ M.IsSetInjectionFromTo I η k ω ∧
      ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y k := by
  obtain ⟨e, heZ, he, hsect⟩ := source.countable_enum_l hZF hA hιZ hι hm.2.1
  obtain ⟨g, hgZ, hg, branch⟩ := source.at_branch_l hZF branches hA hR hB hS heZ hτ hm hn hj he hτj
  obtain ⟨c₀, hc⟩ := source.code
  obtain ⟨k, hkZ, comp⟩ := sc_compose_l hZF source.omega source.transitive hc source.theory
    hA source.omega_mem hιZ hgZ (fn0_of_function_l (ZF.modelsKP hZF) hι.1) (hg.mono_target_l (source.transitive B hB))
  have comp := comp.retarget_l hg
  obtain ⟨hk, prescribed, _⟩ := at_decode_l hZF source.omega hm hn he
    (fn0_of_function_l (ZF.modelsKP hZF) hι.1) hsect hg comp branch
  obtain ⟨η, hηZ, hη⟩ := sc_graph_numbering_l hZF source.omega source.transitive hc source.theory
    source.omega_mem hA hB hιZ hkZ.1 hι comp.1
  exact ⟨k, η, hkZ.1, hηZ, hk, hη, fun x y h => prescribed x y
    (hj.1.1.input_mem_of_pairMember (hτj x y h)) (hj.1.1.output_mem_of_pairMember (hτj x y h)) h⟩

/-- 集合隶属结构的直接入口，关系码的源内性自动构造。 -/
theorem Ep_source_d.countable_membership_l {ω κ K Z W c d A R B S τ ι j : M.Domain}
    (source : Ep_source_d hZF ω κ K Z W) (branches : Sc_branch_d ω Z) (hA : M.mem A Z) (hB : M.mem B Z)
    (hτ : M.mem τ Z) (hιZ : M.mem ι Z) (hm : Smem_d I c A R) (hn : Smem_d I d B S)
    (hι : M.IsSetInjectionFromTo I ι A ω) (hj : Smap_d I ω c d A B j)
    (hτj : ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y j) :
    ∃ k η, M.mem k Z ∧ M.mem η Z ∧ Smap_d I ω c d A B k ∧ M.IsSetInjectionFromTo I η k ω ∧
      ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y k :=
  source.countable_embedding_l hZF branches hA (source.membership_relation_l hZF hA hm)
    hB (source.membership_relation_l hZF hB hn) hτ hιZ hm.1 hn.1 hι hj hτj

end YesMetaZFC.SetTheory.LargeCardinal

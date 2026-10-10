import YesMetaZFC.Model.Forcing.Proper.Generic.Countable
import YesMetaZFC.Model.Forcing.Internal.Ground.FiniteSequence
import YesMetaZFC.SetTheory.Card.FiniteSequenceLift
import YesMetaZFC.SetTheory.CountableChain
import YesMetaZFC.Model.Forcing.Internal.Names.Sequence

/-! # N[G] 参数列的内部有限名称提升

求值满射先在扩张中提升整个有限列，再由地有限列空间的满覆盖回拉函数图。
得到的是地模型的实际有限名称列，长度可以外部非标准；逐坐标求值等于原参数列。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
include O hZF hU

/-- N[G] 中任意内部有限参数列，都有取值于 N 的实际内部有限名称列。 -/
theorem ng_fseq_l {b N ω} {Y n f : (E).Domain} (hb : U b) (hω : M.IsOmega ω)
    (hY : ∀ x, x ∈ Y ↔ Ng_mem_d M B R z U N x)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M B R z U t (e a))
    (hn : n ∈ e ω) (hf : (E).IsSetFunctionFromTo J f n Y) :
    ∃ m t, M.mem m ω ∧ e m = n ∧ M.IsSetFunctionFromTo I t m N ∧
      ∀ i s, Entry_d M i s t → Name_d M B s ∧
        ∀ x, Entry_d E (e i) x f → Qval_d M B R z U s x := by
  have hE := preserves_zf_l O hZF hU
  have hw : (E).IsOmega (e ω) := image_omega_l (hEN := hE.1) e hi he hZF
    (internal_foundation_l O hZF hU) hω (fun T => KP.difference_exists_d (ZF.modelsKP hE) T (e ω))
  obtain ⟨S, hS⟩ := ng_source_exists_l M hZF B N
  obtain ⟨F, _, hF⟩ := ng_graph_l O hZF hU (hU.proper b hb).1
    (fun s hs => ((hS s).mp hs).2) e hv
  have hs : (E).IsSetSurjectiveOnto J F (e S) Y := by
    intro y hy
    obtain ⟨s, hs, hv⟩ := (hY y).mp hy
    have hsS := (hS s).mpr ⟨hs, qval_name_l hv⟩
    exact ⟨e s, (he S (e s)).mpr ⟨s, hsS, rfl⟩, (hF (e s) y).mpr ⟨s, hsS, rfl, hv⟩⟩
  obtain ⟨r, hr, hc⟩ := ZF.fseq_lift_l J hE hw hs hn hf
  obtain ⟨T, hT⟩ := ZF.fseq_space_exists_l I hZF hω S
  have hT' := image_fseq_l hZF hE e hi he hω hw hT
  obtain ⟨t, htT, htr⟩ := (he T r).mp ((hT' r).mpr ⟨n, hn, hr⟩)
  obtain ⟨m, hm, ht⟩ := (hT t).mp htT
  have ht' := image_function_l (hEN := extension_ext_l O hZF hU) (hPN := internal_pair_l O hZF hU) e hi he ht
  have hmn : e m = n := ht'.2.1.eq hE.1 (htr.symm ▸ hr.2.1)
  refine ⟨m, t, hm, hmn, ht.mono_target_l I (fun s hs => ((hS s).mp hs).1), fun i s his => ?_⟩
  refine ⟨((hS s).mp (ht.output_mem_of_pairMember his)).2, fun x hix => ?_⟩
  have hir := htr ▸ (image_entries_l e he ht.1.1 (e i) (e s)).mpr ⟨i, s, his, rfl, rfl⟩
  obtain ⟨a, _, has, hax⟩ := (hF (e s) x).mp (hc (e i) (e s) x hir hix)
  exact hi has ▸ hax

/-- 回拉后整列装配为一个名称，其泛型值就是原内部有限参数图。 -/
theorem ng_fseq_name_l {b N ω} {Y n f : (E).Domain} (hb : U b) (hω : M.IsOmega ω)
    (hY : ∀ x, x ∈ Y ↔ Ng_mem_d M B R z U N x)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M B R z U t (e a))
    (hn : n ∈ e ω) (hf : (E).IsSetFunctionFromTo J f n Y) :
    ∃ m s t, M.mem m ω ∧ e m = n ∧ M.IsSetFunctionFromTo I s m N ∧
      Nseq_d M B b s t ∧ Qval_d M B R z U t f := by
  obtain ⟨m, s, hm, hmn, hs, hc⟩ := ng_fseq_l O hZF hU hb hω hY e hi he hv hn hf
  obtain ⟨t, ht⟩ := nseq_exists_l M hZF (hU.proper b hb).1 hs (fun i a ha => (hc i a ha).1)
  obtain ⟨v, htv⟩ := name_value_l (R := R) (z := z) (U := U) ht.1
  obtain ⟨hr, hgraph⟩ := nseq_value_l O hZF hU (hU.proper b hb).1 ht htv e hv
  have hEq : v = f := by
    apply entry_ext_l E (extension_ext_l O hZF hU) hr hf.1.1
    intro x y
    rw [hgraph x y]
    constructor
    · rintro ⟨i, a, hia, rfl, hay⟩
      have hin : e i ∈ n := hmn ▸ (image_member_l e hi he).mpr (hs.input_mem_of_pairMember hia)
      obtain ⟨y', _, hiy⟩ := hf.2.2 (e i) hin
      exact qval_unique_l ((hc i a hia).2 y' hiy) hay ▸ hiy
    · intro hxy
      obtain ⟨i, him, rfl⟩ := (he m x).mp (hmn.symm ▸ hf.input_mem_of_pairMember hxy)
      obtain ⟨a, _, hia⟩ := hs.2.2 i him
      exact ⟨i, a, hia, rfl, (hc i a hia).2 y hxy⟩
  exact ⟨m, s, t, hm, hmn, hs, ht, hEq ▸ htv⟩

end YesMetaZFC.Model.Forcing.Internal

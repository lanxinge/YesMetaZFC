import YesMetaZFC.SetTheory.CumulativeCertificate
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 传递载体中的累积层证书及其秩覆盖绝对性

相对证书只检查载体内的子集。若载体已包含 Vα 的全部成员，则历史上的
逐层比较恢复真实 Vα；证明不预设载体满足 ZF。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Vr_d (Z α V : M.Domain) : Prop := ∃ B F, M.mem B Z ∧ M.mem F Z ∧ ∀ t, M.mem t Z → Vc_d α V B F t

theorem vr_source_l (hZF : M.Models ZF) {δ X α V : M.Domain}
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (hα : M.mem α δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) α V) :
    ∃ B F, M.mem B X ∧ M.mem F X ∧ (∀ t, Vc_d α V B F t) ∧
      ∀ β W, Rd_entry_d β W F → V_d (kp_pair_l (ZF.modelsKP hZF)) β W := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := v_transitive_l I hX
  have hVX := ZF.v_mem_l I hZF hV hX hα
  obtain ⟨F, hf, step⟩ := hV
  have hV : V_d I α V := ⟨F, hf, step⟩
  have fn : M.IsSetFunctionFromTo I F α V := ⟨hf.1.2.1, hf.1.2.2, fun β hβ => by
    obtain ⟨W, hw⟩ := (hf.1.2.2 β).mp hβ
    exact ⟨W, ZF.v_mem_l I hZF (hf.recursionValue_of_pairMember hβ hw) hV hβ, hw⟩⟩
  obtain ⟨B, hb⟩ := ZF.exists_range_of_setFunction hZF I fn.1 fn.2.1
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF V
  have hBX : M.mem B X := ht P (v_power_mem_l I hX hδ hVX hP) B
    ((hP B).mpr fun w hw => ((hb w).mp hw).elim fun _ hp => fn.output_mem_of_pairMember hp)
  obtain ⟨Z, hZX, hαZ, hVZ⟩ := v_joint_bound_l I hX (ZF.v_ordinal_mem_l I hZF hX hα) hVX
  have hFX := v_relation_mem_l I hX hδ hZX (F := F) (fun p hp => by
    obtain ⟨β, W, hpair⟩ := fn.1.1 p hp
    exact ⟨β, hαZ β (fn.input_mem_of_pairMember ⟨p, hpair, hp⟩), W,
      hVZ W (fn.output_mem_of_pairMember ⟨p, hpair, hp⟩), hpair⟩)
  have fnB : Fn0_d α B F := fn0_of_function_l (ZF.modelsKP hZF) ⟨fn.1, fn.2.1, fun β hβ =>
    ((fn.2.1 β).mp hβ).imp fun W hw => ⟨(hb W).mpr ⟨β, hw⟩, hw⟩⟩
  refine ⟨B, F, hBX, hFX, fun t => ⟨hf.1.1, fnB, ?_, ?_⟩,
    fun β W hw => hf.recursionValue_of_pairMember (fn.input_mem_of_pairMember hw) hw⟩
  · intro β hβ W _ hw
    obtain ⟨G, hg, hs⟩ := hf.2 β hβ W hw
    exact (hs t).trans ⟨fun ⟨γ, U, hu, ht⟩ => ⟨γ, ((hg.2 γ U).mp hu).1, U,
      (hb U).mpr ⟨γ, ((hg.2 γ U).mp hu).2⟩, ((hg.2 γ U).mp hu).2, ht⟩,
      fun ⟨γ, hγ, U, _, hu, ht⟩ => ⟨γ, U, (hg.2 γ U).mpr ⟨hγ, hu⟩, ht⟩⟩
  · exact (step t).trans ⟨fun ⟨β, W, hw, ht⟩ =>
      ⟨β, fn.input_mem_of_pairMember hw, W, (hb W).mpr ⟨β, hw⟩, hw, ht⟩,
      fun ⟨β, _, W, _, hw, ht⟩ => ⟨β, W, hw, ht⟩⟩

/-- 已覆盖的秩层可同任意更长相对历史比较；不要求截断历史自身属于载体。 -/
theorem vr_compare_l (hZF : M.Models ZF) {Z η B F α V W : M.Domain} (hZ : M.TransitiveSet Z)
    (hBZ : M.MemberSubset B Z) (fn : Fn0_d η B F) (hαη : M.MemberSubset α η)
    (hWZ : M.mem W Z) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) α V) (hVZ : M.MemberSubset V Z)
    (history : ∀ β, M.mem β α → ∀ H, Rd_entry_d β H F → ∀ t, M.mem t Z → Vc_step_d β B F H t)
    (root : ∀ t, M.mem t Z → Vc_step_d α B F W t) : W = V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have compare β U (hβ : M.IsOrdinal β) (sub : M.MemberSubset β α) (hUZ : M.mem U Z)
      (step : ∀ t, M.mem t Z → Vc_step_d β B F U t)
      (prev : ∀ γ, M.mem γ β → ∀ H, Rd_entry_d γ H F → V_d I γ H) : V_d I β U := by
    obtain ⟨T, hT⟩ := ZF.v_exists_l I hZF hβ
    have eq : U = T := hZF.1.eq_of_same_members U T (fun x => ⟨fun hx => by
      obtain ⟨γ, hγ, H, _, hγH, hxH⟩ := (step x (hZ U hUZ x hx)).mp hx
      exact (ZF.v_unfold_l I hZF hT x).mpr ⟨γ, H, hγ, prev γ hγ H hγH, hxH⟩,
      fun hx => by
        obtain ⟨γ, H, hγ, hH, hxH⟩ := (ZF.v_unfold_l I hZF hT x).mp hx
        obtain ⟨H', hh, hγH'⟩ := fn.2.1 γ (hαη γ (sub γ hγ))
        have eq := ZF.v_unique_l I hZF hH (prev γ hγ H' hγH')
        exact (step x (hVZ x (ZF.v_mono_l I hZF hT hV sub x hx))).mpr ⟨γ, hγ, H', hh, hγH', eq ▸ hxH⟩⟩)
    exact eq.symm ▸ hT
  let ρ := (⟨fun _ => α, fun _ => α⟩ : Env M 1).push F
  let φ : UnarySchema 2 := { body := .imp (.mem .newest (.bound 2)) (.forallE
    (.imp (rd_entry_m (.bound 1) .newest (.bound 2)) (v_m kpair_convention_l (.bound 1) .newest))) }
  have sat β : φ.denote ρ β ↔ M.mem β α → ∀ H, Rd_entry_d β H F → V_d I β H := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, rd_entry_sat_l hZF.1, v_sat_l I hZF.1]; rfl
  have all β (hβ : M.mem β α) : ∀ H, Rd_entry_d β H F → V_d I β H := by
    apply (sat β).mp (ZF.mem_ind_l M hZF I φ ρ ?_ β) hβ
    intro β ih
    apply (sat β).mpr
    intro hβ H hβH
    exact compare β H ((v_ordinal_l I hV).mem hβ) ((v_ordinal_l I hV).transitive β hβ)
      (hBZ H (fn.bound_l hβH).2)
      (history β hβ H hβH)
      (fun γ hγ => (sat γ).mp (ih γ hγ) ((v_ordinal_l I hV).transitive β hβ γ hγ))
  exact ZF.v_unique_l I hZF (compare α W (v_ordinal_l I hV) (fun _ h => h) hWZ
    root all) hV

/-- 在已覆盖的秩层内，相对幂集递归没有遗漏真实子集。 -/
theorem vr_agree_l (hZF : M.Models ZF) {Z α V W : M.Domain} (hZ : M.TransitiveSet Z)
    (hWZ : M.mem W Z) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) α V) (hVZ : M.MemberSubset V Z)
    (hW : Vr_d Z α W) : W = V := by
  obtain ⟨B, F, hBZ, _, cert⟩ := hW
  have fn := (cert W hWZ).2.1
  exact vr_compare_l hZF hZ (hZ B hBZ) fn (fun _ h => h) hWZ hV hVZ
    (fun β hβ H hβH t ht => (cert t ht).2.2.1 β hβ H (fn.bound_l hβH).2 hβH)
    (fun t ht => (cert t ht).2.2.2)

end YesMetaZFC.SetTheory

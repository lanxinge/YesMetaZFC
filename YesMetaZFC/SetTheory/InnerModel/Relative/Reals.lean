import YesMetaZFC.SetTheory.InnerModel.Relative.Model
import YesMetaZFC.SetTheory.Descriptive.Space
import YesMetaZFC.SetTheory.TransitiveClosure

/-! # L(ℝ) 的实际构造与实数保持

实数固定为 Kuratowski 编码的内部 ω→ω 函数。起层为 TC({ℝ})，
继承相对 Jensen 递归；全部序数和原实数都属于并类。背景仅需 ZF。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Descriptive
universe u
variable {M : Structure.{u}} (S : M.Domain) (hZF : M.Models ZF) (hS : M.TransitiveSet S)

local notation "Nₛ" => la_model_l S (ZF.models_kpi_l hZF)

/-- 函数图的绝对性通过已有的 Δ₀ 有界图公式取得。 -/
theorem la_function_l (A B F : (Nₛ).Domain) :
    (Nₛ).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF hS))) F A B ↔
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) F.val A.val B.val := by
  let ρ : Env Nₛ 3 := ⟨Fin.cases F (Fin.cases B (fun _ => A)), fun _ => A⟩
  have h := la_model_delta_l S (ZF.models_kpi_l hZF) hS (fn0_delta_l (.bound 2) (.bound 1) (.bound 0)) ρ
  rw [fn0_sat_l (la_model_ext_l S (ZF.models_kpi_l hZF) hS), fn0_sat_l hZF.1] at h
  exact ⟨fun hf => fn0_function_l (ZF.modelsKP hZF)
    (h.mp (fn0_of_function_l (ZF.modelsKP (la_model_zf_l S hZF hS)) hf)),
    fun hf => fn0_function_l (ZF.modelsKP (la_model_zf_l S hZF hS))
      (h.mpr (fn0_of_function_l (ZF.modelsKP hZF) hf))⟩

/-- 最小归纳集在相对内模型与背景中相同，包括非标准自然数。 -/
theorem la_omega_l {ω : M.Domain} (hω : M.IsOmega ω) :
    (Nₛ).IsOmega ⟨ω, la_ordinal_l S (ZF.models_kpi_l hZF) hS (hω.isOrdinal hZF)⟩ := by
  let hM := ZF.models_kpi_l hZF
  have same (a b : (Nₛ).Domain) : (Nₛ).SameMembers a b ↔ a.val = b.val :=
    ⟨fun h => congrArg Subtype.val ((la_model_ext_l S (ZF.models_kpi_l hZF) hS).eq_of_same_members a b h),
      fun h => (show a = b from Subtype.ext h) ▸ (fun _ => Iff.rfl)⟩
  have hL := la_ordinal_l S (ZF.models_kpi_l hZF) hS (hω.isOrdinal hZF)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨e, he, heω⟩ := hω.1.1
    exact ⟨⟨e, la_transitive_l S hM hS hL heω⟩, fun z => he z.val, heω⟩
  · intro x hx
    obtain ⟨s, hs, hsω⟩ := hω.1.2 x.val hx
    exact ⟨⟨s, la_transitive_l S hM hS hL hsω⟩,
      fun z => (hs z.val).trans (or_congr_right
        ⟨fun h v => h v.val, fun h => (same z x).mp h ▸ (fun _ => Iff.rfl)⟩), hsω⟩
  · intro T hT x hx
    apply hω.2 T.val (show M.IsInductive T.val from ?_) x.val hx
    refine ⟨?_, fun a ha => ?_⟩
    · obtain ⟨e, he, heT⟩ := hT.1
      exact ⟨e.val, fun z hz => he ⟨z, la_transitive_l S hM hS e.property hz⟩ hz, heT⟩
    · let a' : (Nₛ).Domain := ⟨a, la_transitive_l S hM hS T.property ha⟩
      obtain ⟨s, hs, hsT⟩ := hT.2 a' ha
      refine ⟨s.val, fun z => ⟨fun hz => ?_, fun hz => ?_⟩, hsT⟩
      · let z' : (Nₛ).Domain := ⟨z, la_transitive_l S hM hS s.property hz⟩
        exact ((hs z').mp hz).imp_right (fun h => by
          have he : z = a := (same z' a').mp h
          subst z
          exact fun _ => Iff.rfl)
      · rcases hz with hz | hz
        · exact (hs ⟨z, la_transitive_l S hM hS a'.property hz⟩).mpr (Or.inl hz)
        · have he := hZF.1.eq_of_same_members z a hz
          exact he.symm ▸ hs.predecessor_mem

omit S hS in
def Lr_seed_d (ω B T : M.Domain) : Prop :=
  Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B ∧ Tc_d B T

omit S hS in
theorem lr_seed_exists_l : ∃ ω B T, Lr_seed_d hZF ω B T := by
  obtain ⟨ω, hω⟩ := ZF.exists_omega hZF
  obtain ⟨B, hB⟩ := baire_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω
  obtain ⟨T, hT⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hZF)) hZF B
  exact ⟨ω, B, T, hB, hT⟩

omit hS in
/-- 原 Baire 空间作为集合及其全部成员进入 L(ℝ)，且仍是内部的完整 Baire 空间。 -/
theorem lr_reals_l {ω B : M.Domain} (h : Lr_seed_d hZF ω B S) :
    ∃ w r : (Nₛ).Domain, w.val = ω ∧ r.val = B ∧
      Baire_d (kp_pair_l (ZF.modelsKP (la_model_zf_l S hZF h.2.1))) w r := by
  let w : (Nₛ).Domain := ⟨ω, la_ordinal_l S (ZF.models_kpi_l hZF) h.2.1 (h.1.1.isOrdinal hZF)⟩
  let r : (Nₛ).Domain := ⟨B, la_transitive_l S (ZF.models_kpi_l hZF) h.2.1
    (la_seed_l S (ZF.models_kpi_l hZF)) h.2.2.1⟩
  exact ⟨w, r, rfl, rfl, la_omega_l S hZF h.2.1 h.1.1,
    fun f => (h.1.2 f.val).trans (la_function_l S hZF h.2.1 w w f).symm⟩

end YesMetaZFC.SetTheory.InnerModel.Relative

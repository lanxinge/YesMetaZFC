import YesMetaZFC.Model.Forcing.Proper.Syntax
import YesMetaZFC.Model.Forcing.Proper.Master.CCC

/-! # CCC 的 properness 与实际主条件装配

可数主条件闭包给出无界性。内部递增序列的并保持可数性，每个稠密集及其
预稠密见证已出现在某个成员中，因此主条件集合族闭。由此得到实际 club。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z ω : M.Domain}

/-- 任意 CCC 偏序满足原公式的 club 主条件 properness。 -/
theorem ccc_proper_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hω : M.IsOmega ω)
    (hc : Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z) :
    Proper_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R z := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro X hBX
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF X
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push ω
  let φ : UnarySchema 4 := {
    body := .conj (Formula.cardinalLessOrEqual kpair_convention_l .newest (.bound 1))
      (Formula.forallMem (.bound 4) (.imp (.neg (Formula.extensionalEq .newest (.bound 3)))
        (mstr_m (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest))) }
  have hφ N : φ.denote ρ N ↔ M.CardinalLessOrEqual I N ω ∧
      ∀ p, M.mem p B → p ≠ z → Mstr_d M B R z N p := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_cardinalLessOrEqual_iff I hZF.1,
      Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, mstr_sat_l M hZF.1]
    rfl
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF φ ρ P
  have hC N : M.mem N C ↔ M.MemberSubset N X ∧ M.CardinalLessOrEqual I N ω ∧
      ∀ p, M.mem p B → p ≠ z → Mstr_d M B R z N p := by
    exact (hC' N).trans (and_congr (hP N) (hφ N))
  refine ⟨C, ⟨fun N hN => ⟨((hC N).mp hN).1, ((hC N).mp hN).2.1⟩, ?_, ?_⟩,
    fun N hN p _ hp hz => ⟨p, below_refl_l O hp hz, ((hC N).mp hN).2.2 p hp hz⟩⟩
  · intro A hAX hA
    obtain ⟨N, hAN, hNX, hn, hm⟩ := ccc_mstr_hull_l O hZFC hω hc hBX hAX hA
    exact ⟨N, (hC N).mpr ⟨hNX, hn, hm⟩, hAN⟩
  · intro f N hf _ hu
    apply (hC N).mpr
    refine ⟨fun x hx => ?_, ZFC.cc_union_countable_l I hZFC hω hf hu (fun A hA => ((hC A).mp hA).2.1),
      fun p hp hz => ⟨hp, hz, fun D hDN hd r hr => ?_⟩⟩
    · obtain ⟨i, A, hi, hxA⟩ := (hu x).mp hx
      exact ((hC A).mp (hf.output_mem_of_pairMember hi)).1 x hxA
    · obtain ⟨i, A, hi, hDA⟩ := (hu D).mp hDN
      obtain ⟨s, hsD, hsA, hrs⟩ := (((hC A).mp (hf.output_mem_of_pairMember hi)).2.2 p hp hz).2.2 D hDA hd r hr
      exact ⟨s, hsD, (hu s).mpr ⟨i, A, hi, hsA⟩, hrs⟩

/-- properness 自动取得含给定可数种子的可数集合及给定条件的主加强。 -/
theorem proper_mstr_l (hZF : M.Models ZF) (hω : M.IsOmega ω)
    (h : Proper_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω B R z)
    {A p} (hA : M.CardinalLessOrEqual (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) A ω)
    (hp : M.mem p B) (hz : p ≠ z) : ∃ N q,
    M.MemberSubset A N ∧ M.mem p N ∧
    M.CardinalLessOrEqual (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) N ω ∧
    Below_d M B R z q p ∧ Mstr_d M B R z N q := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨S, hS⟩ := KP.exists_insert (ZF.modelsKP hZF) A p
  obtain ⟨X, hX⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B S
  obtain ⟨C, hC, hm⟩ := h X (fun x hx => (hX x).mpr (Or.inl hx))
  obtain ⟨N, hN, hSN⟩ := hC.unbounded S (fun x hx => (hX x).mpr (Or.inr hx))
    (ZF.countable_insert_l I hZF hω hA hS)
  have hpN := hSN p ((hS p).mpr (Or.inr rfl))
  obtain ⟨q, hqp, hq⟩ := hm N hN p hpN hp hz
  exact ⟨N, q, fun x hx => hSN x ((hS x).mpr (Or.inl hx)), hpN, (hC.members N hN).2, hqp, hq⟩

end YesMetaZFC.Model.Forcing.Internal

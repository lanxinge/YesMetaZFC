import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteWitness
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.Model.SetTheory.Internal.Skolem

/-! # 小壳公式所量化的全部内部代码

源中的代码集与有限参数空间按原公式读取。合法程序和有限函数的实际
源内存在性排除相对量词遗漏背景内部非标准有限对象的可能。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.codes_sat_l {ω κ K Z W : M.Domain} (source : Ep_source_d hZF ω κ K Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w C : Term d)
    (hw : (w.eval ρ).val = ω) : Formula.satisfies ρ (sh_codes_m w C) ↔ Scode_d I ω (C.eval ρ).val := by
  have prog {e} (η : Env (rt_model_l Z hz) e) (w b l L F : Term e) :
      Formula.satisfies η (fb_program_m w b l L F) ↔
        Fb_program_d (ZF.modelsKP hZF) (w.eval η).val (b.eval η).val (l.eval η).val (L.eval η).val (F.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (fb_program_delta_l w b l L F) η).trans (fb_program_sat_l (ZF.modelsKP hZF) ..)
  have pair {e} (η : Env (rt_model_l Z hz) e) (p a b : Term e) :
      Formula.satisfies η (kpair0_m p a b) ↔ KPair_d M (p.eval η).val (a.eval η).val (b.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive hz (kpair0_delta_l p a b) η).trans (kpair0_sat_l hZF.1 ..)
  simp only [sh_codes_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, prog, pair, Definitional.Term.eval_weaken, hw]
  have cert {a l F r : M.Domain} (h : Sformula_d I ω a l F r) :
      M.mem a Z ∧ ∃ b L, M.mem b Z ∧ M.mem l Z ∧ M.mem L Z ∧ M.mem F Z ∧ M.mem r Z ∧
        Fb_program_d (ZF.modelsKP hZF) ω b l L F := by
    obtain ⟨hF, b, L, hL, program⟩ := source.program_l hZF h.2.1
    have hr := source.transitive ω source.omega_mem r (source.omega.transitive hZF l h.2.1.1 r h.2.2)
    obtain ⟨p, hp, eq⟩ := source.kpair_l hZF hF hr
    exact ⟨kpair_unique_l M hZF.1 eq h.1 ▸ hp, b, L,
      source.transitive ω source.omega_mem b program.1,
      source.transitive ω source.omega_mem l program.2.1, hL, hF, hr, program⟩
  constructor
  · intro h a
    constructor
    · intro ha
      obtain ⟨b, l, L, F, r, program, hr, code⟩ := (h ⟨a, source.transitive _ (C.eval ρ).property a ha⟩).mp ha
      exact ⟨l.val, F.val, r.val, code, (program.read_l hZF source.omega).1, hr⟩
    · rintro ⟨l, F, r, code⟩
      obtain ⟨ha, b, L, hb, hl, hL, hF, hr, program⟩ := cert code
      exact (h ⟨a, ha⟩).mpr ⟨⟨b, hb⟩, ⟨l, hl⟩, ⟨L, hL⟩, ⟨F, hF⟩, ⟨r, hr⟩, program, code.2.2, code.1⟩
  · intro h a
    constructor
    · intro ha
      obtain ⟨l, F, r, code⟩ := (h a.val).mp ha
      obtain ⟨_, b, L, hb, hl, hL, hF, hr, program⟩ := cert code
      exact ⟨⟨b, hb⟩, ⟨l, hl⟩, ⟨L, hL⟩, ⟨F, hF⟩, ⟨r, hr⟩, program, code.2.2, code.1⟩
    · rintro ⟨b, l, L, F, r, program, hr, code⟩
      exact (h a.val).mpr ⟨l.val, F.val, r.val, code, (program.read_l hZF source.omega).1, hr⟩

theorem Ep_source_d.sequences_sat_l {ω κ K Z W : M.Domain} (source : Ep_source_d hZF ω κ K Z W)
    (hz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d) (w A J : Term d)
    (hw : (w.eval ρ).val = ω) :
    Formula.satisfies ρ (sh_sequences_m w A J) ↔ Fseq_space_d I ω (A.eval ρ).val (J.eval ρ).val := by
  have fn (η : Env (rt_model_l Z hz) (d+2)) :
      Formula.satisfies η (fn0_m .newest A.weaken.weaken (.bound 1)) ↔
        Fn0_d (η.bound 0).val (A.weaken.weaken.eval η).val (η.bound 1).val := by
    have tr := (rt_model_delta_l source.transitive hz (fn0_delta_l .newest A.weaken.weaken (.bound 1)) η).trans (fn0_sat_l hZF.1 ..)
    cases A <;> exact tr
  simp only [sh_sequences_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, fn, Definitional.Term.eval_weaken]
  obtain ⟨L, hL, space⟩ := source.sequences.space _ (A.eval ρ).property
  constructor
  · intro h f
    constructor
    · intro hf
      obtain ⟨n, hn, hs⟩ := (h ⟨f, source.transitive _ (J.eval ρ).property f hf⟩).mp hf
      exact ⟨n.val, hw ▸ hn, fn0_function_l (ZF.modelsKP hZF) hs⟩
    · rintro ⟨n, hn, hf⟩
      exact (h ⟨f, source.transitive L hL f ((space f).mpr ⟨n, hn, hf⟩)⟩).mpr
        ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw.symm ▸ hn, fn0_of_function_l (ZF.modelsKP hZF) hf⟩
  · intro h f
    exact (h f.val).trans ⟨fun ⟨n, hn, hf⟩ =>
      ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw.symm ▸ hn, fn0_of_function_l (ZF.modelsKP hZF) hf⟩,
      fun ⟨n, hn, hf⟩ => ⟨n.val, hw ▸ hn, fn0_function_l (ZF.modelsKP hZF) hf⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

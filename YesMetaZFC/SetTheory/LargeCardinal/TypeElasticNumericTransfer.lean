import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticCodeTransfer
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative

/-! # 两个根像之间保持原弹性查询

低自然数程序经共同根往返；含新 κ 常量的实际列图经传递层读取和回收。
两条路线在同一原查询处汇合，不把一边的全称语义直接当成另一边的语义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ee_numeric_transfer_l {ω r B R x X S y Y T π σ C₀ C D A : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mb : Smem_d I r B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω r x B X π) (k : Smap_d I ω r y B Y σ) (hw : M.mem ω B)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ) (ct : M.TransitiveSet C) (dt : M.TransitiveSet D)
    (nc : Nonempty {a // M.mem a C}) (nd : Nonempty {a // M.mem a D})
    (ρ : Env (rt_model_l C nc) 8) (η : Env (rt_model_l D nd) 8)
    (same : ∀ i, (ρ.bound i).val = (η.bound i).val) (hωρ : (ρ.bound 0).val = ω)
    (hA : M.mem A D) (names : Tn_names_d (η.bound 2).val (η.bound 3).val A)
    (valid : Formula.satisfies ρ ee_numeric0_m) : Formula.satisfies η ee_numeric0_m := by
  simp only [ee_numeric0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨l, v, d, e, zg, zh, zi, ze, kw, pg, cg, ph, ch, pi, pair, ci, pe, ce⟩ := valid
  let ε := ρ.push l |>.push v |>.push d |>.push e |>.push zg |>.push zh |>.push zi |>.push ze |>.push kw
  have metaG := pg
  simp only [ee_largest_program_m, Formula.satisfies_bind, ee_largest_program0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at metaG
  have hg : M.mem zg.val ω := hωρ ▸ metaG.1
  have metaI := pi
  simp only [ee_inacc_program_m, Formula.satisfies_bind, ee_inacc_program0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at metaI
  have hi : M.mem zi.val ω := hωρ ▸ metaI.1
  have metaH := ph
  simp only [tg_guard_program_m, Formula.satisfies_bind, tg_guard_program0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at metaH
  have hl : M.mem l.val ω := hωρ ▸ metaH.1
  have hh : M.mem zh.val ω := hωρ ▸ metaH.2.1
  have metaE := pe
  simp only [ee_stretch_program_m, Formula.satisfies_bind, ee_stretch_program0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at metaE
  obtain ⟨hn, hv, hd, he, hz, _⟩ := metaE
  have hn : M.mem (ρ.bound 2).val ω := hωρ ▸ hn
  have hv : M.mem v.val ω := hωρ ▸ hv
  have hd : M.mem d.val ω := hωρ ▸ hd
  have he : M.mem e.val ω := hωρ ▸ he
  have hz : M.mem ze.val ω := hωρ ▸ hz
  have cgM := tt_code0_source_l (ZF.modelsKP hZF) ct nc ε (.bound 11) (.bound 12) (.bound 4) (.bound 13) cg
  have chM := tg_guard_code_source_l (ZF.modelsKP hZF) ct nc ε (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) ch
  have ciM := tt_code2_source_l (ZF.modelsKP hZF) ct nc ε (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) ci
  have ceM := ee_stretch_code_source_l hZF.1 ct nc ε (.bound 9) (.bound 11) (.bound 10) (.bound 7)
    (.bound 6) (.bound 5) (.bound 1) (.bound 16) ce
  have pairM := (rt_model_delta_l ct nc (kpair0_delta_l ..) _).mp pair
  simp only [kpair0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at pairM
  have hwη : (η.bound 0).val = ω := (same 0).symm.trans hωρ
  have hωD : M.mem ω D := hwη ▸ (η.bound 0).property
  have num a (ha : M.mem a ω) := dt ω hωD a ha
  have hkw : M.mem kw.val D := by
    obtain ⟨_, F, _, _, _, _, cp, slots⟩ := ciM
    have hF := (cp.mem_l M dt ((same 6).symm ▸ (η.bound 6).property)).2
    obtain ⟨i, ni⟩ := num_exists_l (ZF.modelsKP hZF) 1
    exact (rd_entry_transitive_l dt hF (slots 1 i ni)).2
  let l' : (rt_model_l D nd).Domain := ⟨l.val, num _ hl⟩
  let v' : (rt_model_l D nd).Domain := ⟨v.val, num _ hv⟩
  let d' : (rt_model_l D nd).Domain := ⟨d.val, num _ hd⟩
  let e' : (rt_model_l D nd).Domain := ⟨e.val, num _ he⟩
  let zg' : (rt_model_l D nd).Domain := ⟨zg.val, num _ hg⟩
  let zh' : (rt_model_l D nd).Domain := ⟨zh.val, num _ hh⟩
  let zi' : (rt_model_l D nd).Domain := ⟨zi.val, num _ hi⟩
  let ze' : (rt_model_l D nd).Domain := ⟨ze.val, num _ hz⟩
  let kw' : (rt_model_l D nd).Domain := ⟨kw.val, hkw⟩
  let υ := η.push l' |>.push v' |>.push d' |>.push e' |>.push zg' |>.push zh' |>.push zi' |>.push ze' |>.push kw'
  have equal : ∀ i, (ε.bound i).val = (υ.bound i).val :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl same))))))))
  have move {a} (φ : Formula 1 a) (hc : φ.FreeClosed) (f : Fin a → Term 17)
      (closed : ∀ i, (f i).freeSupport = [])
      (low : ∀ i, ((f i).eval ε).val = ω ∨ M.mem ((f i).eval ε).val ω)
      (truth : Formula.satisfies ε (φ.bind f)) : Formula.satisfies υ (φ.bind f) := by
    have same' i : ((f i).eval ε).val = ((f i).eval υ).val := by
      have eq := term_closed_env_l (f i) (closed i)
        (ρ := image_env_l (M := rt_model_l C nc) (N := M) Subtype.val ε)
        (η := image_env_l (M := rt_model_l D nd) (N := M) Subtype.val υ) (funext equal)
      simpa only [@eval_image_env_l (rt_model_l C nc) M Subtype.val,
        @eval_image_env_l (rt_model_l D nd) M Subtype.val] using eq
    apply (Formula.satisfies_bind υ f φ).mpr
    exact (smap_numeric_peer_l hZF hω bt xt yt mb mx my j k hw iC iD ct dt nc nd φ hc
      (Definitional.Env.substitute ε f) (Definitional.Env.substitute υ f) same' low).mp ((Formula.satisfies_bind ε f φ).mp truth)
  simp only [ee_numeric0_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff]
  refine ⟨l', v', d', e', zg', zh', zi', ze', kw', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let f : Fin 2 → Term 17 := Fin.cases (.bound 9) (fun _ => .bound 4)
    exact move ee_largest_program0_m ee_largest_program0_closed_l f (Fin.cases rfl (fun _ => rfl))
      (Fin.cases (Or.inl hωρ) (fun _ => Or.inr hg)) pg
  · apply tt_code0_reflect_l (ZF.modelsKP hZF) dt nd hω hωD υ (.bound 11) (.bound 12) (.bound 4) (.bound 13) hA names
    exact (same 2) ▸ (same 3) ▸ (same 4) ▸ cgM
  · let f : Fin 3 → Term 17 := Fin.cases (.bound 9) (Fin.cases (.bound 8) (fun _ => .bound 3))
    exact move tg_guard_program0_m tg_guard_program0_closed_l f (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
      (Fin.cases (Or.inl hωρ) (Fin.cases (Or.inr hl) (fun _ => Or.inr hh))) ph
  · apply tg_guard_code_reflect_l (ZF.modelsKP hZF) dt nd υ (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) hA names
    exact (same 2) ▸ (same 1) ▸ (same 3) ▸ (same 5) ▸ chM
  · let f : Fin 2 → Term 17 := Fin.cases (.bound 9) (fun _ => .bound 2)
    exact move ee_inacc_program0_m ee_inacc_program0_closed_l f (Fin.cases rfl (fun _ => rfl))
      (Fin.cases (Or.inl hωρ) (fun _ => Or.inr hi)) pi
  · apply (rt_model_delta_l dt nd (kpair0_delta_l ..) υ).mpr
    apply (kpair0_sat_l hZF.1 ..).mpr
    simp only [@eval_image_env_l (rt_model_l D nd) M Subtype.val, υ,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact (same 0) ▸ pairM
  · apply tt_code2_reflect_l (ZF.modelsKP hZF) dt nd hω hωD υ (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) hA names
    exact (same 2) ▸ (same 3) ▸ (same 6) ▸ ciM
  · let f : Fin 6 → Term 17 :=
      Fin.cases (.bound 9) (Fin.cases (.bound 11) (Fin.cases (.bound 7) (Fin.cases (.bound 6) (Fin.cases (.bound 5) (fun _ => .bound 1)))))
    exact move ee_stretch_program0_m ee_stretch_program0_closed_l f
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))
      (Fin.cases (Or.inl hωρ) (Fin.cases (Or.inr hn) (Fin.cases (Or.inr hv) (Fin.cases (Or.inr hd)
        (Fin.cases (Or.inr he) (fun _ => Or.inr hz)))))) pe
  · apply ee_stretch_code_reflect_l hZF.1 dt nd υ (.bound 9) (.bound 11) (.bound 10) (.bound 7)
      (.bound 6) (.bound 5) (.bound 1) (.bound 16)
    exact (same 0) ▸ (same 2) ▸ (same 1) ▸ (same 7) ▸ ceM

end YesMetaZFC.SetTheory.LargeCardinal

import YesMetaZFC.Model.SetTheory.Internal.TupleUnpack

/-! # 原变量列到平坦元组图的自动公式编译

实际编译打包与反解公式，再绑定前缀见证。所得原公式直接核验候选图：
定义域为内部 n，值域在前一秩层，并且每项等于相应原变量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem st_tuple_build_l {ω w v b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hv : M.mem v b) (hn : M.mem n ω) (hnb : M.MemberSubset n b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ ν μ X Y c R f t,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → M.mem ω Y → Smem_d Q c Y R →
      M.IsSetFunctionFromTo Q f ω Y → M.PairMember Q w ω f → M.PairMember Q v n f → M.PairMember Q b t f →
      (Satisfies_d Q ω c a f ↔ M.IsSetFunctionFromTo K t n X ∧
        ∀ i x, M.mem i n → (M.PairMember K i x t ↔ M.PairMember Q i x f)) := by
  obtain ⟨p, hp, hpω⟩ := hω.1.2 b hb
  obtain ⟨d, hd, hdω⟩ := hω.1.2 p hpω
  have below {i} (hi : M.mem i b) : M.mem i d := (hd i).mpr (Or.inl ((hp i).mpr (Or.inl hi)))
  obtain ⟨m₀, G₀, u₀, hG₀, hu₀, pack⟩ := st_pack_build_l hZF hω hpω ((hp w).mpr (Or.inl hw)) hn
    (fun i hi => (hp i).mpr (Or.inl (hnb i hi)))
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l st_unpack_s.body)
    (source_core_closed_l _ st_unpack_s.freeClosed) (Fin.cases p (Fin.cases b (Fin.cases v (fun _ => w)))) hdω
    (Fin.cases hd.predecessor_mem (Fin.cases ((hd b).mpr (Or.inl hp.predecessor_mem))
      (Fin.cases (below hv) (fun _ => below hw)))) hG₀
  obtain ⟨m₂, G₂, u₂, a₂, both⟩ := sfm_and_l Q hZF hω add.program (add.span u₀ hu₀) add.root
  obtain ⟨m, G, u, a₃, ex⟩ := sfm_ex_l Q hZF hω a₂.program hpω a₂.root
  obtain ⟨a, ha⟩ := (Q).total G u
  have form : Sformula_d Q ω a m G u := ⟨ha, a₃.program, a₃.root⟩
  refine ⟨a, m, G, u, form, fun ν μ X Y c R f t hV hW hs hωY model fn fw fv fb => ?_⟩
  have trans := ZF.v_transitive_l Q hZF hW
  have hXY := (ZF.v_successor_l Q hZF hV hW hs X).mpr (fun _ h => h)
  have sub : M.MemberSubset X Y := trans X hXY
  have hων : M.MemberSubset ω ν := by
    rcases (hs ω).mp (ZF.v_ordinal_height_l hZF hW (hω.isOrdinal hZF) hωY) with lt | eq
    · exact (v_ordinal_l Q hV).transitive ω lt
    · exact fun i hi => (eq i).mp hi
  have hωμ := (v_ordinal_l Q hW).transitive ω (ZF.v_ordinal_height_l hZF hW (hω.isOrdinal hZF) hωY)
  have widen {g} (h : M.IsSetFunctionFromTo K g ω X) : M.IsSetFunctionFromTo K g ω Y :=
    ⟨h.1, h.2.1, fun i hi => (h.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩
  have lift {g q} (h : Fs_code_d K ω X g n q) : Fs_code_d K ω Y g n q := by
    obtain ⟨H, hH, entry⟩ := h
    exact ⟨H, ⟨widen hH.1, hH.2⟩, entry⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF Q ω Y
  have hf := (hE f).mpr fn
  have read q (hq : M.mem q Y) f₁ (update : Senv_update_d Q f p q f₁) g₁
      (hg₁ : M.IsSetFunctionFromTo K g₁ ω Y) (fg₁ : Sx_graph_d Q K f₁ g₁) :
      Ssat_d Q Y R E G₂ m₂ u₂ f₁ ↔ Fs_code_d K ω Y g₁ n q ∧ M.IsSetFunctionFromTo K t n X ∧
        ∃ g, M.IsSetFunctionFromTo K g ω X ∧ Fs_code_d K ω X g n q ∧ M.IsRestrictionOf K t g n := by
    have fn₁ := update.function_l Q fn hpω hq
    have hf₁ := (hE f₁).mpr fn₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    have fq := (update.2 p q).mpr (Or.inl ⟨rfl, rfl⟩)
    have fw₁ := (old w ω ((hp w).mpr (Or.inl hw))).mp fw
    have fv₁ := (old v n ((hp v).mpr (Or.inl hv))).mp fv
    have fb₁ := (old b t hp.predecessor_mem).mp fb
    let η : Env (smdl_structure_l Q (R := R) model.1.2.1) 4 :=
      ⟨Fin.cases ⟨q, hq⟩ (Fin.cases ⟨t, fn.output_mem_of_pairMember fb⟩
        (Fin.cases ⟨n, fn.output_mem_of_pairMember fv⟩ (fun _ => ⟨ω, hωY⟩))),
        fun _ => ⟨t, fn.output_mem_of_pairMember fb⟩⟩
    have atom := (compile Y R model.1.2.1 E hE f₁ hf₁ η (Fin.cases fq (Fin.cases fb₁ (Fin.cases fv₁ (fun _ => fw₁))))).trans
      ((source_core_sat_l st_unpack_s.body η).trans ((smem_formula_l Q model _ st_unpack_s.body
        (⟨η.bound, η.free⟩ : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 4)).symm.trans
          (st_unpack_source_l hZF hω hV hW hs hωY ⟨n, fn.output_mem_of_pairMember fv⟩
            ⟨t, fn.output_mem_of_pairMember fb⟩ ⟨q, hq⟩)))
    exact (both Y R E f₁ hf₁).trans (and_congr ((add.sat_l Q hZF hG₀ hu₀ Y R E f₁).symm.trans
      (pack μ Y c R E f₁ g₁ q hW hωY model hE hf₁ hg₁ fg₁ fw₁ fq)) atom)
  refine (satisfies_decode_l Q hZF.1 model.1 form hE).trans ((ex Y R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨q, f₁, hq, update, truth⟩
    obtain ⟨g₁, hg₁, fg₁⟩ := fn_recode_l Q K hZF (update.function_l Q fn hpω hq)
    obtain ⟨cp, ht, g, hg, cg, cut⟩ := (read q hq f₁ update g₁ hg₁ fg₁).mp truth
    have same := (cp.prefix_l K hZF hω hg₁ (widen hg) (lift cg)).mp rfl
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    exact ⟨ht, fun i x hi => (cut.2 i x).trans ((and_iff_right hi).trans
      ((same i x hi).symm.trans ((fg₁ i x).trans (old i x ((hp i).mpr (Or.inl (hnb i hi)))).symm)))⟩
  · rintro ⟨ht, same⟩
    obtain ⟨e, he, heω⟩ := hω.1.1
    have heX := ZF.v_ordinal_mem_l Q hZF hV (hων e heω)
    obtain ⟨g, fill, hg⟩ := senv_fill_exists_l K hZF (ω := ω) ht heX
    have cut : M.IsRestrictionOf K t g n := ⟨ht.1.1, fun i x => ⟨fun hx => by
      have hi := ht.input_mem_of_pairMember hx
      exact ⟨hi, (fill.2 i x).mpr ⟨hω.transitive hZF n hn i hi, Or.inl ⟨hi, hx⟩⟩⟩,
      fun ⟨hi, hx⟩ => ((fill.2 i x).mp hx).2.elim And.right (fun h => (h.1 hi).elim)⟩⟩
    obtain ⟨q, hqX, cg⟩ := fp_finite_rank_l Q hZF hω hV hων hg hn
    have hq := sub q hqX
    obtain ⟨f₁, update, fn₁⟩ := senv_update_exists_l Q hZF fn hpω hq
    obtain ⟨g₁, hg₁, fg₁⟩ := fn_recode_l Q K hZF fn₁
    obtain ⟨H₁, trace, _⟩ := fp_trace_rank_l Q hZF hω hW hωμ hg₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    have agree : Senv_agree_d K n g g₁ := fun i x hi =>
      ((cut.2 i x).trans (and_iff_right hi)).symm.trans ((same i x hi).trans
        ((old i x ((hp i).mpr (Or.inl (hnb i hi)))).trans (fg₁ i x).symm))
    exact ⟨q, f₁, hq, update, (read q hq f₁ update g₁ hg₁ fg₁).mpr
      ⟨(lift cg).transport_l K hZF hω (widen hg) hg₁ trace agree, ht, g, hg, cg, cut⟩⟩

/-- 任意固定原公式都可在内部元组上求值；编译结果只绑定实际元组图。 -/
theorem st_tuple_bind_l {ω w v b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hv : M.mem v b) (hn : M.mem n ω) (hnb : M.MemberSubset n b)
    {k : Nat} (φ : Formula 1 (k+1)) (hφ : φ.FreeClosed) (σ : Fin k → M.Domain) (hσ : ∀ i, M.mem (σ i) b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ ν μ X Y c R f (hm : Smem_d Q c Y R)
      (ρ : Env (smdl_structure_l Q (R := R) hm.1.2.1) k),
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → M.mem ω Y → M.IsSetFunctionFromTo Q f ω Y →
      M.PairMember Q w ω f → M.PairMember Q v n f → (∀ i, M.PairMember Q (σ i) (ρ.bound i).val f) →
        (Satisfies_d Q ω c a f ↔ ∃ h : (smdl_structure_l Q (R := R) hm.1.2.1).Domain,
          M.IsSetFunctionFromTo K h.val n X ∧
            (∀ i x, M.mem i n → (M.PairMember K i x h.val ↔ M.PairMember Q i x f)) ∧ Formula.satisfies (ρ.push h) φ) := by
  obtain ⟨a₀, m₀, G₀, u₀, form₀, tuple⟩ := st_tuple_build_l hZF hω hb hw hv hn hnb
  obtain ⟨j, hj, hjω⟩ := hω.1.2 b hb
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ hφ) (Fin.cases b σ) hjω
    (Fin.cases hj.predecessor_mem (fun i => (hj (σ i)).mpr (Or.inl (hσ i)))) form₀.2.1
  obtain ⟨m₂, G₂, u₂, a₂, both⟩ := sfm_and_l Q hZF hω add.program (add.span u₀ form₀.2.2) add.root
  obtain ⟨m, G, u, a₃, ex⟩ := sfm_ex_l Q hZF hω a₂.program hb a₂.root
  obtain ⟨a, ha⟩ := (Q).total G u
  have form : Sformula_d Q ω a m G u := ⟨ha, a₃.program, a₃.root⟩
  refine ⟨a, m, G, u, form, fun ν μ X Y c R f hm ρ hV hW hs hωY fn fw fv values => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF Q ω Y
  have hf := (hE f).mpr fn
  have body (h : (smdl_structure_l Q (R := R) hm.1.2.1).Domain) f₁ (update : Senv_update_d Q f b h.val f₁) :
      Ssat_d Q Y R E G₂ m₂ u₂ f₁ ↔ M.IsSetFunctionFromTo K h.val n X ∧
        (∀ i x, M.mem i n → (M.PairMember K i x h.val ↔ M.PairMember Q i x f)) ∧ Formula.satisfies (ρ.push h) φ := by
    have fn₁ := update.function_l Q fn hb h.property
    have hf₁ := (hE f₁).mpr fn₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    have fh := (update.2 b h.val).mpr (Or.inl ⟨rfl, rfl⟩)
    have tuples := (add.sat_l Q hZF form₀.2.1 form₀.2.2 Y R E f₁).symm.trans
      ((satisfies_decode_l Q hZF.1 hm.1 form₀ hE).symm.trans
        (tuple ν μ X Y c R f₁ h.val hV hW hs hωY hm fn₁ ((old w ω hw).mp fw) ((old v n hv).mp fv) fh))
    have atom := (compile Y R hm.1.2.1 E hE f₁ hf₁ (ρ.push h)
      (Fin.cases fh (fun i => (old (σ i) (ρ.bound i).val (hσ i)).mp (values i)))).trans (source_core_sat_l φ (ρ.push h))
    refine (both Y R E f₁ hf₁).trans ((and_congr tuples atom).trans ⟨?_, ?_⟩)
    · rintro ⟨⟨fn, same⟩, truth⟩
      exact ⟨fn, fun i x hi => (same i x hi).trans (old i x (hnb i hi)).symm, truth⟩
    · rintro ⟨fn, same, truth⟩
      exact ⟨⟨fn, fun i x hi => (same i x hi).trans (old i x (hnb i hi))⟩, truth⟩
  refine (satisfies_decode_l Q hZF.1 hm.1 form hE).trans ((ex Y R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨h, f₁, hh, update, truth⟩
    exact ⟨⟨h, hh⟩, (body ⟨h, hh⟩ f₁ update).mp truth⟩
  · rintro ⟨h, truth⟩
    obtain ⟨f₁, update, _⟩ := senv_update_exists_l Q hZF fn hb h.property
    exact ⟨h.val, f₁, h.property, update, (body h f₁ update).mpr truth⟩

end YesMetaZFC.SetTheory.Internal

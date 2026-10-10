import YesMetaZFC.Model.SetTheory.Internal.FiniteEvaluation
import YesMetaZFC.Model.SetTheory.Internal.FiniteTruth
import YesMetaZFC.Model.SetTheory.Internal.SkolemSyntax

/-! # Skolem 见证的有限真值证书

只记录更新后赋值在程序支撑上的值。参数列长度和被更新坐标不必落在该
支撑内，因此同一证书覆盖全部内部公式及全部有限参数列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Fw_env_d (b A u n s i x t : M.Domain) : Prop := Fn0_d b A t ∧
  ∀ v, M.mem v b → ∀ y, M.mem y A → (Rd_entry_d v y t ↔
    (v = i ∧ y = x) ∨ (v ≠ i ∧ ((M.mem v n ∧ Rd_entry_d v y s) ∨ (¬ M.mem v n ∧ y = u))))

def fw_env_m {d} (b A u n s i x t : Term d) : Formula 1 d := .conj (fn0_m b A t)
  (Formula.forallMem b (Formula.forallMem A.weaken (.iff (rd_entry0_m (.bound 1) .newest t.weaken.weaken)
    (.disj (.conj (Formula.extensionalEq (.bound 1) i.weaken.weaken) (Formula.extensionalEq .newest x.weaken.weaken))
      (.conj (.neg (Formula.extensionalEq (.bound 1) i.weaken.weaken))
        (.disj (.conj (.mem (.bound 1) n.weaken.weaken) (rd_entry0_m (.bound 1) .newest s.weaken.weaken))
          (.conj (.neg (.mem (.bound 1) n.weaken.weaken)) (Formula.extensionalEq .newest u.weaken.weaken))))))))
derive_free_closed fw_env_m

theorem fw_env_delta_l {d} (b A u n s i x t : Term d) : (fw_env_m b A u n s i x t).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..)
    (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (.conj (.neg (.atom _ _ _))
      (.disj (.conj (.mem _ _) (rd_entry0_delta_l ..)) (.conj (.neg (.mem _ _)) (.atom _ _ _))))))))

theorem fw_env_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b A u n s i x t : Term d) :
    Formula.satisfies ρ (fw_env_m b A u n s i x t) ↔ Fw_env_d
      (b.eval ρ) (A.eval ρ) (u.eval ρ) (n.eval ρ) (s.eval ρ) (i.eval ρ) (x.eval ρ) (t.eval ρ) := by
  simp only [fw_env_m, Fw_env_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hE, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]; rfl

theorem fw_env_read_l (hKP : M.Models KP) {ω b A u n s i x t f g : M.Domain}
    (hb : M.MemberSubset b ω) (hf : Senv_fill_d (kp_pair_l hKP) ω u n s f)
    (hg : Senv_update_d (kp_pair_l hKP) f i x g) (hG : M.IsSetFunctionFromTo (kp_pair_l hKP) g ω A)
    (ht : Fn0_d b A t) : Fw_env_d b A u n s i x t ↔ Senv_agree_d (kp_pair_l hKP) b g t := by
  have value v y (hv : M.mem v b) := (hg.2 v y).trans (or_congr Iff.rfl
    (and_congr Iff.rfl ((hf.2 v y).trans (and_iff_right (hb v hv)))))
  exact ⟨fun h v y hv => ⟨fun hgy => (h.2 v hv y (hG.output_mem_of_pairMember hgy)).mpr ((value v y hv).mp hgy),
    fun hty => (value v y hv).mpr ((h.2 v hv y (ht.bound_l hty).2).mp hty)⟩,
    fun h => ⟨ht, fun v hv y _ => (h v y hv).symm.trans (value v y hv)⟩⟩

def Fw_cert_d (hKP : M.Models KP) (ω A R J u a i s x n b l L F E C H t r : M.Domain) : Prop :=
  M.mem n ω ∧ Fn0_d n A s ∧ KPair_d M a F r ∧ M.mem r l ∧ Fb_program_d hKP ω b l L F ∧
    Fv_space_d b A J E ∧ Fv_eval_d hKP b A R E l L F C H ∧ Fw_env_d b A u n s i x t ∧ Fv_at_d C H r t

def fw_cert_m {d} (ω A R J u a i s x n b l L F E C H t r : Term d) : Formula 1 d :=
  .conj (.mem n ω) (.conj (fn0_m n A s) (.conj (kpair0_m a F r) (.conj (.mem r l)
    (.conj (fb_program_m ω b l L F) (.conj (fv_space_m b A J E) (.conj (fv_eval_m b A R E l L F C H)
      (.conj (fw_env_m b A u n s i x t) (fv_at_m C H r t))))))))
derive_free_closed fw_cert_m

theorem fw_cert_delta_l {d} (ω A R J u a i s x n b l L F E C H t r : Term d) :
    (fw_cert_m ω A R J u a i s x n b l L F E C H t r).IsDelta0 :=
  .conj (.mem _ _) (.conj (fn0_delta_l ..) (.conj (kpair0_delta_l ..) (.conj (.mem _ _)
    (.conj (fb_program_delta_l ..) (.conj (fv_space_delta_l ..) (.conj (fv_eval_delta_l ..)
      (.conj (fw_env_delta_l ..) (fv_at_delta_l ..))))))))

theorem fw_cert_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω A R J u a i s x n b l L F E C H t r : Term d) :
    Formula.satisfies ρ (fw_cert_m ω A R J u a i s x n b l L F E C H t r) ↔ Fw_cert_d hKP
      (ω.eval ρ) (A.eval ρ) (R.eval ρ) (J.eval ρ) (u.eval ρ) (a.eval ρ) (i.eval ρ) (s.eval ρ) (x.eval ρ)
      (n.eval ρ) (b.eval ρ) (l.eval ρ) (L.eval ρ) (F.eval ρ) (E.eval ρ) (C.eval ρ) (H.eval ρ) (t.eval ρ) (r.eval ρ) := by
  simp only [fw_cert_m, Fw_cert_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    fn0_sat_l hKP.1, kpair0_sat_l hKP.1, fb_program_sat_l hKP, fv_space_sat_l hKP.1,
    fv_eval_sat_l hKP, fw_env_sat_l hKP.1, fv_at_sat_l hKP.1]

def fw_witness_m {d} (ω A R J u a i s x : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (fw_cert_m (w ω) (w A) (w R) (w J) (w u) (w a) (w i) (w s) (w x)
      (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))))))
derive_free_closed fw_witness_m

theorem Fw_cert_d.witness_l (hZF : M.Models ZF) {ω c A R J u a i s x n b l L F E C H t r : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c A R)
    (hJ : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A J) (hu : M.mem u A) (hi : M.mem i ω) (hx : M.mem x A)
    (h : Fw_cert_d (ZF.modelsKP hZF) ω A R J u a i s x n b l L F E C H t r) :
    Ssk_wit_d (kp_pair_l (ZF.modelsKP hZF)) ω c A u a i s x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨hn, hs, code, hr, program, space, ev, env, ht⟩ := h
  obtain ⟨hF, bound⟩ := program.read_l hZF hω
  have hE := (fv_space_l (ZF.modelsKP hZF) program.1 hJ).mp space
  obtain ⟨f, hf, fn⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) hs) hu
  obtain ⟨g, hg, gn⟩ := senv_update_exists_l I hZF fn hi hx
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω A
  have same := ssat_spaces_l I hZF (R := R) hF bound hE₀ hE (hω.transitive hZF b program.1) (fun _ h => h) hr
    ((hE₀ g).mpr gn) ((hE t).mpr (fn0_function_l (ZF.modelsKP hZF) env.1))
    ((fw_env_read_l (ZF.modelsKP hZF) (hω.transitive hZF b program.1) hf hg gn env.1).mp env)
  exact ⟨n, f, g, hn, fn0_function_l (ZF.modelsKP hZF) hs, hf, hg,
    (satisfies_decode_l I hZF.1 hm ⟨code, hF, hr⟩ hE₀).mpr (same.mpr ((ev.truth_l hZF hω program hE hr).mp ht))⟩

end YesMetaZFC.SetTheory.Internal

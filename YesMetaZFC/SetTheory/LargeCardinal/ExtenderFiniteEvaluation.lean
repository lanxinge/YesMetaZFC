import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteSyntax

/-! # 源内实际存在的有限真值表

对程序行作内部强归纳。原子、布尔步和有限赋值的量词投影均由源内 Δ₀
分离给出；有限函数闭性随后收集整张表。无需源包含赋值空间的完整幂集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.finite_evaluation_l {ω κ K Z S b A R E n L F : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (hA : M.mem A Z) (hR : M.mem R Z) (hEZ : M.mem E Z)
    (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F) (hE : M.IsFunctionSpace I E b A) :
    ∃ C H, M.mem C Z ∧ M.mem H Z ∧ Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H := by
  have hω := source.omega
  obtain ⟨hF, bound⟩ := program.read_l hZF hω
  obtain ⟨H, hH⟩ := seval_exists_l I hZF A R E F hF.2.1.1
  obtain ⟨C, hC⟩ := ZF.exists_range_of_setFunction hZF I hH.1.2.1 hH.1.2.2
  have fnH : M.IsSetFunctionFromTo I H n C := ⟨hH.1.2.1, hH.1.2.2, fun r hr =>
    ((hH.1.2.2 r).mp hr).imp fun Y hY => ⟨(hC Y).mpr ⟨r, hY⟩, hY⟩⟩
  have row_sub r Y (hY : Rd_entry_d r Y H) : M.MemberSubset Y E := by
    obtain ⟨c, hc⟩ := (hF.2.1.2.2 r).mp (fnH.input_mem_of_pairMember hY)
    exact fun f hf => ((seval_row_l I hZF hF hH hc hY f).mp hf).1
  obtain ⟨c₀, model⟩ := source.code
  let ρ : Env M 2 := ⟨Fin.cases H (fun _ => Z), fun _ => H⟩
  let φ : UnarySchema 2 := { body := .forallE (.imp
    (rd_entry0_m (.bound 1) .newest (.bound 2)) (.mem .newest (.bound 3))) }
  have sat r : φ.denote ρ r ↔ ∀ Y, Rd_entry_d r Y H → M.mem Y Z := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  have rows r (hr : M.mem r n) : ∀ Y, Rd_entry_d r Y H → M.mem Y Z := by
    apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr)
    intro r hr ih
    apply (sat r).mpr
    intro Y hrY
    obtain ⟨c, hrc⟩ := (hF.2.1.2.2 r).mp hr
    have finish {p i j} (k : Fin 4) (hs : Sop_d I k.val c i j) (ψ : UnarySchema p)
        (hd : ψ.body.IsDelta0) (η : Env M p) (hη : ∀ i, M.mem (η.bound i) Z)
        (read : ∀ f, M.mem f E → (ψ.denote η f ↔ Sarg_d I k.val A R H f i j)) : M.mem Y Z := by
      obtain ⟨D, hDZ, spec⟩ := sc_separate_source_l I hZF hω source.transitive model source.theory ψ hd η hη hEZ
      have eq : D = Y := hZF.1.eq_of_same_members D Y (fun f => (spec f).trans
        ((and_congr_right fun hf => (read f hf).trans (snode_decode_l I (ZF.modelsKP hZF) k hs).symm).trans
          (seval_row_l I hZF hF hH hrc hrY f).symm))
      exact eq ▸ hDZ
    rcases hF.2.2 r c hrc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ |
      ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
    · let η : Env M 4 := ⟨Fin.cases i (Fin.cases j (Fin.cases A (fun _ => R))), fun _ => A⟩
      let ψ : UnarySchema 4 := {
        body := fv_arg_m 0 (.bound 3) (.bound 3) (.bound 4) (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2) }
      apply finish 0 hs ψ (fv_arg_delta_l 0 (.bound 3) (.bound 3) (.bound 4)
        (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2)) η
        (Fin.cases (source.transitive ω source.omega_mem i hi)
          (Fin.cases (source.transitive ω source.omega_mem j hj) (Fin.cases hA (fun _ => hR))))
      intro f hf
      exact (fv_arg_sat_l hZF.1 0 (η.push f) (.bound 3) (.bound 3) (.bound 4)
        (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2)).trans (fv_arg_l (ZF.modelsKP hZF) hE hf
        (bound.operands_l I hrc hs).1 (fn0_of_function_l (ZF.modelsKP hZF) fnH) row_sub 0)
    · let η : Env M 3 := ⟨Fin.cases i (Fin.cases j (fun _ => A)), fun _ => A⟩
      let ψ : UnarySchema 3 := {
        body := fv_arg_m 1 (.bound 3) (.bound 3) (.bound 3) (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2) }
      apply finish 1 hs ψ (fv_arg_delta_l 1 (.bound 3) (.bound 3) (.bound 3)
        (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2)) η
        (Fin.cases (source.transitive ω source.omega_mem i hi)
          (Fin.cases (source.transitive ω source.omega_mem j hj) (fun _ => hA)))
      intro f hf
      exact (fv_arg_sat_l hZF.1 1 (η.push f) (.bound 3) (.bound 3) (.bound 3)
        (.bound 3) (.bound 3) (.bound 3) .newest (.bound 1) (.bound 2)).trans (fv_arg_l (ZF.modelsKP hZF) hE hf
        (bound.operands_l I hrc hs).1 (fn0_of_function_l (ZF.modelsKP hZF) fnH) row_sub 1)
    · obtain ⟨U, hiU⟩ := (hH.1.2.2 i).mp (hF.2.1.1.transitive r hr i hi)
      obtain ⟨V, hjV⟩ := (hH.1.2.2 j).mp (hF.2.1.1.transitive r hr j hj)
      let η : Env M 2 := ⟨Fin.cases U (fun _ => V), fun _ => U⟩
      let ψ : UnarySchema 2 := { body := .neg (.disj (.mem .newest (.bound 1)) (.mem .newest (.bound 2))) }
      apply finish 2 hs ψ (.neg (.disj (.mem _ _) (.mem _ _))) η
        (Fin.cases ((sat i).mp (ih i hi) U hiU) (fun _ => (sat j).mp (ih j hj) V hjV))
      intro f _
      simp only [ψ, UnarySchema.denote, Formula.satisfies_neg_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff]
      change (¬ (M.mem f U ∨ M.mem f V)) ↔ Sarg_d I 2 A R H f i j
      exact ⟨fun h => ⟨U, V, hiU, hjV, h⟩, fun ⟨U', V', hiU', hjV', h⟩ =>
        fnH.1.2 i U' U hiU' hiU ▸ fnH.1.2 j V' V hjV' hjV ▸ h⟩
    · obtain ⟨V, hjV⟩ := (hH.1.2.2 j).mp (hF.2.1.1.transitive r hr j hj)
      let η : Env M 5 := ⟨Fin.cases b (Fin.cases A (Fin.cases E (Fin.cases i (fun _ => V)))), fun _ => A⟩
      let ψ : UnarySchema 5 := { body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
        (.conj (se_update0_m (.bound 3) (.bound 4) (.bound 2) (.bound 6) (.bound 1) .newest) (.mem .newest (.bound 7)))) }
      have read f : ψ.denote η f ↔ ∃ x, M.mem x A ∧ ∃ g, M.mem g E ∧ Se_update0_d b A f i x g ∧ M.mem g V := by
        simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
          se_update0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
      apply finish 3 hs ψ (.existsMem _ (.existsMem _ (.conj (se_update0_delta_l ..) (.mem _ _)))) η
        (Fin.cases (source.transitive ω source.omega_mem b program.1) (Fin.cases hA (Fin.cases hEZ
          (Fin.cases (source.transitive ω source.omega_mem i hi) (fun _ => (sat j).mp (ih j hj) V hjV)))))
      intro f hf
      have update x (hx : M.mem x A) (g : M.Domain) := se_update0_l (g := g) (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) ((hE f).mp hf))
        (bound.operands_l I hrc hs).1 hx
      refine (read f).trans ⟨fun ⟨x, hx, g, _, hg, h⟩ => ⟨V, hjV, x, g, hx, (update x hx g).mp hg, h⟩, ?_⟩
      rintro ⟨V', hjV', x, g, hx, hg, h⟩
      have eq := fnH.1.2 j V' V hjV' hjV
      subst V'
      exact ⟨x, hx, g, row_sub j V hjV g h, (update x hx g).mpr hg, h⟩
  have fnZ := (fn0_of_function_l (ZF.modelsKP hZF) fnH).retarget_l
    (fun r Y hY => rows r (fnH.input_mem_of_pairMember hY) Y hY)
  have hHZ := sc_finite_function_l hZF hω source.transitive source.theory.algebra.pair source.theory.algebra.union source.omega_mem
    (fun _ h => h) hF.1 fnZ
  obtain ⟨_, C', hC'Z, fn'⟩ := source.function_l hZF hHZ fnZ
  exact ⟨C', H, hC'Z, hHZ, fv_eval_of_l hZF hω program hE hH fn'⟩

end YesMetaZFC.SetTheory.LargeCardinal

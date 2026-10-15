import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReady
import YesMetaZFC.SetTheory.Descriptive.GameControl

/-! # 原 I 策略下三步响应保持可继续状态

最小请求合法后，I 的两种应答由原获胜策略的控制集合保证合法；奇数轮读取
对手的原字母。三个实际追加图同时给出下一轮时钟和实数前缀，未引入续步谕示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_digits_d.append_l {ω c b n m A h t z y : M.Domain}
    (hw : M.IsOmega ω) (hc : M.IsOrdinal c) (hn : M.mem n ω) (succ : M.SuccessorOf m n)
    (digits : Tg_digits_d hZF c b n A h z) (sub : M.MemberSubset h t) (ft : M.IsSetFunction I t)
    (hy : M.mem y A) (event : Tg_event_d I c n b t y) :
    ∃ z', Fseq_end_d I ω z' z y ∧ Tg_digits_d hZF c b m A t z' := by
  obtain ⟨m', z', hm', fz', endz⟩ := ZF.fseq_end_exists_l I hZF hw hn (fn0_function_l (ZF.modelsKP hZF) digits.1) hy
  obtain ⟨r, s, dec⟩ := endz
  have es := dec.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) digits.1).2.1; subst s
  have er := dec.source.2.2.2.eq hZF.1 fz'.2.1; subst r
  have em := dec.length_successor.eq hZF.1 succ; subst m'
  refine ⟨z', ⟨m, n, dec⟩, fn0_of_function_l (ZF.modelsKP hZF) fz', fun i v hi => ?_⟩
  obtain ⟨w, _, iw⟩ := fz'.2.2 i hi
  have ew : Tg_event_d I c i b t w := by
    rcases (succ i).mp hi with hin | eq
    · obtain ⟨j, clock, q, pair, hq⟩ := (digits.2 i w hin).mp ((dec.prefix_restriction.2 i w).mpr ⟨hin, iw⟩)
      exact ⟨j, clock, q, pair, sub q hq⟩
    · have eq := hZF.1.eq_of_same_members i n eq; subst i
      exact (fz'.1.2 n w y iw dec.last_value).symm ▸ event
  exact ⟨fun iv => (fz'.1.2 i w v iw iv) ▸ ew,
    fun ev => (ew.unique_l hZF hc ft ev) ▸ iw⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

theorem Tg_ready_d.advance_l {p : Tg_params_d M.Domain} {X F L G J σ R n m h h₁ h₂ t a w y : M.Domain}
    (setup : Tg_setup_d hZFC p X) (histories : Tg_histories_d hZ p X F L)
    (owner : Tg_owner_d hZ p.ω p.c p.a p.b J) (control : Cg_control_d K true p.ω p.e X F L G J σ R)
    (ready : Tg_ready_d hZ p X n h) (hh : M.mem h R) (succ : M.SuccessorOf m n)
    (h₁F : M.mem h₁ F) (h₂F : M.mem h₂ F) (tF : M.mem t F)
    (e₁ : Fseq_end_d K p.ω h₁ h a) (e₂ : Fseq_end_d K p.ω h₂ h₁ w) (e₃ : Fseq_end_d K p.ω t h₂ y)
    (legal : Cg_admit_d hZ p.ω L h a) (value : Rd_entry_d h₁ w σ)
    (digit : ∃ j, Fn0_d j X h₂ ∧ ((M.mem j J ∧ Rd_entry_d h₂ y σ) ∨ (¬ M.mem j J ∧ M.mem y p.A))) :
    M.mem t R ∧ Tg_ready_d hZ p X m t ∧ Tg_aux_d hZ p n h a ∧ Tg_event_d K p.c n p.e t a ∧
      M.mem y p.A ∧ ∃ j, Fn0_d j X h₂ ∧ M.IsOrdinalDivision K j p.c n p.b ∧
        Tg_answer_d hZ p n h₁ w ∧ Tg_event_d K p.c n p.e h₁ a ∧ Tg_event_d K p.c n p.a t w := by
  obtain ⟨hn, i, z, hi, fh, div, digits, _⟩ := ready
  obtain ⟨j₁, hj₁, fh₁⟩ := (histories.1 h₁).mp h₁F
  obtain ⟨j₂, hj₂, fh₂⟩ := (histories.1 h₂).mp h₂F
  obtain ⟨j₃, hj₃, ft⟩ := (histories.1 t).mp tF
  have ends {s t x i j : M.Domain} (fs : Fn0_d i X s) (ft : M.IsSetFunctionFromTo K t j X)
      (en : Fseq_end_d K p.ω t s x) : M.SuccessorOf j i ∧ Rd_entry_d i x t := by
    obtain ⟨a, b, d⟩ := en
    have ei := d.prefix_sequence.2.2.2.eq hZ.1 (fn0_function_l (ZF.modelsKP hZ) fs).2.1
    have ej := d.source.2.2.2.eq hZ.1 ft.2.1
    exact ⟨ej ▸ ei ▸ d.length_successor, ei ▸ d.last_value⟩
  obtain ⟨s₁, v₁⟩ := ends fh fh₁ e₁
  obtain ⟨s₂, v₂⟩ := ends (fn0_of_function_l (ZF.modelsKP hZ) fh₁) fh₂ e₂
  obtain ⟨s₃, v₃⟩ := ends (fn0_of_function_l (ZF.modelsKP hZ) fh₂) ft e₃
  obtain ⟨hc, _⟩ := tg_clock_l hZ setup.omega setup.empty setup.one setup.two setup.three hi
  have oc := setup.omega.members_areOrdinals hZ p.c hc
  have ab := oc.transitive p.b setup.three.predecessor_mem p.a setup.two.predecessor_mem
  have div₁ := tg_division_next_l hZ oc div setup.one s₁ ab
  have div₂ := tg_division_next_l hZ oc div₁ setup.two s₂ setup.three.predecessor_mem
  have ne₀ : p.e ≠ p.a := fun eq => setup.empty p.e (eq.symm ▸ setup.one.predecessor_mem)
  have ne₁ : p.e ≠ p.b := fun eq => setup.empty p.a (eq.symm ▸ setup.two.predecessor_mem)
  have turn₀ : ¬ M.mem i J := fun own => ((owner.read_l hZ (setup.omega.isOrdinal hZ) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hi hn div).mp own).elim ne₀ (fun h => ne₁ h.1)
  obtain ⟨h₁', check, endt⟩ := legal
  have eq := fseq_end_rebuild_l K hZ.1 endt e₁; subst h₁'
  have h₁R := control.step i h a h₁ hi hh (fh₁.output_mem_of_pairMember v₁) fh e₁ (Or.inl ⟨turn₀, check⟩)
  have turn₁ := (owner.read_l hZ (setup.omega.isOrdinal hZ) oc ⟨p.b, setup.three.predecessor_mem⟩ hj₁ hn div₁).mpr (Or.inl rfl)
  have h₂R := control.step j₁ h₁ w h₂ hj₁ h₁R (fh₂.output_mem_of_pairMember v₂)
    (fn0_of_function_l (ZF.modelsKP hZ) fh₁) e₂ (Or.inr ⟨turn₁, value⟩)
  have replyStep := (tg_step_read_l hZ (setup.omega.members_areOrdinals hZ j₁ hj₁) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div₁).mp
    (((histories.2 h₂).mp (control.legal.current_l ((control.positions h₂).mp h₂R).1)).2.end_l hZ
      (fn0_of_function_l (ZF.modelsKP hZ) fh₁) e₂)
  have answer : Tg_answer_d hZ p n h₁ w := replyStep.elim (fun h => (ne₀ h.1.symm).elim)
    (fun h => h.elim And.right (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZ) p.a (h.1.symm ▸ setup.two.predecessor_mem)).elim))
  obtain ⟨j, fj, digit⟩ := digit
  have eq := fj.domain_eq_l hZ.1 (fn0_of_function_l (ZF.modelsKP hZ) fh₂); subst j
  have tR : M.mem t R := by
    rcases digit with ⟨own, value⟩ | ⟨own, hy⟩
    · exact control.step j₂ h₂ y t hj₂ h₂R (ft.output_mem_of_pairMember v₃)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ (Or.inr ⟨own, value⟩)
    ·
      have chk := tg_check_end_l hZ hj₃ s₃ (fn0_of_function_l (ZF.modelsKP hZ) ft)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ ⟨n, p.b, hn, div₂, Or.inr (Or.inr ⟨rfl, hy⟩)⟩
      exact control.step j₂ h₂ y t hj₂ h₂R (ft.output_mem_of_pairMember v₃)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ (Or.inl ⟨own, (histories.2 t).mpr ⟨tF, chk⟩⟩)
  have step := (tg_step_read_l hZ (setup.omega.members_areOrdinals hZ j₂ hj₂) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div₂).mp
    (((histories.2 t).mp (control.legal.current_l ((control.positions t).mp tR).1)).2.end_l hZ
      (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃)
  have be : p.b ≠ p.e := Ne.symm ne₁
  have ba : p.b ≠ p.a := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZ) p.a (eq ▸ setup.two.predecessor_mem)
  have hy := step.elim (fun h => (be h.1).elim) (fun h => h.elim (fun h => (ba h.1).elim) And.right)
  have sub : M.MemberSubset h t := fun x hx => e₃.subset_l K x (e₂.subset_l K x (e₁.subset_l K x hx))
  obtain ⟨z', _, digits'⟩ := digits.append_l hZ setup.omega oc hn succ sub ft.1 hy ⟨j₂, div₂, v₃⟩
  have auxStep := (tg_step_read_l hZ (setup.omega.members_areOrdinals hZ i hi) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div).mp (((histories.2 h₁).mp check).2.end_l hZ fh e₁)
  have aux := auxStep.elim And.right (fun h => h.elim (fun h => (ne₀ h.1).elim) (fun h => (ne₁ h.1).elim))
  have saved := aux
  obtain ⟨ℓ, q, κ, u, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, data, hκ, _⟩ := saved
  obtain ⟨m', sm', hm'⟩ := setup.omega.1.2 n hn
  have eq := sm'.eq hZ.1 succ
  exact ⟨tR, ⟨eq ▸ hm', j₃, z', hj₃, fn0_of_function_l (ZF.modelsKP hZ) ft,
    tg_division_cycle_l hZ oc div₂ setup.three succ s₃ setup.empty, digits',
    Or.inr ⟨n, a, ℓ, q, κ, u, succ, (Tg_event_d.end_l (Tg_event_d.end_l ⟨i, div, v₁⟩ e₂) e₃), data, hκ⟩⟩,
    aux, (Tg_event_d.end_l (Tg_event_d.end_l ⟨i, div, v₁⟩ e₂) e₃), hy, j₂,
    fn0_of_function_l (ZF.modelsKP hZ) fh₂, div₂, answer, ⟨i, div, v₁⟩, Tg_event_d.end_l ⟨j₁, div₁, v₂⟩ e₃⟩

end YesMetaZFC.SetTheory.LargeCardinal

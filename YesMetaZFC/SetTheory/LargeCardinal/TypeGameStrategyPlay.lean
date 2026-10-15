import YesMetaZFC.SetTheory.LargeCardinal.TypeGameStrategy

/-! # 服从所构造策略的任意原对局与递归前缀逐轮一致 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_choice_d.play_l {ω c o C γ Z A S r X D K a F σ f H : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) (sf : Fn0_d F A σ)
    (values : ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_response_d hZF ω A X K r a s y)
    (ff : Fn0_d ω A f) (follows : Gm_follows_d I false ω σ f) (run : Gi_d hZF true ω X K r a f H) :
    ∀ n u s, Rd_entry_d n u H → Tg_run_real_d A n u s → M.IsRestrictionOf I s f n := by
  classical
  have fn := fn0_function_l (ZF.modelsKP hZF) ff
  let ρ : Env M 3 := ⟨fun i => [A,H,f].get i,fun _ => A⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪∀ u s,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,u,⌜(.bound 2 : Term 4)⌝ₛ) →
    ⌜tg_run_real_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,⌜(.newest : Term 4)⌝ₛ,u,s) →
    ⌜(Formula.isRestriction kpair_convention_l)⌝ₚ(s,⌜(.bound 3 : Term 4)⌝ₛ,⌜(.newest : Term 4)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ u s, Rd_entry_d n u H → Tg_run_real_d A n u s → M.IsRestrictionOf I s f n := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,rd_entry0_sat_l hZF.1,
      tg_run_real_sat_l hZF.1,Formula.satisfies_isRestriction_iff I,Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → ∀ u s, Rd_entry_d n u H → Tg_run_real_d A n u s → M.IsRestrictionOf I s f n := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz u s _ real
      exact ⟨(fn0_function_l (ZF.modelsKP hZF) real.function_l).1.1,fun i y =>
        ⟨fun hi => (hz i (real.function_l.bound_l hi).1).elim,fun hi => (hz i hi.1).elim⟩⟩
    · intro n hn ih m succ t q mt real
      obtain ⟨u,_,nu⟩ := run.1.2.1 n hn
      have valid := h.valid_l hZF hw ho run n u nu
      obtain ⟨x,p,inp,pair,pt⟩ := run.2.2 n m u t succ nu mt
      obtain ⟨m',succ',next,_,_,move⟩ := h.step n u x t p valid.1 valid.2 pair pt
      have mm := succ'.eq hZF.1 succ
      have next := mm ▸ next
      obtain ⟨s,q',y,old,new,endt,last,even⟩ := (show Tg_run_move_d hZF ω A n m u t x from mm ▸ move).last_l hZF
      have qq := next.real_unique_l hZF new real
      subst q'
      have cut := ih u s nu old
      have fs := fn0_function_l (ZF.modelsKP hZF) old.function_l
      obtain ⟨z,_,nz⟩ := ff.2.1 n hn
      have yz : y = z := by
        by_cases he : Gm_even_d I ω n
        · exact (even he).trans (inp.elim (fun hx => fn.1.2 n x z hx.2 nz) (fun hx => (hx.1 ⟨he,z,nz⟩).elim))
        · have xa : x = a := inp.elim (fun hx => (he hx.1).elim) And.right
          obtain ⟨G,grun⟩ := gi_exists_l hZF (b := true) hw h.product h.function h.member ha fs.1 (fun _ _ hs => fs.output_mem_of_pairMember hs)
          obtain ⟨u',_,nu'⟩ := grun.1.2.1 n hn
          have uu := run.prefix_l hZF hw (fn0_function_l (ZF.modelsKP hZF) h.function).1 fn.1 grun hn cut u u' nu nu'
          have response : Tg_response_d hZF ω A X K r a s y :=
            ⟨n,G,u,p,t,m,q,fs.2.1,grun,uu.symm ▸ nu',xa ▸ pair,pt,succ,real,last⟩
          have sy := (values s y).mpr ⟨(space s).mpr ⟨n,hn,fs⟩,response⟩
          exact (fn0_function_l (ZF.modelsKP hZF) sf).1.2 s y z sy (follows n hn he s cut z nz)
      have fq := fn0_function_l (ZF.modelsKP hZF) real.function_l
      apply (ds_restrict_iff_l I fq fn.1).mpr
      intro p hp
      obtain ⟨i,v,pair⟩ := fq.1.1 p hp
      have iv : Rd_entry_d i v q := ⟨p,pair,hp⟩
      have entry : Rd_entry_d i v f := by
        rcases (succ i).mp (fq.input_mem_of_pairMember iv) with hi | eq
        · obtain ⟨l,k,d⟩ := endt
          have kn := d.prefix_sequence.2.2.2.eq hZF.1 fs.2.1
          exact ((cut.2 i v).mp ((d.prefix_restriction.2 i v).mpr ⟨kn.symm ▸ hi,iv⟩)).2
        · have eq := hZF.1.eq_of_same_members i n eq
          subst i
          exact (fq.1.2 n v y iv last).symm ▸ yz.symm ▸ nz
      obtain ⟨p',pair',hp'⟩ := entry
      exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  exact fun n u s nu real => all n (run.1.bound_l nu).1 u s nu real

theorem Tg_run_choice_d.sequence_l {ω c o C γ Z A S r X D K a F σ f : M.Domain}
    (h : Tg_run_choice_d hZF ω c o C γ Z A S r X D K) (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) (sf : Fn0_d F A σ)
    (values : ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_response_d hZF ω A X K r a s y)
    (ff : Fn0_d ω A f) (follows : Gm_follows_d I false ω σ f) : ∃ H,
      Tg_sequence_d hZF ω c o C γ Z A X H ∧ (∀ i u, Rd_entry_d i u H → Tg_run_name_d S u) ∧
      ∀ i u, Rd_entry_d i u H → ∃ n s, M.SuccessorOf n i ∧ Tg_run_real_d A n u s ∧ M.IsRestrictionOf I s f n := by
  have fn := fn0_function_l (ZF.modelsKP hZF) ff
  obtain ⟨G,run⟩ := gi_exists_l hZF (b := true) hw h.product h.function h.member ha fn.1 (fun _ _ hi => fn.output_mem_of_pairMember hi)
  let ρ : Env M 1 := ⟨fun _ => G,fun _ => G⟩
  let φ : BinarySchema 1 := { body := set[3] ⟪∃ n, ⌜KP.succ0_m⌝ₚ(n,⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(n,⌜(.newest : Term 3)⌝ₛ,⌜(.bound 2 : Term 3)⌝ₛ)⟫ }
  have sat i u : φ.denote ρ i u ↔ ∃ n, M.SuccessorOf n i ∧ Rd_entry_d n u G := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      KP.succ0_sat_l hZF.1,rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  obtain ⟨H,hf,hs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X) (by
    intro i hi
    obtain ⟨n,succ,hn⟩ := hw.1.2 i hi
    obtain ⟨u,_,nu⟩ := run.1.2.1 n hn
    exact ⟨u,(sat i u).mpr ⟨n,succ,nu⟩⟩) (by
    intro i _ u v hu hv
    obtain ⟨n,ni,nu⟩ := (sat i u).mp hu
    obtain ⟨m,mi,mv⟩ := (sat i v).mp hv
    exact (fn0_function_l (ZF.modelsKP hZF) run.1).1.2 n u v nu ((mi.eq hZF.1 ni) ▸ mv)) (by
    intro i u _ hu
    obtain ⟨n,_,nu⟩ := (sat i u).mp hu
    exact (run.1.bound_l nu).2)
  have read i u (hu : Rd_entry_d i u H) := (sat i u).mp ((hs i u).mp hu).2
  refine ⟨H,⟨fn0_of_function_l (ZF.modelsKP hZF) hf,?_,?_⟩,?_,?_⟩
  · intro i u hu
    obtain ⟨n,ni,nu⟩ := read i u hu
    exact ⟨n,ni,(h.valid_l hZF hw ho run n u nu).1⟩
  · intro i j u v succ hu hv
    obtain ⟨n,ni,nu⟩ := read i u hu
    obtain ⟨m,mj,mv⟩ := read j v hv
    have nj := ni.eq hZF.1 succ
    obtain ⟨x,p,_,pair,pv⟩ := run.2.2 n m u v (nj.symm ▸ mj) nu mv
    have valid := h.valid_l hZF hw ho run n u nu
    exact (h.step n u x v p valid.1 valid.2 pair pv).choose_spec.2.2.2.1
  · intro i u hu
    obtain ⟨n,_,nu⟩ := read i u hu
    exact (h.valid_l hZF hw ho run n u nu).2
  · intro i u hu
    obtain ⟨n,ni,nu⟩ := read i u hu
    obtain ⟨s,real⟩ := (h.valid_l hZF hw ho run n u nu).1.real_l hZF
    exact ⟨n,s,ni,real,h.play_l hZF hw ho ha space sf values ff follows run n u s nu real⟩

end YesMetaZFC.SetTheory.LargeCardinal

import YesMetaZFC.SetTheory.LargeCardinal.IterationWeakChoice

/-! # 应答函数驱动的唯一超限运行

后继阶段只读取此前的一个走法，零和极限阶段使用空标记。
递归值是应答的状态分量，所选枝仍可由同一请求重新读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Wi_input_d (o F α t : M.Domain) : Prop :=
  (∃ ξ, M.SuccessorOf α ξ ∧ Rd_entry_d ξ t F) ∨ ((∀ ξ, ¬ M.SuccessorOf α ξ) ∧ t = o)
def wi_input_m {d} (o F α t : Term d) : Formula 1 d := set[d] ⟪
  (∃ ξ, ⌜KP.succ0_m⌝ₚ(⌜α⌝ₛ, ξ) ∧ ⌜rd_entry0_m⌝ₚ(ξ, ⌜t⌝ₛ, ⌜F⌝ₛ)) ∨
  ((∀ ξ, ¬ ⌜KP.succ0_m⌝ₚ(⌜α⌝ₛ, ξ)) ∧ ⌜t⌝ₛ = ⌜o⌝ₛ)⟫
derive_free_closed wi_input_m
theorem wi_input_sat_l (hE : Extensional M) {d} (η : Env M d) (o F α t : Term d) :
    Formula.satisfies η (wi_input_m o F α t) ↔ Wi_input_d (o.eval η) (F.eval η) (α.eval η) (t.eval η) := by
  simp only [wi_input_m, Wi_input_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, KP.succ0_sat_l hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Wi_input_d.unique_l (hKP : M.Models KP) {o F α t v : M.Domain} (ho : M.IsOrdinal α)
    (hf : M.IsSetFunction (kp_pair_l hKP) F) (h : Wi_input_d o F α t) (g : Wi_input_d o F α v) : t = v := by
  rcases h with ⟨ξ, hξ, ht⟩ | ⟨no, ht⟩
  · rcases g with ⟨η, hη, hv⟩ | ⟨no, _⟩
    · have eq := Structure.SuccessorOf.predecessor_eq hKP.1 (ho.mem hξ.predecessor_mem) hξ hη
      exact hf.2 ξ t v ht (eq.symm ▸ hv)
    · exact (no ξ hξ).elim
  · exact g.elim (fun ⟨ξ, hξ, _⟩ => (no ξ hξ).elim) (fun hh => ht.trans hh.2.symm)

def Wi_drive_d (o Ψ F H s : M.Domain) : Prop := ∃ α t r u B,
  (∀ i, M.mem i α ↔ ∃ v, Rd_entry_d i v H) ∧ Wi_input_d o F α t ∧ Rd_triple_d r α H t ∧
    Rd_entry_d r u Ψ ∧ KPair_d M u B s
def wi_drive_m {d} (o Ψ F H s : Term d) : Formula 1 d := set[d] ⟪
  ∃ α t r u B, ⌜Formula.isDomain kpair_convention_l⌝ₚ(α, ⌜H⌝ₛ) ∧ ⌜wi_input_m⌝ₚ(⌜o⌝ₛ, ⌜F⌝ₛ, α, t) ∧
    ⌜rd_triple0_m⌝ₚ(r, α, ⌜H⌝ₛ, t) ∧ ⌜rd_entry0_m⌝ₚ(r, u, ⌜Ψ⌝ₛ) ∧ ⌜kpair0_m⌝ₚ(u, B, ⌜s⌝ₛ)⟫
derive_free_closed wi_drive_m
def wi_drive_schema : BinarySchema 3 where
  body := wi_drive_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
theorem wi_drive_sat_l (hKP : M.Models KP) (η : Env M 3) (H s : M.Domain) :
    wi_drive_schema.denote η H s ↔ Wi_drive_d (η.bound 2) (η.bound 1) (η.bound 0) H s := by
  simp only [wi_drive_schema, BinarySchema.denote, wi_drive_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff (kp_pair_l hKP), wi_input_sat_l hKP.1,
    rd_triple0_sat_l hKP.1, rd_entry0_sat_l hKP.1, kpair0_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

def Wi_run_d (hZF : M.Models ZF) (o Ψ F α Z H : M.Domain) : Prop :=
  M.IsRecursiveSequenceIn (kp_pair_l (ZF.modelsKP hZF)) (Wi_drive_d o Ψ F) H α Z

theorem Wi_drive_d.unique_l (hKP : M.Models KP) {o Ψ F α H s v : M.Domain}
    (seq : M.IsSequenceOfLength (kp_pair_l hKP) H α) (hf : M.IsSetFunction (kp_pair_l hKP) F)
    (hp : M.IsSetFunction (kp_pair_l hKP) Ψ) (h : Wi_drive_d o Ψ F H s) (g : Wi_drive_d o Ψ F H v) : s = v := by
  obtain ⟨β, t, r, u, B, dom, input, pack, edge, pair⟩ := h
  obtain ⟨γ, t', r', u', B', dom', input', pack', edge', pair'⟩ := g
  have eβ := Structure.IsDomainOf.eq (𝕀 := kp_pair_l hKP) hKP.1 dom seq.2.2
  have eγ := Structure.IsDomainOf.eq (𝕀 := kp_pair_l hKP) hKP.1 dom' seq.2.2
  subst β γ
  have eq := input.unique_l hKP seq.1 hf input'
  subst t'
  obtain ⟨q, pq, pr⟩ := pack
  obtain ⟨q', pq', pr'⟩ := pack'
  have eq := kpair_unique_l M hKP.1 pq pq'
  subst q'
  have eq := kpair_unique_l M hKP.1 pr pr'
  subst r'
  exact (kpair_injective_l M (hp.2 r u u' edge edge' ▸ pair) pair').2

theorem wi_run_exists_l (hZFC : M.Models ZFC) {ω χ Z Ω a A S o s₀ Ψ F : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hZ : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ Z)
    (hΩ : M.IsOrdinal Ω) (hΩZ : M.mem Ω Z) (hoZ : M.mem o Z)
    (select : Wi_selector_d (ZFC.models_zf_l hZFC) ω a A S o s₀ Z Ψ) (moves : Fn0_d Ω Z F) :
    ∃ H, Wi_run_d (ZFC.models_zf_l hZFC) o Ψ F Ω Z H ∧
      ∀ H', Wi_run_d (ZFC.models_zf_l hZFC) o Ψ F Ω Z H' → H' = H := by
  classical
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let η : Env M 3 := ((⟨fun _ => o, fun _ => o⟩ : Env M 1).push Ψ).push F
  have sat H s : wi_drive_schema.denote η H s ↔ Wi_drive_d o Ψ F H s := wi_drive_sat_l (ZF.modelsKP hZF) ..
  have zt := ZF.h_transitive_l I hZF hZ
  have ff := fn0_function_l (ZF.modelsKP hZF) moves
  have pf := fn0_function_l (ZF.modelsKP hZF) select.function
  have total H (seq : M.IsSequenceInBelow I H Ω Z) : ∃ s, Wi_drive_d o Ψ F H s := by
    obtain ⟨_, α, hα, seq⟩ := seq
    have hαZ := zt Ω hΩZ α hα
    have hh := ZFC.h_function_l hZFC hω hχ hωχ hZ hαZ seq.2
    have input : ∃ t, M.mem t Z ∧ Wi_input_d o F α t := by
      by_cases succ : ∃ ξ, M.SuccessorOf α ξ
      · obtain ⟨ξ, hξ⟩ := succ
        obtain ⟨t, ht, edge⟩ := moves.2.1 ξ (hΩ.transitive α hα ξ hξ.predecessor_mem)
        exact ⟨t, ht, Or.inl ⟨ξ, hξ, edge⟩⟩
      · exact ⟨o, hoZ, Or.inr ⟨fun ξ hξ => succ ⟨ξ, hξ⟩, rfl⟩⟩
    obtain ⟨t, ht, input⟩ := input
    obtain ⟨p, pp⟩ := I.total H t
    obtain ⟨r, pr⟩ := I.total α p
    have hr := ZFC.h_kpair_l hZFC hω hχ hωχ hZ pr hαZ (ZFC.h_kpair_l hZFC hω hχ hωχ hZ pp hh ht)
    obtain ⟨u, _, edge⟩ := select.function.2.1 r hr
    obtain ⟨B, s, pair⟩ := select.values r u edge
    exact ⟨s, α, t, r, u, B, seq.2.2.1, input, ⟨p, pp, pr⟩, edge, pair⟩
  have functional : M.IsClassFunctionOnSequencesInBelow I (wi_drive_schema.denote η) Ω Z := by
    intro H seq
    obtain ⟨s, hs⟩ := total H seq
    refine ⟨s, (sat H s).mpr hs, fun v hv => ?_⟩
    obtain ⟨_, α, _, seq⟩ := seq
    exact ((sat H v).mp hv).unique_l (ZF.modelsKP hZF) ⟨seq.1, seq.2.1, seq.2.2.1⟩ ff.1 pf.1 hs
  have into : M.MapsSequencesInBelowInto I (wi_drive_schema.denote η) Ω Z := by
    intro H s _ hs
    obtain ⟨_, _, r, u, _, _, _, _, edge, pair⟩ := (sat H s).mp hs
    exact (pair.mem_l M zt (select.function.bound_l edge).2).2
  obtain ⟨H, run, unique⟩ := ZF.recursiveSequenceIn_existsUnique hZF I η wi_drive_schema hΩ functional into
  have convert K : M.IsRecursiveSequenceIn I (wi_drive_schema.denote η) K Ω Z ↔ Wi_run_d hZF o Ψ F Ω Z K := by
    refine and_congr_right fun _ => forall_congr' fun i => imp_congr_right fun hi => forall_congr' fun s => imp_congr_right fun edge => ?_
    exact exists_congr fun J => and_congr_right fun _ => sat J s
  exact ⟨H, (convert H).mp run, fun K hk => unique K ((convert K).mpr hk)⟩

end YesMetaZFC.SetTheory.LargeCardinal

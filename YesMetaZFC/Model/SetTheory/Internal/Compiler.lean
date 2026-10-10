import YesMetaZFC.Model.SetTheory.Internal.CompileSemantics

/-! # 原 Project 公式的内部编译

结构归纳只用于输入的原 AST；输出始终是模型内的实际合法指令图。每一步
保留旧程序并给出对全部集合结构的语义证书，量词的新编号由内部后继取得。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

private theorem true_compile_l (hZF : M.Models ZF) {d ω σ n F} (hω : M.IsOmega ω)
    (v : Fin d → M.Domain) (hσ : M.mem σ ω) (hF : Sfm_d I ω n F) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ Scompile_d I ω m G k v (.truth : Formula 0 d) := by
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 1 σ σ
  obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF (Or.inr (Or.inl ⟨σ, σ, hc, hσ, hσ⟩))
  refine ⟨m, G, n, h, fun X R hX E hE f hf ρ _ => ?_⟩
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
  obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 σ hσ
  simp only [Definitional.Semantics.satisfies]
  exact (ssat_eq_l I hZF h.program hH he hc hE hf hx hx).trans ⟨fun _ => trivial, fun _ => rfl⟩

/-- 在任意已有合法程序后编译第 0 层 AST；同一输出对所有模型及参数赋值有效。 -/
theorem source_compile_core_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω)
    {d} (φ : Formula 0 d) (hφ : φ.FreeClosed) {σ n F} (v : Fin d → M.Domain)
    (hσ : M.mem σ ω) (hv : ∀ i, M.mem (v i) σ) (hF : Sfm_d I ω n F) :
    ∃ m G k, Sbuild_d I ω n F m G k ∧ Scompile_d I ω m G k v φ := by
  induction φ generalizing σ n F <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case truth => exact true_compile_l I hZF hω v hσ hF
  case falsum =>
    obtain ⟨m, G, k, h, hc⟩ := true_compile_l I hZF hω v hσ hF
    obtain ⟨l, H, r, g, hg⟩ := scompile_neg_l I hZF hω h.program h.root hc
    refine ⟨l, H, r, h.comp I g, fun X R hX E hE f hf ρ hρ => ?_⟩
    have he := hg X R hX E hE f hf ρ hρ
    simp only [Definitional.Semantics.satisfies] at he ⊢
    exact he.trans ⟨fun h => h True.intro, False.elim⟩
  case mem s t =>
    cases s with
    | free i => cases hφ.1
    | bound i =>
      cases t with
      | free j => cases hφ.2
      | bound j =>
        obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 0 (v i) (v j)
        obtain ⟨m, G, h, he⟩ := sfm_node_build_l I hZF hω hF
          (Or.inl ⟨v i, v j, hc, hω.transitive hZF σ hσ _ (hv i), hω.transitive hZF σ hσ _ (hv j)⟩)
        refine ⟨m, G, n, h, fun X R hX E hE f hf ρ hρ => ?_⟩
        obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G h.program.2.1.1
        simp only [Definitional.Semantics.satisfies, Definitional.Term.eval]
        unfold smdl_structure_l
        exact ssat_rel_l I hZF h.program hH he hc hE hf (hρ i) (hρ j)
  case atom r hr ts =>
    have hh : (0 : Nat) < 0 := hr
    omega
  case neg φ ih =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ v hσ hv hF
    obtain ⟨l, H, r, g, hg⟩ := scompile_neg_l I hZF hω h.program h.root hc
    exact ⟨l, H, r, h.comp I g, hg⟩
  case conj φ ψ ih jh =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ.1 v hσ hv hF
    obtain ⟨l, H, r, g, hd⟩ := jh hφ.2 v hσ hv h.program
    have hc' := hc.extend_l I hZF h.program g h.root
    obtain ⟨s, J, q, b, hb⟩ := sfm_and_l I hZF hω g.program (g.span k h.root) g.root
    refine ⟨s, J, q, (h.comp I g).comp I b, fun X R hX E hE f hf ρ hρ => ?_⟩
    simpa only [Definitional.Semantics.satisfies] using (hb X R E f hf).trans
      (and_congr (hc' X R hX E hE f hf ρ hρ) (hd X R hX E hE f hf ρ hρ))
  case disj φ ψ ih jh =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ.1 v hσ hv hF
    obtain ⟨l, H, r, g, hd⟩ := jh hφ.2 v hσ hv h.program
    have hc' := hc.extend_l I hZF h.program g h.root
    obtain ⟨s, J, q, b, hb⟩ := sfm_or_l I hZF hω g.program (g.span k h.root) g.root
    refine ⟨s, J, q, (h.comp I g).comp I b, fun X R hX E hE f hf ρ hρ => ?_⟩
    simpa only [Definitional.Semantics.satisfies] using (hb X R E f hf).trans
      (or_congr (hc' X R hX E hE f hf ρ hρ) (hd X R hX E hE f hf ρ hρ))
  case imp φ ψ ih jh =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ.1 v hσ hv hF
    obtain ⟨l, H, r, g, hd⟩ := jh hφ.2 v hσ hv h.program
    have hc' := hc.extend_l I hZF h.program g h.root
    obtain ⟨s, J, q, b, hb⟩ := sfm_imp_l I hZF hω g.program (g.span k h.root) g.root
    refine ⟨s, J, q, (h.comp I g).comp I b, fun X R hX E hE f hf ρ hρ => ?_⟩
    simpa only [Definitional.Semantics.satisfies] using (hb X R E f hf).trans
      (imp_congr (hc' X R hX E hE f hf ρ hρ) (hd X R hX E hE f hf ρ hρ))
  case iff φ ψ ih jh =>
    obtain ⟨m, G, k, h, hc⟩ := ih hφ.1 v hσ hv hF
    obtain ⟨l, H, r, g, hd⟩ := jh hφ.2 v hσ hv h.program
    have hc' := hc.extend_l I hZF h.program g h.root
    obtain ⟨s, J, q, b, hb⟩ := sfm_iff_l I hZF hω g.program (g.span k h.root) g.root
    refine ⟨s, J, q, (h.comp I g).comp I b, fun X R hX E hE f hf ρ hρ => ?_⟩
    simpa only [Definitional.Semantics.satisfies] using (hb X R E f hf).trans
      (iff_congr (hc' X R hX E hE f hf ρ hρ) (hd X R hX E hE f hf ρ hρ))
  case existsE φ ih =>
    obtain ⟨τ, ht, htω⟩ := hω.1.2 σ hσ
    have hV : ∀ i, M.mem (Fin.cases σ v i) τ :=
      Fin.cases ht.predecessor_mem (fun i => (ht (v i)).mpr (Or.inl (hv i)))
    obtain ⟨m, G, k, h, hc⟩ := ih hφ (Fin.cases σ v) htω hV hF
    obtain ⟨l, H, r, g, hg⟩ := scompile_ex_l I hZF hω h.program h.root hσ
      (fun i hi => by
        have hh := hv i
        rw [hi] at hh
        exact KP.mem_irrefl_d (ZF.modelsKP hZF) σ hh) hc
    exact ⟨l, H, r, h.comp I g, hg⟩
  case forallE φ ih =>
    obtain ⟨τ, ht, htω⟩ := hω.1.2 σ hσ
    have hV : ∀ i, M.mem (Fin.cases σ v i) τ :=
      Fin.cases ht.predecessor_mem (fun i => (ht (v i)).mpr (Or.inl (hv i)))
    obtain ⟨m, G, k, h, hc⟩ := ih hφ (Fin.cases σ v) htω hV hF
    obtain ⟨l, H, r, g, hg⟩ := scompile_neg_l I hZF hω h.program h.root hc
    obtain ⟨s, J, q, b, hb⟩ := scompile_ex_l I hZF hω g.program g.root hσ
      (fun i hi => by
        have hh := hv i
        rw [hi] at hh
        exact KP.mem_irrefl_d (ZF.modelsKP hZF) σ hh) hg
    obtain ⟨z, K, w, e, he⟩ := scompile_neg_l I hZF hω b.program b.root hb
    refine ⟨z, K, w, ((h.comp I g).comp I b).comp I e, fun X R hX E hE f hf ρ hρ => ?_⟩
    have hh := he X R hX E hE f hf ρ hρ
    simp only [Definitional.Semantics.satisfies] at hh ⊢
    exact hh.trans ⟨fun hn x => Classical.byContradiction (fun hx => hn ⟨x, hx⟩), fun h ⟨x, hx⟩ => hx (h x)⟩

/-- 原 AST 一次编译成实际内部公式码，并给出规范参数编号及全模型语义对应。 -/
theorem source_compile_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) {a d}
    (φ : Formula a d) (hφ : φ.FreeClosed) : ∃ c n F k, ∃ v : Fin d → M.Domain,
    Sformula_d I ω c n F k ∧ (∀ i, Num_d i.val (v i)) ∧ Scompile_d I ω n F k v φ := by
  -- 有限组数码只在存在命题中取见证，不从存在性证明提取模型数据。
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice (fun i : Fin d => num_exists_l (ZF.modelsKP hZF) i.val)
  obtain ⟨σ, hσ⟩ := num_exists_l (ZF.modelsKP hZF) d
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hf : Sfm_d I ω e e := ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he),
    Structure.IsSequenceOfLength.empty I he, fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
  obtain ⟨n, F, k, h, hc⟩ := source_compile_core_l I hZF hω (source_core_l φ) (source_core_closed_l φ hφ)
    v (num_mem_l hZF.1 hω hσ) (fun i => num_lt_l hZF.1 (hv i) hσ i.isLt) hf
  obtain ⟨c, hcF⟩ := I.total F k
  exact ⟨c, n, F, k, v, ⟨hcF, h.program, h.root⟩, hv,
    fun X R hX E hE f hf ρ hρ => (hc X R hX E hE f hf ρ hρ).trans (source_core_sat_l φ ρ)⟩

/-- 指定编码模型及原公式参数后，自动生成公式码、内部赋值和精确满足等价式。 -/
theorem source_satisfaction_l (hZF : M.Models ZF) {ω c X R} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) {d} (φ : Formula 1 d) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) hM.2.1) d) : ∃ a E f,
      (∃ n F k, Sformula_d I ω a n F k) ∧ M.IsFunctionSpace I E ω X ∧ M.mem f E ∧
        (Satisfies_d I ω c a f ↔ Formula.satisfies ρ φ) := by
  obtain ⟨a, n, F, k, v, ha, hv, hc⟩ := source_compile_l I hZF hω φ hφ
  obtain ⟨E, hE, _⟩ := senv_space_l I hZF ω hM.2.1
  have hinj : Function.Injective v := by
    intro i j he
    have hj := hv j
    rw [← he] at hj
    exact Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) hj)
  obtain ⟨f, hf, hp⟩ := senv_params_l I hZF hE hM.2.1 v (fun i => (ρ.bound i).val) hinj
    (fun i => num_mem_l hZF.1 hω (hv i)) (fun i => (ρ.bound i).property)
  exact ⟨a, E, f, ⟨n, F, k, ha⟩, hE, hf,
    (satisfies_decode_l I hZF.1 hM ha hE).trans (hc X R hM.2.1 E hE f hf ρ hp)⟩

end YesMetaZFC.SetTheory.Internal

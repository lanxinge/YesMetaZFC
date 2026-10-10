import YesMetaZFC.Model.Forcing.Iteration.Closed.Successor
import YesMetaZFC.Model.Forcing.Iteration.Names.ProjectionName

/-! # 保留指定前缀的可数闭区间

区间性质量化真实内部下降链及共同旧前缀，返回精确保留该前缀的整链下界。
限制函数图给出链投影；恒等、相邻后继与区间复合均直接构造实际见证。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_chain_lower_d (I : kpair_convention_l.Interpretation M) (α R f p : M.Domain) : Prop :=
  ∀ i r a, Entry_d M i r f → M.IsRestrictionOf I a r α → Entry_d M p a R

def row_chain_lower_m {n} (α R f p : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.imp (entry_m (.bound 2) (.bound 1) f.weaken.weaken.weaken)
    (.imp (Formula.isRestriction kpair_convention_l .newest (.bound 1) α.weaken.weaken.weaken)
      (entry_m p.weaken.weaken.weaken .newest R.weaken.weaken.weaken)))))
derive_free_closed row_chain_lower_m

theorem row_chain_lower_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α R f p : Term n) : Formula.satisfies ρ (row_chain_lower_m α R f p) ↔
      Row_chain_lower_d I (α.eval ρ) (R.eval ρ) (f.eval ρ) (p.eval ρ) := by
  simp only [row_chain_lower_m, Row_chain_lower_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_sat_l M hE, Formula.satisfies_isRestriction_iff I, Definitional.Term.eval_weaken]
  rfl

def Row_cl_d (I : kpair_convention_l.Interpretation M) (ω α B R D V : M.Domain) : Prop :=
  ∀ f p, Chain_d I D V D ω f → M.mem p B → Row_chain_lower_d I α R f p →
    ∃ q, M.mem q D ∧ M.IsRestrictionOf I p q α ∧ ∀ i r, Entry_d M i r f → Entry_d M q r V

def row_cl_m {n} (ω α B R D V : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (chain_m D.weaken.weaken V.weaken.weaken D.weaken.weaken ω.weaken.weaken (.bound 1))
    (.imp (.mem .newest B.weaken.weaken)
      (.imp (row_chain_lower_m α.weaken.weaken R.weaken.weaken (.bound 1) .newest)
        (.existsE (.conj (.mem .newest D.weaken.weaken.weaken)
          (.conj (Formula.isRestriction kpair_convention_l (.bound 1) .newest α.weaken.weaken.weaken)
            (.forallE (.forallE (.imp (entry_m (.bound 1) .newest (.bound 4))
              (entry_m (.bound 2) .newest V.weaken.weaken.weaken.weaken.weaken)))))))))))
derive_free_closed row_cl_m

theorem row_cl_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω α B R D V : Term n) : Formula.satisfies ρ (row_cl_m ω α B R D V) ↔
      Row_cl_d I (ω.eval ρ) (α.eval ρ) (B.eval ρ) (R.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_cl_m, Row_cl_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    chain_sat_l I hE, Formula.satisfies_mem_iff, row_chain_lower_sat_l I hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_isRestriction_iff I,
    entry_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

def Row_cl_stage_d (I : kpair_convention_l.Interpretation M) (ω F G β : M.Domain) : Prop :=
  ∀ α B R D V, M.MemberSubset α β → Entry_d M α B F → Entry_d M α R G →
    Entry_d M β D F → Entry_d M β V G → Row_cl_d I ω α B R D V

def row_cl_stage_m {n} (ω F G β : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (Formula.subset (.bound 4) β.weaken.weaken.weaken.weaken.weaken)
      (.imp (entry_m (.bound 4) (.bound 3) F.weaken.weaken.weaken.weaken.weaken)
        (.imp (entry_m (.bound 4) (.bound 2) G.weaken.weaken.weaken.weaken.weaken)
          (.imp (entry_m β.weaken.weaken.weaken.weaken.weaken (.bound 1) F.weaken.weaken.weaken.weaken.weaken)
            (.imp (entry_m β.weaken.weaken.weaken.weaken.weaken .newest G.weaken.weaken.weaken.weaken.weaken)
              (row_cl_m ω.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))))))
derive_free_closed row_cl_stage_m

theorem row_cl_stage_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω F G β : Term n) : Formula.satisfies ρ (row_cl_stage_m ω F G β) ↔
      Row_cl_stage_d I (ω.eval ρ) (F.eval ρ) (G.eval ρ) (β.eval ρ) := by
  simp only [row_cl_stage_m, Row_cl_stage_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, entry_sat_l M hE, row_cl_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

/-- 下降链沿原阶段限制投影，输出逐项限制方程和实际下降性。 -/
theorem row_chain_project_l {α B R D V ω f} (k : Row_link_d I α B R D V) (hf : Chain_d I D V D ω f) :
    ∃ g, Chain_d I B R B ω g ∧ ∀ i a, Entry_d M i a g ↔ ∃ r, Entry_d M i r f ∧ M.IsRestrictionOf I a r α := by
  obtain ⟨P, hP⟩ := row_proj_exists_l hZF k
  obtain ⟨g, hg, hGraph⟩ := ZF.exists_compositionFunction hZF I hf.1 hP.1
  have edge i a : Entry_d M i a g ↔ ∃ r, Entry_d M i r f ∧ M.IsRestrictionOf I a r α := by
    change (M.PairMember I i a g ↔ _)
    rw [hGraph i a]
    exact ⟨fun ⟨_, r, hir, hra⟩ => ⟨r, hir, ((hP.2 r a).mp hra).2⟩,
      fun ⟨r, hir, hra⟩ => ⟨hf.1.input_mem_of_pairMember hir, r, hir,
        (hP.2 r a).mpr ⟨hf.1.output_mem_of_pairMember hir, hra⟩⟩⟩
  refine ⟨g, ⟨hg, fun i a hia he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hg.output_mem_of_pairMember hia),
    fun i j a b hij hia hjb => ?_⟩, edge⟩
  obtain ⟨r, hir, har⟩ := (edge i a).mp hia
  obtain ⟨s, hjs, hbs⟩ := (edge j b).mp hjb
  exact k.mono s r b a (hf.1.output_mem_of_pairMember hjs) (hf.1.output_mem_of_pairMember hir)
    hbs har (hf.2.2 i j r s hij hir hjs)

omit hZF in
theorem row_cl_id_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {ω α B R b}
    (h : Row_stage_d M α B R b) : Row_cl_d (kpair_interpretation_l M hE hP) ω α B R B R := by
  have self p (hp : M.mem p B) : M.IsRestrictionOf (kpair_interpretation_l M hE hP) p p α :=
    ⟨(h.rows p hp).graph, fun i s => ⟨fun his => ⟨(h.rows p hp).domain i s his, his⟩, And.right⟩⟩
  exact fun f p hf hp hpf => ⟨p, hp, self p hp, fun i r hir => hpf i r r hir (self r (hf.1.output_mem_of_pairMember hir))⟩

/-- 在较短闭区间内构造下界，同时保存对原长链的全部前缀比较。 -/
theorem row_cl_project_l {ω α β B R C S D V f p} (hαβ : M.MemberSubset α β)
    (k : Row_link_d I β C S D V) (h₁ : Row_cl_d I ω α B R C S)
    (hf : Chain_d I D V D ω f) (hp : M.mem p B) (hpf : Row_chain_lower_d I α R f p) :
    ∃ a, M.mem a C ∧ M.IsRestrictionOf I p a α ∧ Row_chain_lower_d I β S f a := by
  obtain ⟨g, hg, he⟩ := row_chain_project_l hZF k hf
  obtain ⟨a, ha, hpa, hag⟩ := h₁ g p hg hp (fun i r b hir hbr => by
    obtain ⟨s, his, hrs⟩ := (he i r).mp hir
    exact hpf i s b his (hbr.comp_l hrs hαβ))
  exact ⟨a, ha, hpa, fun i r b hir hbr => hag i b ((he i b).mpr ⟨r, hir, hbr⟩)⟩

/-- 两段保留前缀的闭区间复合；中间链由实际投影图生成。 -/
theorem row_cl_comp_l {ω α β B R C S D V} (hαβ : M.MemberSubset α β)
    (k : Row_link_d I β C S D V) (h₁ : Row_cl_d I ω α B R C S) (h₂ : Row_cl_d I ω β C S D V) :
    Row_cl_d I ω α B R D V := by
  intro f p hf hp hpf
  obtain ⟨a, ha, hpa, hpf'⟩ := row_cl_project_l hZF hαβ k h₁ hf hp hpf
  obtain ⟨q, hq, haq, hqf⟩ := h₂ f a hf ha hpf'
  exact ⟨q, hq, hpa.comp_l haq hαβ, hqf⟩

omit hZF in
/-- 已构造的名称后继是完整的闭区间；不要求先给首阶段闭性。 -/
theorem row_cl_next_l (hZFC : M.Models ZFC) {ω α B R b A T t D V w}
    (h : Row_stage_d M α B R b) (hNext : Row_next_d M α B R b A T t D V)
    (L : Cond_order_d M D V D) (hT : Name_d M B T) (hω : M.IsOmega ω) (hw : Check_d M b ω w)
    (hc : Forces_d M B R B (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) b) :
    Row_cl_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω α B R D V := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨W, C, S, hW, hs, hk⟩ := hNext
  have hA : Name_d M B A := ⟨W, hs.root, hs.closed⟩
  have hwN := check_name_l M (check_range_l M hZF) h.base hw
  have hn : ∀ a : Term 3, Name_d M B
      (a.eval (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T)) := by
    intro a
    cases a with
    | free _ => exact hwN
    | bound i => exact Fin.cases hT (Fin.cases hA (fun _ => hwN)) i
  intro f p hf hp hpf
  have hp' := below_refl_l h.order hp (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp))
  exact row_next_chain_bound_l hZFC h ⟨W, C, S, hW, hs, hk⟩ L hT hω hw hf hp hpf
    ((forces_regular_l h.order hZF _ _ hn).1 b p h.base ⟨hp, hp'.2.1, h.top p hp⟩ hc)

end YesMetaZFC.Model.Forcing.Internal

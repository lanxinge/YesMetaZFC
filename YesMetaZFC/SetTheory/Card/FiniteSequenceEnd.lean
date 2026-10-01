import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax

/-! # 内部有限列的末项编码

末项分解以实际公式表示，唯一性来自长度、前驱和限制图的唯一性。
供有限元运算把额外的条件参数与原名称列一起编码。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fseq_end_d (ω F f p : M.Domain) : Prop := ∃ n m,
  M.IsFiniteSequenceLastDecomposition I ω F n m f p

def fseq_end_m {d} (ω F f p : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (.mem (.bound 1) ω.weaken.weaken) (.conj
    (Formula.isSequenceOfLength 𝒞 F.weaken.weaken (.bound 1)) (.conj
    (.mem .newest ω.weaken.weaken) (.conj (Formula.isSuccessor (.bound 1) .newest) (.conj
    (Formula.isSequenceOfLength 𝒞 f.weaken.weaken .newest) (.conj
    (Formula.isRestriction 𝒞 f.weaken.weaken F.weaken.weaken .newest)
    (Formula.orderedPairMem 𝒞 .newest p.weaken.weaken F.weaken.weaken))))))))
derive_free_closed fseq_end_m

theorem fseq_end_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω F f p : Term d) :
    Formula.satisfies ρ (fseq_end_m (𝒞 := 𝒞) ω F f p) ↔
      Fseq_end_d I (ω.eval ρ) (F.eval ρ) (f.eval ρ) (p.eval ρ) := by
  simp only [fseq_end_m, Fseq_end_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSequenceOfLength_iff I hE,
    Formula.satisfies_isSuccessor_iff, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  apply exists_congr
  intro n
  apply exists_congr
  intro m
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1,
      ⟨h.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
    fun h => ⟨h.source.1, h.source.2, h.predecessor_mem_omega, h.length_successor,
      h.prefix_sequence.2, h.prefix_restriction, h.last_value⟩⟩

theorem fseq_end_unique_l (hE : Extensional M) {ω F f p g q}
    (h : Fseq_end_d I ω F f p) (k : Fseq_end_d I ω F g q) : f = g ∧ p = q := by
  obtain ⟨n, m, h⟩ := h
  obtain ⟨n', m', k⟩ := k
  have he := h.source.length_unique hE k.source
  subst n'
  exact (h.components_unique hE k).2

/-- 相同前缀和末项决定唯一的内部有限列；长度也从前缀图中恢复。 -/
theorem fseq_end_rebuild_l (hE : Extensional M) {ω F G f p}
    (h : Fseq_end_d I ω F f p) (k : Fseq_end_d I ω G f p) : F = G := by
  obtain ⟨n, m, h⟩ := h
  obtain ⟨n', m', k⟩ := k
  have hm := h.prefix_sequence.length_unique hE k.prefix_sequence
  subst m'
  have hn := hE.eq_of_same_members n n' (fun x => (h.length_successor x).trans (k.length_successor x).symm)
  subst n'
  exact h.sequence_unique_of_components hE k

/-- 将一项追加到内部有限参数列；新增图仍取值于同一集合。 -/
theorem ZF.fseq_end_exists_l (hZF : M.Models ZF) {ω n f X p} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hf : M.IsSetFunctionFromTo I f n X) (hp : M.mem p X) :
    ∃ m F, M.mem m ω ∧ M.IsSetFunctionFromTo I F m X ∧ Fseq_end_d I ω F f p := by
  obtain ⟨m, hm, hmω⟩ := hω.1.2 n hn
  obtain ⟨F, hF, hFf⟩ := Structure.IsSequenceOfLength.exists_append (value := p)
    (modelsKP hZF) I ⟨(hω.isOrdinal hZF).mem hn, hf.1, hf.2.1⟩ ((hω.isOrdinal hZF).mem hmω) hm
  have hr : M.IsRestrictionOf I f F n := by
    refine ⟨hf.1.1, fun i x => ?_⟩
    constructor
    · exact fun hi => ⟨hf.input_mem_of_pairMember hi, (hFf i x).mpr (Or.inl hi)⟩
    · rintro ⟨hi, hx⟩
      rcases (hFf i x).mp hx with hx | ⟨rfl, _⟩
      · exact hx
      · exact ((hω.isOrdinal hZF).mem hn).wellOrder.linear.irrefl _ hi hi |>.elim
  refine ⟨m, F, hmω, ⟨hF.2.1, hF.2.2, fun i hi => ?_⟩, m, n,
    ⟨⟨hmω, hF⟩, hn, hm, ⟨hn, (hω.isOrdinal hZF).mem hn, hf.1, hf.2.1⟩, hr,
      (hFf n p).mpr (Or.inr ⟨rfl, rfl⟩)⟩⟩
  obtain ⟨x, hx⟩ := (hF.2.2 i).mp hi
  refine ⟨x, ?_, hx⟩
  exact ((hFf i x).mp hx).elim hf.output_mem_of_pairMember (fun h => h.2.symm ▸ hp)

end YesMetaZFC.SetTheory

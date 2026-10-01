import YesMetaZFC.Model.SetTheory.Internal.Satisfaction

/-! # 有限参数列的完整赋值

把定义域为内部自然数 n 的参数列延拓到 ω，域外统一取指定基点 u。延拓图
由原公式构造且字面唯一；随后可在任意变量位置施行已有的单坐标更新。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Senv_fill_d (ω u n s f : M.Domain) : Prop :=
  M.IsSetRelation I f ∧ ∀ i x, M.PairMember I i x f ↔ M.mem i ω ∧
    ((M.mem i n ∧ M.PairMember I i x s) ∨ (¬ M.mem i n ∧ x = u))

def senv_fill_m {d} (ω u n s f : Term d) : Formula 1 d :=
  .conj (Formula.isRelation 𝒞 f) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken) (.conj (.mem (.bound 1) ω.weaken.weaken)
      (.disj (.conj (.mem (.bound 1) n.weaken.weaken) (Formula.orderedPairMem 𝒞 (.bound 1) .newest s.weaken.weaken))
        (.conj (.neg (.mem (.bound 1) n.weaken.weaken)) (Formula.extensionalEq .newest u.weaken.weaken)))))))
derive_free_closed senv_fill_m

theorem senv_fill_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω u n s f : Term d) :
    Formula.satisfies ρ (senv_fill_m (𝒞 := 𝒞) ω u n s f) ↔
      Senv_fill_d I (ω.eval ρ) (u.eval ρ) (n.eval ρ) (s.eval ρ) (f.eval ρ) := by
  simp only [senv_fill_m, Senv_fill_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]
  rfl

theorem senv_fill_unique_l (hE : Extensional M) {ω u n s f g}
    (hf : Senv_fill_d I ω u n s f) (hg : Senv_fill_d I ω u n s g) : f = g :=
  hf.1.eq_of_pairMember_iff hE hg.1 (fun i x => (hf.2 i x).trans (hg.2 i x).symm)

theorem Senv_fill_d.function_l {ω X u n s f} (hf : Senv_fill_d I ω u n s f)
    (hs : M.IsSetFunctionFromTo I s n X) (hu : M.mem u X) : M.IsSetFunctionFromTo I f ω X := by
  classical
  have total i (hi : M.mem i ω) : ∃ x, M.mem x X ∧ M.PairMember I i x f := by
    by_cases hn : M.mem i n
    · obtain ⟨x, hx, hix⟩ := hs.2.2 i hn
      exact ⟨x, hx, (hf.2 i x).mpr ⟨hi, Or.inl ⟨hn, hix⟩⟩⟩
    · exact ⟨u, hu, (hf.2 i u).mpr ⟨hi, Or.inr ⟨hn, rfl⟩⟩⟩
  refine ⟨⟨hf.1, ?_⟩, fun i => ⟨fun hi => (total i hi).elim fun x hx => ⟨x, hx.2⟩,
    fun ⟨x, hx⟩ => ((hf.2 i x).mp hx).1⟩, total⟩
  intro i x y hx hy
  rcases ((hf.2 i x).mp hx).2 with ⟨hn, hx⟩ | ⟨hn, rfl⟩ <;>
    rcases ((hf.2 i y).mp hy).2 with ⟨hn', hy⟩ | ⟨hn', rfl⟩
  · exact hs.1.2 i x y hx hy
  · exact (hn' hn).elim
  · exact (hn hn').elim
  · rfl

theorem senv_fill_exists_l (hZF : M.Models ZF) {ω X u n s}
    (hs : M.IsSetFunctionFromTo I s n X) (hu : M.mem u X) :
    ∃ f, Senv_fill_d I ω u n s f ∧ M.IsSetFunctionFromTo I f ω X := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => s, fun _ => s⟩ : Env M 1).push n).push u
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 3)) (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)))
      (.conj (.neg (.mem (.bound 1) (.bound 3))) (Formula.extensionalEq .newest (.bound 2))) }
  have hφ i x : φ.denote ρ i x ↔ (M.mem i n ∧ M.PairMember I i x s) ∨ (¬ M.mem i n ∧ x = u) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  obtain ⟨f, hf, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X) (by
    intro i _
    by_cases hi : M.mem i n
    · obtain ⟨x, _, hx⟩ := hs.2.2 i hi
      exact ⟨x, (hφ i x).mpr (Or.inl ⟨hi, hx⟩)⟩
    · exact ⟨u, (hφ i u).mpr (Or.inr ⟨hi, rfl⟩)⟩) (by
    intro i _ x y hx hy
    rcases (hφ i x).mp hx with ⟨hi, hx⟩ | ⟨hi, rfl⟩ <;>
      rcases (hφ i y).mp hy with ⟨hi', hy⟩ | ⟨hi', rfl⟩
    · exact hs.1.2 i x y hx hy
    · exact (hi' hi).elim
    · exact (hi hi').elim
    · rfl) (by
    intro i x _ hx
    exact ((hφ i x).mp hx).elim (fun hx => hs.output_mem_of_pairMember hx.2) (fun hx => hx.2.symm ▸ hu))
  exact ⟨f, ⟨hf.1.1, fun i x => (he i x).trans (and_congr_right fun _ => hφ i x)⟩, hf⟩

end YesMetaZFC.SetTheory.Internal

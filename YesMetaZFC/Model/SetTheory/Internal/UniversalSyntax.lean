import YesMetaZFC.Model.SetTheory.Internal.Builder
import YesMetaZFC.Model.SetTheory.Internal.Support

/-! # 全称闭包的内部赋值规格

量化坐标 b 以下的变量后，只固定其余坐标。全部条件均有实际原公式，
供对象 ω 上的归纳使用；b 不要求是外部标准自然数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Senv_tail_d (ω b f g : M.Domain) : Prop := ∀ i, M.mem i ω → ¬ M.mem i b →
  ∀ x, M.PairMember I i x f ↔ M.PairMember I i x g

def senv_tail_m {d} (ω b f g : Term d) : Formula 1 d := Formula.forallMem ω
  (.imp (.neg (.mem .newest b.weaken)) (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken)
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken))))
derive_free_closed senv_tail_m

theorem senv_tail_sat_l {d} (ρ : Env M d) (ω b f g : Term d) :
    Formula.satisfies ρ (senv_tail_m (𝒞 := 𝒞) ω b f g) ↔
      Senv_tail_d I (ω.eval ρ) (b.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [senv_tail_m, Senv_tail_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

/-- 拼接两张真实赋值图：b 内取 g，b 外取 f。 -/
theorem senv_patch_l (hZF : M.Models ZF) {ω X b f g : M.Domain}
    (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo I g ω X)
    (hb : M.MemberSubset b ω) : ∃ h, M.IsSetFunctionFromTo I h ω X ∧
      Senv_agree_d I b g h ∧ Senv_tail_d I ω b f h := by
  classical
  let ρ := ((⟨fun _ => b, fun _ => b⟩ : Env M 1).push f).push g
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 4)) (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2)))
      (.conj (.neg (.mem (.bound 1) (.bound 4))) (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))) }
  have sat i x : φ.denote ρ i x ↔ (M.mem i b ∧ M.PairMember I i x g) ∨ (¬ M.mem i b ∧ M.PairMember I i x f) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨h, hh, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X)
    (fun i hi => by
      by_cases h : M.mem i b
      · obtain ⟨x, _, hx⟩ := hg.2.2 i hi
        exact ⟨x, (sat i x).mpr (Or.inl ⟨h, hx⟩)⟩
      · obtain ⟨x, _, hx⟩ := hf.2.2 i hi
        exact ⟨x, (sat i x).mpr (Or.inr ⟨h, hx⟩)⟩)
    (fun i _ x y hx hy => by
      rcases (sat i x).mp hx with ⟨hi, hx⟩ | ⟨hi, hx⟩ <;>
        rcases (sat i y).mp hy with ⟨hj, hy⟩ | ⟨hj, hy⟩
      · exact hg.1.2 i x y hx hy
      · exact (hj hi).elim
      · exact (hi hj).elim
      · exact hf.1.2 i x y hx hy)
    (fun i x _ hx => ((sat i x).mp hx).elim (fun h => hg.output_mem_of_pairMember h.2) (fun h => hf.output_mem_of_pairMember h.2))
  refine ⟨h, hh, fun i x hi => ?_, fun i hi hn x => ?_⟩
  · exact ⟨fun hx => (spec i x).mpr ⟨hb i hi, (sat i x).mpr (Or.inl ⟨hi, hx⟩)⟩,
      fun hx => ((sat i x).mp ((spec i x).mp hx).2).elim And.right (fun h => (h.1 hi).elim)⟩
  · exact ⟨fun hx => (spec i x).mpr ⟨hi, (sat i x).mpr (Or.inr ⟨hn, hx⟩)⟩,
      fun hx => ((sat i x).mp ((spec i x).mp hx).2).elim (fun h => (hn h.1).elim) And.right⟩

def Sall_d (ω b F n r G m k : M.Domain) : Prop := Sfm_d I ω m G ∧ M.mem k m ∧
  ∀ X R E f, M.IsFunctionSpace I E ω X → M.mem f E →
    (Ssat_d I X R E G m k f ↔ ∀ g, M.mem g E → Senv_tail_d I ω b f g → Ssat_d I X R E F n r g)

def sall_m {d} (ω b F n r G m k : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken
  .conj (sfm_m (𝒞 := 𝒞) ω m G) (.conj (.mem k m) (.forallE (.forallE (.forallE (.forallE
    (.imp (Formula.isFunctionSpace 𝒞 (.bound 1) (w ω) (.bound 3)) (.imp (.mem .newest (.bound 1))
      (.iff (ssat_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) (w G) (w m) (w k) .newest)
        (Formula.forallMem (.bound 1) (.imp
          (senv_tail_m (𝒞 := 𝒞) (w ω).weaken (w b).weaken (.bound 1) .newest)
          (ssat_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (w F).weaken (w n).weaken (w r).weaken .newest)))))))))))
@[simp] theorem sall_closed_l {d} (ω b F n r G m k : Term d)
    (hω : ω.freeSupport = []) (hb : b.freeSupport = []) (hF : F.freeSupport = []) (hn : n.freeSupport = [])
    (hr : r.freeSupport = []) (hG : G.freeSupport = []) (hm : m.freeSupport = []) (hk : k.freeSupport = []) :
    (sall_m (𝒞 := 𝒞) ω b F n r G m k).FreeClosed := by
  simp -implicitDefEqProofs [sall_m, Definitional.Formula.FreeClosed, Formula.isFunctionSpace,
    hω, hb, hF, hn, hr, hG, hm, hk]

theorem sall_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b F n r G m k : Term d) :
    Formula.satisfies ρ (sall_m (𝒞 := 𝒞) ω b F n r G m k) ↔
      Sall_d I (ω.eval ρ) (b.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) (G.eval ρ) (m.eval ρ) (k.eval ρ) := by
  simp only [sall_m, Sall_d, Formula.satisfies_conj_iff, sfm_sat_l I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_isFunctionSpace_iff I hE,
    Formula.satisfies_iff_iff, ssat_sat_l I hE, Formula.satisfies_forallMem_iff, senv_tail_sat_l I,
    Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Internal

import YesMetaZFC.SetTheory.Descriptive.Tree.Trace

/-! # 实际连续函数图及逆像

连续性用柱集邻域表达。函数本身是模型内的集合图，供码运算和相对化统一使用。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cov_d (f s t : M.Domain) : Prop := ∀ x y, M.PairMember I x y f → M.MemberSubset t x → M.MemberSubset s y
def cov_m {d} (f s t : Term d) : Formula 1 d := .forallE (.forallE
  (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken)
    (.imp (Formula.subset t.weaken.weaken (.bound 1)) (Formula.subset s.weaken.weaken .newest))))
derive_free_closed cov_m
theorem cov_sat_l {d} (ρ : Env M d) (f s t : Term d) :
    Formula.satisfies ρ (cov_m (𝒞 := 𝒞) f s t) ↔ Cov_d I (f.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [cov_m, Cov_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

def Cont_d (A B f : M.Domain) : Prop := M.IsSetFunctionFromTo I f B B ∧ ∀ x y s,
  M.PairMember I x y f → M.mem s A → M.MemberSubset s y →
    ∃ t, M.mem t A ∧ M.MemberSubset t x ∧ Cov_d I f s t
def cont_m {d} (A B f : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 f B B)
  (.forallE (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) f.weaken.weaken.weaken)
    (.imp (.mem .newest A.weaken.weaken.weaken) (.imp (Formula.subset .newest (.bound 1))
      (Formula.existsMem A.weaken.weaken.weaken (.conj (Formula.subset .newest (.bound 3))
        (cov_m (𝒞 := 𝒞) f.weaken.weaken.weaken.weaken (.bound 1) .newest)))))))))
derive_free_closed cont_m
theorem cont_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A B f : Term d) :
    Formula.satisfies ρ (cont_m (𝒞 := 𝒞) A B f) ↔ Cont_d I (A.eval ρ) (B.eval ρ) (f.eval ρ) := by
  simp only [cont_m, Cont_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, Formula.satisfies_existsMem_iff,
    cov_sat_l I, Definitional.Term.eval_weaken]; rfl

def Ip_d (B f K L : M.Domain) : Prop := ∀ x, M.mem x L ↔ M.mem x B ∧ ∃ y, M.PairMember I x y f ∧ M.mem y K
def ip_m {d} (B f K L : Term d) : Formula 1 d := .forallE (.iff (.mem .newest L.weaken)
  (.conj (.mem .newest B.weaken) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken) (.mem .newest K.weaken.weaken)))))
derive_free_closed ip_m
theorem ip_sat_l {d} (ρ : Env M d) (B f K L : Term d) :
    Formula.satisfies ρ (ip_m (𝒞 := 𝒞) B f K L) ↔ Ip_d I (B.eval ρ) (f.eval ρ) (K.eval ρ) (L.eval ρ) := by
  simp only [ip_m, Ip_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

theorem ip_exists_l (hZF : M.Models ZF) (B f K : M.Domain) : ∃ L, Ip_d I B f K L := by
  let ρ : Env M 2 := (⟨fun _ => f, fun _ => f⟩ : Env M 1).push K
  let φ : UnarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3)) (.mem .newest (.bound 2))) }
  obtain ⟨L, hL⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨L, fun x => ?_⟩
  simpa only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff] using! hL x

theorem ip_mem_l {B f K L x y} (hf : M.IsSetFunctionFromTo I f B B) (h : Ip_d I B f K L)
    (hxy : M.PairMember I x y f) : M.mem x L ↔ M.mem y K :=
  (h x).trans ⟨fun ⟨_, z, hz, hk⟩ => hf.1.2 x z y hz hxy ▸ hk,
    fun hk => ⟨hf.input_mem_of_pairMember hxy, y, hxy, hk⟩⟩

theorem ip_unique_l (hE : Extensional M) {B f K L V} (h : Ip_d I B f K L) (k : Ip_d I B f K V) : L = V :=
  hE.eq_of_same_members L V (fun x => (h x).trans (k x).symm)

theorem ip_compl_l {B f K L U V} (hf : M.IsSetFunctionFromTo I f B B)
    (hK : Ip_d I B f K U) (hL : Ip_d I B f L V) (h : Cm_d B K L) : Cm_d B U V := by
  intro x
  constructor
  · intro hx
    obtain ⟨hxB, y, hxy, hy⟩ := (hL x).mp hx
    exact ⟨hxB, fun hxU => ((h y).mp hy).2 ((ip_mem_l I hf hK hxy).mp hxU)⟩
  · rintro ⟨hx, hn⟩
    obtain ⟨y, hy, hxy⟩ := hf.2.2 x hx
    exact (ip_mem_l I hf hL hxy).mpr ((h y).mpr ⟨hy, fun h => hn ((ip_mem_l I hf hK hxy).mpr h)⟩)

end YesMetaZFC.SetTheory.Descriptive

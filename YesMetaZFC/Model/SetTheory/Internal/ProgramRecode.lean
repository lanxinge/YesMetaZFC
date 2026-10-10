import YesMetaZFC.Model.SetTheory.Internal.FlatProgram
import YesMetaZFC.Model.SetTheory.Internal.FormulaCode
import YesMetaZFC.SetTheory.FunctionRecoding
import YesMetaZFC.SetTheory.Notation

/-! # 内部程序更换有序对编码

保留每行的操作符、参数和编号，只更换实际有序对。整张新程序由一次
内部替代取得，不把内部有限长度转换成宿主列表。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 𝒟 : OrderedPairConvention}
  (I : 𝒞.Interpretation M) (J : 𝒟.Interpretation M)

def Sx_node_d (c d : M.Domain) : Prop := ∃ k p i j q,
  I.Codes c k p ∧ I.Codes p i j ∧ J.Codes q i j ∧ J.Codes d k q

def sx_node_m {n} (c d : Term n) : Formula 1 n := set[n] ⟪∃ k p i j q,
  ⌜𝒞.code⌝ₚ(⌜c⌝ₛ, k, p) ∧ ⌜𝒞.code⌝ₚ(p, i, j) ∧ ⌜𝒟.code⌝ₚ(q, i, j) ∧ ⌜𝒟.code⌝ₚ(⌜d⌝ₛ, k, q)⟫
derive_free_closed sx_node_m

theorem sx_node_sat_l {n} (ρ : Env M n) (c d : Term n) :
    Formula.satisfies ρ (sx_node_m (𝒞 := 𝒞) (𝒟 := 𝒟) c d) ↔ Sx_node_d I J (c.eval ρ) (d.eval ρ) := by
  simp only [sx_node_m, Sx_node_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, J.satisfies_code_iff, Definitional.Term.eval_weaken]; rfl

theorem Sx_node_d.unique_l {c d e} (h : Sx_node_d I J c d) (g : Sx_node_d I J c e) : d = e := by
  obtain ⟨k, p, i, j, q, hc, hp, hq, hd⟩ := h
  obtain ⟨l, s, a, b, t, hc', hs, ht, he⟩ := g
  obtain ⟨rfl, rfl⟩ := I.injective hc hc'
  obtain ⟨rfl, rfl⟩ := I.injective hp hs
  have eq := J.unique hq ht; subst t
  exact J.unique hd he

theorem Sx_node_d.op_l {c d i j} {k : Nat} (h : Sx_node_d I J c d)
    (hs : Sop_d I k c i j) : Sop_d J k d i j := by
  obtain ⟨o, p, a, b, q, hc, hp, hq, hd⟩ := h
  obtain ⟨s, t, ht, hs, hc'⟩ := hs
  obtain ⟨rfl, rfl⟩ := I.injective hc hc'
  obtain ⟨rfl, rfl⟩ := I.injective hp hs
  exact ⟨q, o, ht, hq, hd⟩

theorem Sx_node_d.node_l {ω r c d} (h : Sx_node_d I J c d)
    (hc : Sfm_node_d I ω r c) : Sfm_node_d J ω r d := by
  rcases hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · exact Or.inl ⟨i, j, h.op_l I J hs, hi, hj⟩
  · exact Or.inr (Or.inl ⟨i, j, h.op_l I J hs, hi, hj⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, j, h.op_l I J hs, hi, hj⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, j, h.op_l I J hs, hi, hj⟩))

theorem sx_node_exists_l {ω r c} (h : Sfm_node_d I ω r c) : ∃ d, Sx_node_d I J c d := by
  have op {i j} {k : Nat} (h : Sop_d I k c i j) : ∃ d, Sx_node_d I J c d := by
    obtain ⟨p, o, _, hp, hc⟩ := h
    obtain ⟨q, hq⟩ := J.total i j
    obtain ⟨d, hd⟩ := J.total o q
    exact ⟨d, o, p, i, j, q, hc, hp, hq, hd⟩
  rcases h with ⟨_, _, hs, _, _⟩ | ⟨_, _, hs, _, _⟩ | ⟨_, _, hs, _, _⟩ | ⟨_, _, hs, _, _⟩ <;> exact op hs

def Sx_program_d (F G : M.Domain) : Prop := M.IsSetFunction J G ∧ ∀ r d,
  M.PairMember J r d G ↔ ∃ c, M.PairMember I r c F ∧ Sx_node_d I J c d

def sx_program_m {n} (F G : Term n) : Formula 1 n := set[n] ⟪
  ⌜Formula.isFunction 𝒟⌝ₚ(⌜G⌝ₛ) ∧ (∀ r d,
    (⌜Formula.orderedPairMem 𝒟⌝ₚ(r, d, ⌜G⌝ₛ) ↔ (∃ c,
      ⌜Formula.orderedPairMem 𝒞⌝ₚ(r, c, ⌜F⌝ₛ) ∧ ⌜sx_node_m (𝒞 := 𝒞) (𝒟 := 𝒟)⌝ₚ(c, d))))⟫
derive_free_closed sx_program_m

theorem sx_program_sat_l (hE : Extensional M) {n} (ρ : Env M n) (F G : Term n) :
    Formula.satisfies ρ (sx_program_m (𝒞 := 𝒞) (𝒟 := 𝒟) F G) ↔ Sx_program_d I J (F.eval ρ) (G.eval ρ) := by
  simp only [sx_program_m, Sx_program_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff J hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_orderedPairMem_iff J,
    sx_node_sat_l I J, Definitional.Term.eval_weaken]; rfl

theorem Sx_program_d.program_l {ω n F G} (h : Sx_program_d I J F G) (hf : Sfm_d I ω n F) : Sfm_d J ω n G := by
  refine ⟨hf.1, ⟨hf.2.1.1, h.1, fun r => ⟨?_, ?_⟩⟩, fun r d hd => ?_⟩
  · intro hr
    obtain ⟨c, hc⟩ := (hf.2.1.2.2 r).mp hr
    obtain ⟨d, hd⟩ := sx_node_exists_l I J (hf.2.2 r c hc)
    exact ⟨d, (h.2 r d).mpr ⟨c, hc, hd⟩⟩
  · rintro ⟨d, hd⟩
    obtain ⟨c, hc, _⟩ := (h.2 r d).mp hd
    exact (hf.2.1.2.2 r).mpr ⟨c, hc⟩
  · obtain ⟨c, hc, hd⟩ := (h.2 r d).mp hd
    exact hd.node_l I J (hf.2.2 r c hc)

theorem Sx_program_d.row_l {F G r c d} (h : Sx_program_d I J F G) (hf : M.IsSetFunction I F)
    (hc : M.PairMember I r c F) (hd : M.PairMember J r d G) : Sx_node_d I J c d := by
  obtain ⟨b, hb, code⟩ := (h.2 r d).mp hd
  exact (hf.2 r b c hb hc) ▸ code

theorem sx_program_exists_l (hZF : M.Models ZF) {ω n F} (hω : M.IsOmega ω) (hf : Sfm_d I ω n F) :
    ∃ G, Sx_program_d I J F G := by
  obtain ⟨P, hp⟩ := ZF.exists_cartesianProduct hZF J ω ω
  obtain ⟨Q, hq⟩ := ZF.exists_cartesianProduct hZF J ω P
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
    (sx_node_m (𝒞 := 𝒞) (𝒟 := 𝒟) .newest (.bound 1))) }
  have sat r d : φ.denote ρ r d ↔ ∃ c, M.PairMember I r c F ∧ Sx_node_d I J c d := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, sx_node_sat_l I J]; rfl
  obtain ⟨G, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF J φ ρ (source := n) (target := Q) (by
    intro r hr
    obtain ⟨c, hc⟩ := (hf.2.1.2.2 r).mp hr
    obtain ⟨d, hd⟩ := sx_node_exists_l I J (hf.2.2 r c hc)
    exact ⟨d, (sat r d).mpr ⟨c, hc, hd⟩⟩) (by
      intro r _ d e hd he
      obtain ⟨c, hc, hd⟩ := (sat r d).mp hd
      obtain ⟨b, hb, he⟩ := (sat r e).mp he
      have eq := hf.2.1.2.1.2 r b c hb hc; subst b
      exact hd.unique_l I J he) (by
        intro r d hr hd
        obtain ⟨c, hc, hd⟩ := (sat r d).mp hd
        exact sfm_node_mem_l J hZF hω hp hq (hω.transitive hZF n hf.1 r hr) (hd.node_l I J (hf.2.2 r c hc)))
  refine ⟨G, fn.1, fun r d => (graph r d).trans ⟨fun h => (sat r d).mp h.2, ?_⟩⟩
  rintro ⟨c, hc, hd⟩
  exact ⟨(hf.2.1.2.2 r).mpr ⟨c, hc⟩, (sat r d).mpr ⟨c, hc, hd⟩⟩

end YesMetaZFC.SetTheory.Internal

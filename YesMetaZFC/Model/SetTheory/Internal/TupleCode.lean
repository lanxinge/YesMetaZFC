import YesMetaZFC.Model.SetTheory.Types.FlatSatisfaction
import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.FunctionRecoding
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.Model.SetTheory.Types.CanonicalSource
import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.SetTheory.FlatPairing.RankObjects
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Reflection.RankLargest
import YesMetaZFC.SetTheory.FlatPairing.RecursionSource
import YesMetaZFC.SetTheory.FlatPairing.SequenceSource

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
        exact sfm_node_mem_l J hZF hω hp hq (hω.transitive (ZF.modelsKP hZF) n hf.1 r hr) (hd.node_l I J (hf.2.2 r c hc)))
  refine ⟨G, fn.1, fun r d => (graph r d).trans ⟨fun h => (sat r d).mp h.2, ?_⟩⟩
  rintro ⟨c, hc, hd⟩
  exact ⟨(hf.2.1.2.2 r).mpr ⟨c, hc⟩, (sat r d).mpr ⟨c, hc, hd⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 更换程序编码保持全部内部公式的真值

对原程序作内部强归纳。存在量词在两种赋值编码上同时更新同一个坐标，
因此并非只证明无量词片段或外部标准公式的保持性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 𝒟 : OrderedPairConvention}
  (I : 𝒞.Interpretation M) (J : 𝒟.Interpretation M)

def Sx_graph_d (F G : M.Domain) : Prop := ∀ x y, M.PairMember J x y G ↔ M.PairMember I x y F

def sx_graph_m {n} (F G : Term n) : Formula 1 n := set[n] ⟪∀ x y,
  (⌜Formula.orderedPairMem 𝒟⌝ₚ(x, y, ⌜G⌝ₛ) ↔ ⌜Formula.orderedPairMem 𝒞⌝ₚ(x, y, ⌜F⌝ₛ))⟫
derive_free_closed sx_graph_m

theorem sx_graph_sat_l {n} (ρ : Env M n) (F G : Term n) :
    Formula.satisfies ρ (sx_graph_m (𝒞 := 𝒞) (𝒟 := 𝒟) F G) ↔ Sx_graph_d I J (F.eval ρ) (G.eval ρ) := by
  simp only [sx_graph_m, Sx_graph_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_orderedPairMem_iff J, Definitional.Term.eval_weaken]; rfl

theorem Sx_graph_d.update_l {f g i x a b} (h : Sx_graph_d I J f g)
    (ha : Senv_update_d I f i x a) (hb : Senv_update_d J g i x b) : Sx_graph_d I J a b :=
  fun j y => (hb.2 j y).trans ((or_congr Iff.rfl (and_congr Iff.rfl (h j y))).trans (ha.2 j y).symm)

def Sx_row_d (X R S E D F G n r : M.Domain) : Prop := ∀ f g,
  M.mem f E → M.mem g D → Sx_graph_d I J f g →
    (Ssat_d I X R E F n r f ↔ Ssat_d J X S D G n r g)

def sx_row_m {d} (X R S E D F G n r : Term d) : Formula 1 d := set[d] ⟪∀ f g,
  f ∈ ⌜E⌝ₛ → g ∈ ⌜D⌝ₛ → ⌜sx_graph_m (𝒞 := 𝒞) (𝒟 := 𝒟)⌝ₚ(f, g) →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜E⌝ₛ, ⌜F⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, f) ↔
      ⌜ssat_m (𝒞 := 𝒟)⌝ₚ(⌜X⌝ₛ, ⌜S⌝ₛ, ⌜D⌝ₛ, ⌜G⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, g))⟫
derive_free_closed sx_row_m

theorem sx_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R S E D F G n r : Term d) :
    Formula.satisfies ρ (sx_row_m (𝒞 := 𝒞) (𝒟 := 𝒟) X R S E D F G n r) ↔
      Sx_row_d I J (X.eval ρ) (R.eval ρ) (S.eval ρ) (E.eval ρ) (D.eval ρ)
        (F.eval ρ) (G.eval ρ) (n.eval ρ) (r.eval ρ) := by
  simp only [sx_row_m, Sx_row_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, sx_graph_sat_l I J, Formula.satisfies_iff_iff,
    ssat_sat_l I hE, ssat_sat_l J hE, Definitional.Term.eval_weaken]; rfl

theorem Sx_program_d.correct_l (hZF : M.Models ZF) {ω X R S E D F G n r}
    (h : Sx_program_d I J F G) (hf : Sfm_d I ω n F)
    (he : M.IsFunctionSpace I E ω X) (hd : M.IsFunctionSpace J D ω X)
    (rel : Sx_graph_d I J R S) (hr : M.mem r n) : Sx_row_d I J X R S E D F G n r := by
  have hg := h.program_l I J hf
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hf.2.1.1
  obtain ⟨K, hK⟩ := seval_exists_l J hZF X S D G hg.2.1.1
  let ρ : Env M 8 := ⟨Fin.cases n (Fin.cases G (Fin.cases F (Fin.cases D
    (Fin.cases E (Fin.cases S (Fin.cases R (fun _ => X))))))), fun _ => X⟩
  let φ : UnarySchema 8 := { body := (sx_row_m (𝒞 := 𝒞) (𝒟 := 𝒟)
    (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have sat k : φ.denote ρ k ↔ Sx_row_d I J X R S E D F G n k := by
    simp only [φ, UnarySchema.denote, sx_row_sat_l I J hZF.1]; rfl
  apply (sat r).mp (sfm_induction_l I hZF hf φ ρ ?_ hr)
  intro r hr ih
  apply (sat r).mpr
  intro f g hfE hgD agree
  have ff := (he f).mp hfE
  have gg := (hd g).mp hgD
  obtain ⟨c, hc⟩ := (hf.2.1.2.2 r).mp hr
  obtain ⟨d, hdG⟩ := (hg.2.1.2.2 r).mp hr
  have node := h.row_l I J hf.2.1.2.1 hc hdG
  rcases hf.2.2 r c hc with ⟨i, j, op, hi, hj⟩ | ⟨i, j, op, hi, hj⟩ |
    ⟨i, j, op, hi, hj⟩ | ⟨i, j, op, hi, hj⟩
  · obtain ⟨x, _, hix⟩ := ff.2.2 i hi
    obtain ⟨y, _, hjy⟩ := ff.2.2 j hj
    exact (ssat_rel_l I hZF hf hH hc op he hfE hix hjy).trans ((rel x y).symm.trans
      (ssat_rel_l J hZF hg hK hdG (node.op_l I J op) hd hgD ((agree i x).mpr hix) ((agree j y).mpr hjy)).symm)
  · obtain ⟨x, _, hix⟩ := ff.2.2 i hi
    obtain ⟨y, _, hjy⟩ := ff.2.2 j hj
    exact (ssat_eq_l I hZF hf hH hc op he hfE hix hjy).trans
      (ssat_eq_l J hZF hg hK hdG (node.op_l I J op) hd hgD ((agree i x).mpr hix) ((agree j y).mpr hjy)).symm
  · rw [ssat_nor_l I hZF hf hH hc op hfE, ssat_nor_l J hZF hg hK hdG (node.op_l I J op) hgD]
    exact not_congr (or_congr ((sat i).mp (ih i hi) f g hfE hgD agree) ((sat j).mp (ih j hj) f g hfE hgD agree))
  · have tr x a b (hx : M.mem x X) (ha : Senv_update_d I f i x a) (hb : Senv_update_d J g i x b) :
        Ssat_d I X R E F n j a ↔ Ssat_d J X S D G n j b :=
      (sat j).mp (ih j hj) a b ((he a).mpr (ha.function_l I ff hi hx))
        ((hd b).mpr (hb.function_l J gg hi hx)) (agree.update_l I J ha hb)
    rw [ssat_exists_l I hZF hf hH hc op hfE, ssat_exists_l J hZF hg hK hdG (node.op_l I J op) hgD]
    constructor
    · rintro ⟨x, a, hx, ha, truth⟩
      obtain ⟨b, hb, _⟩ := senv_update_exists_l J hZF gg hi hx
      exact ⟨x, b, hx, hb, (tr x a b hx ha hb).mp truth⟩
    · rintro ⟨x, b, hx, hb, truth⟩
      obtain ⟨a, ha, _⟩ := senv_update_exists_l I hZF ff hi hx
      exact ⟨x, a, hx, ha, (tr x a b hx ha hb).mpr truth⟩

/-- 两种实际隶属结构和对应赋值读出相同的完整满足关系。 -/
theorem Sx_program_d.satisfies_l (hZF : M.Models ZF) {ω X R S c d a b F G n r f g}
    (h : Sx_program_d I J F G) (hc : Smem_d I c X R) (hd : Smem_d J d X S)
    (ha : Sformula_d I ω a n F r) (hb : J.Codes b G r)
    (hf : M.IsSetFunctionFromTo I f ω X) (hg : M.IsSetFunctionFromTo J g ω X)
    (agree : Sx_graph_d I J f g) : Satisfies_d I ω c a f ↔ Satisfies_d J ω d b g := by
  obtain ⟨E, he, _⟩ := senv_space_l I hZF ω hc.1.2.1
  obtain ⟨D, hD, _⟩ := senv_space_l J hZF ω hd.1.2.1
  have hb' : Sformula_d J ω b n G r := ⟨hb, h.program_l I J ha.2.1, ha.2.2⟩
  exact (satisfies_decode_l I hZF.1 hc.1 ha he).trans
    ((h.correct_l I J hZF ha.2.1 he hD (fun x y => (hd.2 x y).trans (hc.2 x y).symm) ha.2.2
      f g ((he f).mpr hf) ((hD g).mpr hg) agree).trans (satisfies_decode_l J hZF.1 hd.1 hb' hD).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 原程序到平坦程序的转换证书在极限秩层中绝对

输入坐标由 Kuratowski 码回收，输出坐标由平坦配对的秩界回收。
源只承担实际秩闭包，不承担背景的整个集合论。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {ω δ Z : M.Domain}
  (hω : M.IsOmega ω) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z) (hωZ : M.mem ω Z)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "T" => v_transitive_l I hV

include hω hV hωZ in
theorem Sx_node_d.rank_mem_l {c d} (h : Sx_node_d I K c d) (hc : M.mem c Z) : M.mem d Z := by
  obtain ⟨k, p, i, j, q, hc', hp, hq, hd⟩ := h
  have kp := hc'.mem_l M T hc
  have ij := hp.mem_l M T kp.2
  have hωδ := (v_ordinal_l I hV).transitive ω (ZF.v_ordinal_height_l hZF hV (hω.isOrdinal (ZF.modelsKP hZF)) hωZ)
  have hqZ := ((fp_fixed_l hZF.1 hω).mp hq).rank_mem_l I hZF hω hV hωδ ij.1 ij.2
  exact ((fp_fixed_l hZF.1 hω).mp hd).rank_mem_l I hZF hω hV hωδ kp.1 hqZ

variable (hδ : M.IsLimitOrdinal δ)
local notation "nz" => Nonempty.intro (Subtype.mk ω hωZ)
local notation "P" => sc_v_pair_l (ZF.modelsKP hZF) hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P
local notation "L" => fp_rank_interpretation_l I hZF hω hV hωZ

theorem rt_sx_node_l (c d : (N).Domain) : Sx_node_d J L c d ↔ Sx_node_d I K c.val d.val := by
  have code := rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P
  constructor
  · rintro ⟨k, p, i, j, q, hc, hp, hq, hd⟩
    exact ⟨k.val, p.val, i.val, j.val, q.val, (code ..).mp hc, (code ..).mp hp,
      (fp_fixed_l hZF.1 hω).mpr hq, (fp_fixed_l hZF.1 hω).mpr hd⟩
  · rintro ⟨k, p, i, j, q, hc, hp, hq, hd⟩
    have kp := hc.mem_l M T c.property
    have ij := hp.mem_l M T kp.2
    have kq := ((fp_fixed_l hZF.1 hω).mp hd).inverse_rank_l I hZF hω.1 hV d.property
    exact ⟨⟨k, kp.1⟩, ⟨p, kp.2⟩, ⟨i, ij.1⟩, ⟨j, ij.2⟩, ⟨q, kq.2⟩,
      (code ..).mpr hc, (code ..).mpr hp, (fp_fixed_l hZF.1 hω).mp hq, (fp_fixed_l hZF.1 hω).mp hd⟩

theorem rt_sx_program_l (F G : (N).Domain) :
    Sx_program_d J L F G ↔ Sx_program_d I K F.val G.val := by
  have ent := rt_entry_l T nz hZF.1
  have flat := rt_fp_entry_l I hZF hω hV hωZ
  refine and_congr (rt_fp_function_l I hZF hω hV hωZ G) ?_
  constructor
  · intro h r d
    constructor
    · intro hrd
      have rd := rt_fp_coordinates_l I hZF hω hV G.property hrd
      obtain ⟨c, hc, code⟩ := (h ⟨r, rd.1⟩ ⟨d, rd.2⟩).mp ((flat ..).mpr hrd)
      exact ⟨c.val, (ent ..).mp hc, (rt_sx_node_l hZF hω hV hωZ hδ ..).mp code⟩
    · rintro ⟨c, hc, code⟩
      have rc := rd_entry_transitive_l T F.property hc
      let r' : (N).Domain := ⟨r, rc.1⟩
      let c' : (N).Domain := ⟨c, rc.2⟩
      let d' : (N).Domain := ⟨d, code.rank_mem_l hZF hω hV hωZ rc.2⟩
      exact (flat ..).mp ((h r' d').mpr
        ⟨c', (ent ..).mpr hc, (rt_sx_node_l hZF hω hV hωZ hδ c' d').mpr code⟩)
  · intro h r d
    refine (flat r d G).trans ((h r.val d.val).trans ?_)
    constructor
    · rintro ⟨c, hc, code⟩
      let c' : (N).Domain := ⟨c, (rd_entry_transitive_l T F.property hc).2⟩
      exact ⟨c', (ent ..).mpr hc, (rt_sx_node_l hZF hω hV hωZ hδ c' d).mpr code⟩
    · rintro ⟨c, hc, code⟩
      exact ⟨c.val, (ent ..).mp hc, (rt_sx_node_l hZF hω hV hωZ hδ c d).mp code⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部变量列的递归打包规格

前缀从空集开始，每次把新坐标平坦配到旧前缀之后。
编译规格对实际秩层与全部赋值统一量化，原 ω 和输出位置由变量槽指定。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Fs_code_d.step_l (hE : Extensional M) {ω X f n l p x : M.Domain}
    (hω : M.IsInductive ω) (hn : M.mem n ω) (hs : M.SuccessorOf l n) (hx : M.PairMember I n x f) :
    Fs_code_d I ω X f l p ↔ ∃ q, Fs_code_d I ω X f n q ∧ I.Codes p q x := by
  obtain ⟨l', hl', hlω⟩ := hω.2 n hn
  have hl := hl'.eq hE hs ▸ hlω
  constructor
  · rintro ⟨H, trace, hp⟩
    obtain ⟨q, _, hq⟩ := trace.1.2.2 n hn
    exact ⟨q, ⟨H, trace, hq⟩, trace.2.2 n l q p x hs hq hp hx⟩
  · rintro ⟨q, ⟨H, trace, hq⟩, code⟩
    obtain ⟨p', _, hp'⟩ := trace.1.2.2 l hl
    exact ⟨H, trace, I.unique (trace.2.2 n l q p' x hs hq hp' hx) code ▸ hp'⟩

theorem Fs_trace_d.zero_code_l (hE : Extensional M) {ω X f H e p : M.Domain}
    (h : Fs_trace_d I ω X f H) (he : ∀ x, ¬ M.mem x e) :
    Fs_code_d I ω X f e p ↔ ∀ x, ¬ M.mem x p := by
  constructor
  · rintro ⟨G, trace, hp⟩
    exact trace.1.1.2 e e p (trace.2.1 e he) hp ▸ he
  · intro hp
    have eq := hE.eq_of_same_members e p (fun x => iff_of_false (he x) (hp x))
    exact ⟨H, h, eq ▸ h.2.1 e he⟩

namespace Internal
variable (Q : kpair_convention_l.Interpretation M) (K : FlatPairing.convention.Interpretation M)

def St_pack_d (ω w b k m G u : M.Domain) : Prop := ∀ μ Y c R E f g p,
  V_d Q μ Y → M.mem ω Y → Smem_d Q c Y R → M.IsFunctionSpace Q E ω Y → M.mem f E →
    M.IsSetFunctionFromTo K g ω Y → Sx_graph_d Q K f g → M.PairMember Q w ω f → M.PairMember Q b p f →
      (Ssat_d Q Y R E G m u f ↔ Fs_code_d K ω Y g k p)

def st_pack_m {d} (ω w b k m G u : Term d) : Formula 1 d := set[d] ⟪∀ μ Y c R E f g p,
  ⌜v_m kpair_convention_l⌝ₚ(μ, Y) → ⌜ω⌝ₛ ∈ Y → ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c, Y, R) →
  ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(E, ⌜ω⌝ₛ, Y) → f ∈ E →
  ⌜Formula.isFunctionFromTo FlatPairing.convention⌝ₚ(g, ⌜ω⌝ₛ, Y) →
  ⌜sx_graph_m (𝒞 := kpair_convention_l) (𝒟 := FlatPairing.convention)⌝ₚ(f, g) →
  ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜w⌝ₛ, ⌜ω⌝ₛ, f) →
  ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(⌜b⌝ₛ, p, f) →
    (⌜ssat_m (𝒞 := kpair_convention_l)⌝ₚ(Y, R, E, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, f) ↔
      ⌜fs_code_m (𝒞 := FlatPairing.convention)⌝ₚ(⌜ω⌝ₛ, Y, g, ⌜k⌝ₛ, p))⟫

@[simp] theorem st_pack_closed_l {d} (ω w b k m G u : Term d)
    (hω : ω.freeSupport = []) (hw : w.freeSupport = []) (hb : b.freeSupport = []) (hk : k.freeSupport = [])
    (hm : m.freeSupport = []) (hG : G.freeSupport = []) (hu : u.freeSupport = []) :
    (st_pack_m ω w b k m G u).FreeClosed := by
  simp -implicitDefEqProofs [st_pack_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed, hω, hw, hb, hk, hm, hG, hu]

theorem st_pack_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω w b k m G u : Term d) :
    Formula.satisfies ρ (st_pack_m ω w b k m G u) ↔
      St_pack_d Q K (ω.eval ρ) (w.eval ρ) (b.eval ρ) (k.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [st_pack_m, St_pack_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    v_sat_l Q hE, Formula.satisfies_mem_iff, smem_sat_l Q, Formula.satisfies_isFunctionSpace_iff Q hE,
    Formula.satisfies_isFunctionFromTo_iff K hE, sx_graph_sat_l Q K, Formula.satisfies_orderedPairMem_iff Q,
    Formula.satisfies_iff_iff, ssat_sat_l Q hE, fs_code_sat_l K hE, Definitional.Term.eval_weaken]; rfl

end Internal
end YesMetaZFC.SetTheory

/-! ## 内部打包程序的后继步

输出槽 b 保持固定。先把输出复制到新槽 c，再绑定 b 为旧前缀，
检验平坦配对；最后绑定 c。两次更新均保持原变量及 ω 参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem st_pack_step_l {ω w b k l m G u : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hk : M.mem k b) (hl : M.SuccessorOf l k)
    (hG : Sfm_d Q ω m G) (hu : M.mem u m) (pack : St_pack_d Q K ω w b k m G u) :
    ∃ m' G' u', Sfm_d Q ω m' G' ∧ M.mem u' m' ∧ St_pack_d Q K ω w b l m' G' u' := by
  have hwω := hω.transitive (ZF.modelsKP hZF) b hb w hw
  have hkω := hω.transitive (ZF.modelsKP hZF) b hb k hk
  obtain ⟨c, hc, hcω⟩ := hω.1.2 b hb
  obtain ⟨d, hd, hdω⟩ := hω.1.2 c hcω
  have below {i} (hi : M.mem i b) : M.mem i d := (hd i).mpr (Or.inl ((hc i).mpr (Or.inl hi)))
  let φ : Formula 1 4 := fp_pair0_m (.bound 3) (.bound 2) (.bound 1) .newest
  obtain ⟨m₁, G₁, v, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ (fp_pair0_m_freeClosed _ _ _ _ rfl rfl rfl rfl))
    (Fin.cases c (Fin.cases k (Fin.cases b (fun _ => w)))) hdω
    (Fin.cases hd.predecessor_mem (Fin.cases (below hk)
      (Fin.cases ((hd b).mpr (Or.inl hc.predecessor_mem)) (fun _ => below hw)))) hG
  obtain ⟨m₂, G₂, r₂, a₂, both₂⟩ := sfm_and_l Q hZF hω add.program (add.span u hu) add.root
  obtain ⟨m₃, G₃, r₃, a₃, ex₃⟩ := sfm_ex_l Q hZF hω a₂.program hb a₂.root
  obtain ⟨m₄, G₄, a₄, eq₄⟩ := sfm_eq_l Q hZF hω a₃.program hcω hb
  obtain ⟨m₅, G₅, r₅, a₅, both₅⟩ := sfm_and_l Q hZF hω a₄.program a₄.root (a₄.span r₃ a₃.root)
  obtain ⟨m₆, G₆, r₆, a₆, ex₆⟩ := sfm_ex_l Q hZF hω a₅.program hcω a₅.root
  refine ⟨m₆, G₆, r₆, a₆.program, a₆.root, fun μ Y a R E f g p hV hωY model hE hf hg fg hfw hfb => ?_⟩
  have fn := (hE f).mp hf
  have trans := v_transitive_l Q hV
  have hωμ := (v_ordinal_l Q hV).transitive ω (ZF.v_ordinal_height_l hZF hV (hω.isOrdinal (ZF.modelsKP hZF)) hωY)
  obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hV hωμ hg
  obtain ⟨x, hxY, hfx⟩ := fn.2.2 k hkω
  have gx := (fg k x).mpr hfx
  have body z (hz : M.mem z Y) f₁ (copy : Senv_update_d Q f c z f₁) :
      Ssat_d Q Y R E G₅ m₅ r₅ f₁ ↔ z = p ∧ Fs_code_d K ω Y g l z := by
    have fn₁ := copy.function_l Q fn hcω hz
    have hf₁ := (hE f₁).mpr fn₁
    have old₁ := copy.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) c)
    have fc := (copy.2 c z).mpr (Or.inl ⟨rfl, rfl⟩)
    have fb := (old₁ b p hc.predecessor_mem).mp hfb
    have inner q (hq : M.mem q Y) f₂ (update : Senv_update_d Q f₁ b q f₂) :
        Ssat_d Q Y R E G₂ m₂ r₂ f₂ ↔ Fs_code_d K ω Y g k q ∧ (K).Codes z q x := by
      have fn₂ := update.function_l Q fn₁ hb hq
      have hf₂ := (hE f₂).mpr fn₂
      have old₂ := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
      have old i y (hi : M.mem i b) : M.PairMember Q i y f ↔ M.PairMember Q i y f₂ :=
        (old₁ i y ((hc i).mpr (Or.inl hi))).trans (old₂ i y hi)
      have fw := (old w ω hw).mp hfw
      have fk := (old k x hk).mp hfx
      have fq := (update.2 b q).mpr (Or.inl ⟨rfl, rfl⟩)
      have cb : c ≠ b := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) b (eq ▸ hc.predecessor_mem)
      have fz := (update.2 c z).mpr (Or.inr ⟨cb, fc⟩)
      obtain ⟨g₂, hg₂, fg₂⟩ := fn_recode_l Q K hZF fn₂
      obtain ⟨H₂, trace₂, _⟩ := fp_trace_rank_l Q hZF hω hV hωμ hg₂
      have same : Senv_agree_d K k g₂ g := fun i y hi => (fg₂ i y).trans
        ((old i y ((hω.members_areOrdinals (ZF.modelsKP hZF) b hb).transitive k hk i hi)).symm.trans (fg i y).symm)
      have code_eq : Fs_code_d K ω Y g₂ k q ↔ Fs_code_d K ω Y g k q :=
        ⟨fun h => h.transport_l K hZF hω hg₂ hg trace same,
          fun h => h.transport_l K hZF hω hg hg₂ trace₂ (same.symm_l K)⟩
      have prev := (add.sat_l Q hZF hG hu Y R E f₂).symm.trans
        ((pack μ Y a R E f₂ g₂ q hV hωY model hE hf₂ hg₂ fg₂ fw fq).trans code_eq)
      let η : Env (smdl_structure_l Q (R := R) model.1.2.1) 4 :=
        ⟨Fin.cases ⟨z, hz⟩ (Fin.cases ⟨x, hxY⟩ (Fin.cases ⟨q, hq⟩ (fun _ => ⟨ω, hωY⟩))), fun _ => ⟨q, hq⟩⟩
      have atom : Ssat_d Q Y R E G₁ m₁ v f₂ ↔ (K).Codes z q x :=
        (compile Y R model.1.2.1 E hE f₂ hf₂ η (Fin.cases fz (Fin.cases fk (Fin.cases fq (fun _ => fw))))).trans
          ((source_core_sat_l φ η).trans ((smem_delta_image_l Q model trans (fp_pair0_delta_l ..) η).trans
            ((fp_pair0_sat_l (ZF.modelsKP hZF) (image_env_l
              (M := smdl_structure_l Q (R := R) model.1.2.1) (N := M) Subtype.val η)
              (.bound 3) (.bound 2) (.bound 1) .newest hω.1).trans
              (fp_fixed_l hZF.1 hω).symm)))
      exact (both₂ Y R E f₂ hf₂).trans (and_congr prev atom)
    have step : Ssat_d Q Y R E G₃ m₃ r₃ f₁ ↔ Fs_code_d K ω Y g l z := by
      refine (ex₃ Y R E f₁ hf₁).trans ⟨?_, ?_⟩
      · rintro ⟨q, f₂, hq, update, truth⟩
        obtain ⟨code, pair⟩ := (inner q hq f₂ update).mp truth
        exact (Fs_code_d.step_l K hZF.1 hω.1 hkω hl gx).mpr ⟨q, code, pair⟩
      · intro truth
        obtain ⟨q, code, pair⟩ := (Fs_code_d.step_l K hZF.1 hω.1 hkω hl gx).mp truth
        obtain ⟨f₂, update, _⟩ := senv_update_exists_l Q hZF fn₁ hb (code.bound_l K).2
        exact ⟨q, f₂, (code.bound_l K).2, update, (inner q (code.bound_l K).2 f₂ update).mpr ⟨code, pair⟩⟩
    exact (both₅ Y R E f₁ hf₁).trans (and_congr (eq₄ Y R E f₁ z p hE hf₁ fc fb)
      ((a₄.sat_l Q hZF a₃.program a₃.root Y R E f₁).symm.trans step))
  refine (ex₆ Y R E f hf).trans ⟨?_, ?_⟩
  · rintro ⟨z, f₁, hz, copy, truth⟩
    obtain ⟨eq, code⟩ := (body z hz f₁ copy).mp truth
    exact eq ▸ code
  · intro truth
    have hp := fn.output_mem_of_pairMember hfb
    obtain ⟨f₁, copy, _⟩ := senv_update_exists_l Q hZF fn hcω hp
    exact ⟨p, f₁, hp, copy, (body p hp f₁ copy).mpr ⟨rfl, truth⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 任意内部有限元组的实际打包编译

以可分离的原公式规格作内部 ω 归纳。零步识别空集，后继步追加平坦配对；
输出槽在全部归纳步骤中固定，所得程序同时适用于所有实际秩层及赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem st_pack_zero_l {ω w b e : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (he : ∀ x, ¬ M.mem x e) :
    ∃ m G u, Sfm_d Q ω m G ∧ M.mem u m ∧ St_pack_d Q K ω w b e m G u := by
  have heω := num_mem_l hZF.1 hω (show Num_d 0 e from he)
  have empty : Sfm_d Q ω e e := ⟨heω, Structure.IsSequenceOfLength.empty Q he,
    fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
  obtain ⟨c, hc, hcω⟩ := hω.1.2 b hb
  let φ : Formula 1 1 := Formula.forallMem .newest .falsum
  have closed : φ.FreeClosed := by simp [φ, Formula.forallMem, Definitional.Formula.FreeClosed]
  have delta : φ.IsDelta0 := .forallMem _ .falsum
  obtain ⟨m, G, u, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ closed) (fun _ => b) hcω (fun _ => hc.predecessor_mem) empty
  refine ⟨m, G, u, add.program, add.root, fun μ Y a R E f g p hV hωY model hE hf hg _ _ hfb => ?_⟩
  have trans := v_transitive_l Q hV
  have hωμ := ZF.v_ordinal_height_l hZF hV (hω.isOrdinal (ZF.modelsKP hZF)) hωY
  obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hV ((v_ordinal_l Q hV).transitive ω hωμ) hg
  have hp := ((hE f).mp hf).output_mem_of_pairMember hfb
  let η : Env (smdl_structure_l Q (R := R) model.1.2.1) 1 := ⟨fun _ => ⟨p, hp⟩, fun _ => ⟨p, hp⟩⟩
  have atom : Formula.satisfies (image_env_l (M := smdl_structure_l Q (R := R) model.1.2.1)
      (N := M) Subtype.val η) φ ↔ ∀ x, ¬ M.mem x p := by
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff]
    rfl
  exact ((compile Y R model.1.2.1 E hE f hf η (fun _ => hfb)).trans
    ((source_core_sat_l φ η).trans ((smem_delta_image_l Q model trans delta η).trans atom))).trans
      (trace.zero_code_l K hZF.1 he).symm

/-- 自动构造一个内部程序，读取前 n 个变量并在固定槽 b 检验其平坦前缀码。 -/
theorem st_pack_build_l {ω w b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hn : M.mem n ω) (hnb : M.MemberSubset n b) :
    ∃ m G u, Sfm_d Q ω m G ∧ M.mem u m ∧ St_pack_d Q K ω w b n m G u := by
  let ρ : Env M 4 := ⟨Fin.cases n (Fin.cases b (Fin.cases w (fun _ => ω))), fun _ => ω⟩
  let φ : UnarySchema 4 := {
    body := .imp (Formula.subset .newest (.bound 1))
      (.existsE (.existsE (.existsE (.conj (sfm_m (𝒞 := kpair_convention_l) (.bound 7) (.bound 2) (.bound 1))
        (.conj (.mem .newest (.bound 2)) (st_pack_m (.bound 7) (.bound 6) (.bound 5) (.bound 3)
          (.bound 2) (.bound 1) .newest)))))) }
  have sat k : φ.denote ρ k ↔ (M.MemberSubset k n →
      ∃ m G u, Sfm_d Q ω m G ∧ M.mem u m ∧ St_pack_d Q K ω w b k m G u) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, sfm_sat_l Q hZF.1,
      Formula.satisfies_mem_iff, st_pack_sat_l Q K hZF.1]; rfl
  have built : φ.denote ρ n := by
    apply hω.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ n hn
    · intro e he
      exact (sat e).mpr (fun _ => st_pack_zero_l hZF hω hb he)
    · intro k _ ih l hl
      refine (sat l).mpr fun hln => ?_
      obtain ⟨m, G, u, hG, hu, pack⟩ := (sat k).mp ih (fun i hi => hln i ((hl i).mpr (Or.inl hi)))
      exact st_pack_step_l hZF hω hb hw (hnb k (hln k hl.predecessor_mem)) hl hG hu pack
  exact (sat n).mp built (fun _ h => h)

end YesMetaZFC.SetTheory.Internal

/-! ## 在任意秩层中绑定原变量列的平坦前缀

绑定的是有限前缀码，其秩不高于原变量。随后任意固定原公式可读取它，
无需预设最大序数，也不把可能高一层的元组图作为当前模型的元素。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem st_pack_bind_l {ω w b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hn : M.mem n ω) (hnb : M.MemberSubset n b)
    {k : Nat} (φ : Formula 1 (k+1)) (hc : φ.FreeClosed) (σ : Fin k → M.Domain) (hσ : ∀ i, M.mem (σ i) b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ η Y c R f g (hm : Smem_d Q c Y R)
      (ρ : Env (smdl_structure_l Q (R := R) hm.1.2.1) k),
      V_d Q η Y → M.mem ω Y → M.IsSetFunctionFromTo Q f ω Y → M.IsSetFunctionFromTo K g ω Y →
      Sx_graph_d Q K f g → M.PairMember Q w ω f → (∀ i, M.PairMember Q (σ i) (ρ.bound i).val f) →
        (Satisfies_d Q ω c a f ↔ ∃ p : (smdl_structure_l Q (R := R) hm.1.2.1).Domain,
          Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) φ) := by
  obtain ⟨m₀, G₀, u₀, prog, root, pack⟩ := st_pack_build_l hZF hω hb hw hn hnb
  obtain ⟨j, hj, hjω⟩ := hω.1.2 b hb
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ hc) (Fin.cases b σ) hjω
    (Fin.cases hj.predecessor_mem (fun i => (hj (σ i)).mpr (Or.inl (hσ i)))) prog
  obtain ⟨m₂, G₂, u₂, bothProg, both⟩ := sfm_and_l Q hZF hω add.program (add.span u₀ root) add.root
  obtain ⟨m, G, u, finalProg, ex⟩ := sfm_ex_l Q hZF hω bothProg.program hb bothProg.root
  obtain ⟨a, ha⟩ := (Q).total G u
  have form : Sformula_d Q ω a m G u := ⟨ha, finalProg.program, finalProg.root⟩
  refine ⟨a, m, G, u, form, fun η Y c R f g model ρ hY hωY ff fg agree fw values => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF Q ω Y
  have hf := (hE f).mpr ff
  have hωη := (v_ordinal_l Q hY).transitive ω (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal (ZF.modelsKP hZF)) hωY)
  obtain ⟨H, trace, _⟩ := fp_trace_rank_l Q hZF hω hY hωη fg
  have body (p : (smdl_structure_l Q (R := R) model.1.2.1).Domain) f₁ (update : Senv_update_d Q f b p.val f₁) :
      Ssat_d Q Y R E G₂ m₂ u₂ f₁ ↔ Fs_code_d K ω Y g n p.val ∧ Formula.satisfies (ρ.push p) φ := by
    have fn₁ := update.function_l Q ff hb p.property
    have hf₁ := (hE f₁).mpr fn₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    have fp := (update.2 b p.val).mpr (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨g₁, hg₁, same₁⟩ := fn_recode_l Q K hZF fn₁
    obtain ⟨H₁, trace₁, _⟩ := fp_trace_rank_l Q hZF hω hY hωη hg₁
    have same : Senv_agree_d K n g₁ g := fun i x hi =>
      (same₁ i x).trans ((old i x (hnb i hi)).symm.trans (agree i x).symm)
    have codes : Fs_code_d K ω Y g₁ n p.val ↔ Fs_code_d K ω Y g n p.val :=
      ⟨fun h => h.transport_l K hZF hω hg₁ fg trace same,
        fun h => h.transport_l K hZF hω fg hg₁ trace₁ (fun i x hi => (same i x hi).symm)⟩
    have packed := (add.sat_l Q hZF prog root Y R E f₁).symm.trans
      ((pack η Y c R E f₁ g₁ p.val hY hωY model hE hf₁ hg₁ same₁ ((old w ω hw).mp fw) fp).trans codes)
    have atom := (compile Y R model.1.2.1 E hE f₁ hf₁ (ρ.push p)
      (Fin.cases fp (fun i => (old (σ i) (ρ.bound i).val (hσ i)).mp (values i)))).trans (source_core_sat_l φ (ρ.push p))
    exact (both Y R E f₁ hf₁).trans (and_congr packed atom)
  refine (satisfies_decode_l Q hZF.1 model.1 form hE).trans ((ex Y R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨p, f₁, hp, update, truth⟩
    exact ⟨⟨p, hp⟩, (body ⟨p, hp⟩ f₁ update).mp truth⟩
  · rintro ⟨p, truth⟩
    obtain ⟨f₁, update, _⟩ := senv_update_exists_l Q hZF ff hb p.property
    exact ⟨p.val, f₁, p.property, update, (body p f₁ update).mpr truth⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 从平坦前缀恢复原变量列的图

固定公式在后继秩层中自行找到前一层，量化完整平坦赋值及其前缀轨道，
再取前 n 项的图。所有见证的所属秩均由实际函数图自动给出。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

def st_unpack_s : UnarySchema 3 := { body := .existsE (.existsE
  (.conj (sv_last_m (.bound 1)) (.conj
    (Formula.isFunctionFromTo FlatPairing.convention .newest (.bound 5) (.bound 1)) (.conj
    (Formula.isFunctionFromTo FlatPairing.convention (.bound 3) (.bound 4) (.bound 1)) (.conj
    (fs_code_m (𝒞 := FlatPairing.convention) (.bound 5) (.bound 1) .newest (.bound 4) (.bound 2))
    (Formula.isRestriction FlatPairing.convention (.bound 3) .newest (.bound 4))))))) }

variable {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
  (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) ν X)
  (hW : V_d (kp_pair_l (ZF.modelsKP hZF)) μ Y) (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l Q hZF hω hW hωY

include hω hV hW hs in
theorem st_unpack_source_l (n h p : (N).Domain) :
    Formula.satisfies (⟨Fin.cases p (Fin.cases h (Fin.cases n (fun _ => ⟨ω, hωY⟩))),
      fun _ => h⟩ : Env N 4) st_unpack_s.body ↔
    M.IsSetFunctionFromTo K h.val n.val X ∧ ∃ g, M.IsSetFunctionFromTo K g ω X ∧
      Fs_code_d K ω X g n.val p.val ∧ M.IsRestrictionOf K h.val g n.val := by
  let ρ : Env N 4 := ⟨Fin.cases p (Fin.cases h (Fin.cases n (fun _ => ⟨ω, hωY⟩))), fun _ => h⟩
  have hων : M.MemberSubset ω ν := by
    have hωμ := ZF.v_ordinal_height_l hZF hW (hω.isOrdinal (ZF.modelsKP hZF)) hωY
    rcases (hs ω).mp hωμ with h | h
    · exact (v_ordinal_l Q hV).transitive ω h
    · exact fun i hi => (h i).mp hi
  have last (A g : (N).Domain) := sv_last_rank_l Q hZF hω hV hW hs hωY ((ρ.push A).push g) (.bound 1)
  have fn := rt_fp_function_from_l Q hZF hω hW hωY
  have code := rt_fs_code_l Q hZF hω hW hωY
  have cut := rt_fp_restriction_l Q hZF hω hW hωY
  have read : Formula.satisfies ρ st_unpack_s.body ↔ ∃ A g : (N).Domain,
      A.val = X ∧ (N).IsSetFunctionFromTo J g ⟨ω, hωY⟩ A ∧ (N).IsSetFunctionFromTo J h n A ∧
        Fs_code_d J ⟨ω, hωY⟩ A g n p ∧ (N).IsRestrictionOf J h g n := by
    simp only [st_unpack_s, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, last,
      Formula.satisfies_isFunctionFromTo_iff J (rt_model_ext_l hZF.1 (v_transitive_l Q hW) _),
      fs_code_sat_l J (rt_model_ext_l hZF.1 (v_transitive_l Q hW) _),
      Formula.satisfies_isRestriction_iff J]
    rfl
  refine read.trans ⟨?_, ?_⟩
  · rintro ⟨A, g, eq, hg, hh, cp, restrict⟩
    exact ⟨eq ▸ (fn h n A).mp hh, g.val, eq ▸ (fn g ⟨ω, hωY⟩ A).mp hg,
      eq ▸ (code A g n p (eq.symm ▸ hV) hων).mp cp, (cut h g n).mp restrict⟩
  · rintro ⟨hh, g, hg, cp, restrict⟩
    let A : (N).Domain := ⟨X, (ZF.v_successor_l Q hZF hV hW hs X).mpr (fun _ h => h)⟩
    let g' : (N).Domain := ⟨g, (ZF.v_successor_l Q hZF hV hW hs g).mpr
      (fp_function_rank_l Q hZF hω hV hων (fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i hi)) hg)⟩
    exact ⟨A, g', rfl, (fn g' ⟨ω, hωY⟩ A).mpr hg, (fn h n A).mpr hh,
      (code A g' n p hV hων).mpr cp, (cut h g' n).mpr restrict⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原变量列到平坦元组图的自动公式编译

实际编译打包与反解公式，再绑定前缀见证。所得原公式直接核验候选图：
定义域为内部 n，值域在前一秩层，并且每项等于相应原变量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem st_tuple_build_l {ω w v b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hv : M.mem v b) (hn : M.mem n ω) (hnb : M.MemberSubset n b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ ν μ X Y c R f t,
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → M.mem ω Y → Smem_d Q c Y R →
      M.IsSetFunctionFromTo Q f ω Y → M.PairMember Q w ω f → M.PairMember Q v n f → M.PairMember Q b t f →
      (Satisfies_d Q ω c a f ↔ M.IsSetFunctionFromTo K t n X ∧
        ∀ i x, M.mem i n → (M.PairMember K i x t ↔ M.PairMember Q i x f)) := by
  obtain ⟨p, hp, hpω⟩ := hω.1.2 b hb
  obtain ⟨d, hd, hdω⟩ := hω.1.2 p hpω
  have below {i} (hi : M.mem i b) : M.mem i d := (hd i).mpr (Or.inl ((hp i).mpr (Or.inl hi)))
  obtain ⟨m₀, G₀, u₀, hG₀, hu₀, pack⟩ := st_pack_build_l hZF hω hpω ((hp w).mpr (Or.inl hw)) hn
    (fun i hi => (hp i).mpr (Or.inl (hnb i hi)))
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l st_unpack_s.body)
    (source_core_closed_l _ st_unpack_s.freeClosed) (Fin.cases p (Fin.cases b (Fin.cases v (fun _ => w)))) hdω
    (Fin.cases hd.predecessor_mem (Fin.cases ((hd b).mpr (Or.inl hp.predecessor_mem))
      (Fin.cases (below hv) (fun _ => below hw)))) hG₀
  obtain ⟨m₂, G₂, u₂, a₂, both⟩ := sfm_and_l Q hZF hω add.program (add.span u₀ hu₀) add.root
  obtain ⟨m, G, u, a₃, ex⟩ := sfm_ex_l Q hZF hω a₂.program hpω a₂.root
  obtain ⟨a, ha⟩ := (Q).total G u
  have form : Sformula_d Q ω a m G u := ⟨ha, a₃.program, a₃.root⟩
  refine ⟨a, m, G, u, form, fun ν μ X Y c R f t hV hW hs hωY model fn fw fv fb => ?_⟩
  have trans := v_transitive_l Q hW
  have hXY := (ZF.v_successor_l Q hZF hV hW hs X).mpr (fun _ h => h)
  have sub : M.MemberSubset X Y := trans X hXY
  have hων : M.MemberSubset ω ν := by
    rcases (hs ω).mp (ZF.v_ordinal_height_l hZF hW (hω.isOrdinal (ZF.modelsKP hZF)) hωY) with lt | eq
    · exact (v_ordinal_l Q hV).transitive ω lt
    · exact fun i hi => (eq i).mp hi
  have hωμ := (v_ordinal_l Q hW).transitive ω (ZF.v_ordinal_height_l hZF hW (hω.isOrdinal (ZF.modelsKP hZF)) hωY)
  have widen {g} (h : M.IsSetFunctionFromTo K g ω X) : M.IsSetFunctionFromTo K g ω Y :=
    ⟨h.1, h.2.1, fun i hi => (h.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩
  have lift {g q} (h : Fs_code_d K ω X g n q) : Fs_code_d K ω Y g n q := by
    obtain ⟨H, hH, entry⟩ := h
    exact ⟨H, ⟨widen hH.1, hH.2⟩, entry⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF Q ω Y
  have hf := (hE f).mpr fn
  have read q (hq : M.mem q Y) f₁ (update : Senv_update_d Q f p q f₁) g₁
      (hg₁ : M.IsSetFunctionFromTo K g₁ ω Y) (fg₁ : Sx_graph_d Q K f₁ g₁) :
      Ssat_d Q Y R E G₂ m₂ u₂ f₁ ↔ Fs_code_d K ω Y g₁ n q ∧ M.IsSetFunctionFromTo K t n X ∧
        ∃ g, M.IsSetFunctionFromTo K g ω X ∧ Fs_code_d K ω X g n q ∧ M.IsRestrictionOf K t g n := by
    have fn₁ := update.function_l Q fn hpω hq
    have hf₁ := (hE f₁).mpr fn₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    have fq := (update.2 p q).mpr (Or.inl ⟨rfl, rfl⟩)
    have fw₁ := (old w ω ((hp w).mpr (Or.inl hw))).mp fw
    have fv₁ := (old v n ((hp v).mpr (Or.inl hv))).mp fv
    have fb₁ := (old b t hp.predecessor_mem).mp fb
    let η : Env (smdl_structure_l Q (R := R) model.1.2.1) 4 :=
      ⟨Fin.cases ⟨q, hq⟩ (Fin.cases ⟨t, fn.output_mem_of_pairMember fb⟩
        (Fin.cases ⟨n, fn.output_mem_of_pairMember fv⟩ (fun _ => ⟨ω, hωY⟩))),
        fun _ => ⟨t, fn.output_mem_of_pairMember fb⟩⟩
    have atom := (compile Y R model.1.2.1 E hE f₁ hf₁ η (Fin.cases fq (Fin.cases fb₁ (Fin.cases fv₁ (fun _ => fw₁))))).trans
      ((source_core_sat_l st_unpack_s.body η).trans ((smem_formula_l Q model _ st_unpack_s.body
        (⟨η.bound, η.free⟩ : Env (rt_model_l Y ⟨⟨ω, hωY⟩⟩) 4)).symm.trans
          (st_unpack_source_l hZF hω hV hW hs hωY ⟨n, fn.output_mem_of_pairMember fv⟩
            ⟨t, fn.output_mem_of_pairMember fb⟩ ⟨q, hq⟩)))
    exact (both Y R E f₁ hf₁).trans (and_congr ((add.sat_l Q hZF hG₀ hu₀ Y R E f₁).symm.trans
      (pack μ Y c R E f₁ g₁ q hW hωY model hE hf₁ hg₁ fg₁ fw₁ fq)) atom)
  refine (satisfies_decode_l Q hZF.1 model.1 form hE).trans ((ex Y R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨q, f₁, hq, update, truth⟩
    obtain ⟨g₁, hg₁, fg₁⟩ := fn_recode_l Q K hZF (update.function_l Q fn hpω hq)
    obtain ⟨cp, ht, g, hg, cg, cut⟩ := (read q hq f₁ update g₁ hg₁ fg₁).mp truth
    have same := (cp.prefix_l K hZF hω hg₁ (widen hg) (lift cg)).mp rfl
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    exact ⟨ht, fun i x hi => (cut.2 i x).trans ((and_iff_right hi).trans
      ((same i x hi).symm.trans ((fg₁ i x).trans (old i x ((hp i).mpr (Or.inl (hnb i hi)))).symm)))⟩
  · rintro ⟨ht, same⟩
    obtain ⟨e, he, heω⟩ := hω.1.1
    have heX := ZF.v_ordinal_mem_l Q hZF hV (hων e heω)
    obtain ⟨g, fill, hg⟩ := senv_fill_exists_l K hZF (ω := ω) ht heX
    have cut : M.IsRestrictionOf K t g n := ⟨ht.1.1, fun i x => ⟨fun hx => by
      have hi := ht.input_mem_of_pairMember hx
      exact ⟨hi, (fill.2 i x).mpr ⟨hω.transitive (ZF.modelsKP hZF) n hn i hi, Or.inl ⟨hi, hx⟩⟩⟩,
      fun ⟨hi, hx⟩ => ((fill.2 i x).mp hx).2.elim And.right (fun h => (h.1 hi).elim)⟩⟩
    obtain ⟨q, hqX, cg⟩ := fp_finite_rank_l Q hZF hω hV hων hg hn
    have hq := sub q hqX
    obtain ⟨f₁, update, fn₁⟩ := senv_update_exists_l Q hZF fn hpω hq
    obtain ⟨g₁, hg₁, fg₁⟩ := fn_recode_l Q K hZF fn₁
    obtain ⟨H₁, trace, _⟩ := fp_trace_rank_l Q hZF hω hW hωμ hg₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    have agree : Senv_agree_d K n g g₁ := fun i x hi =>
      ((cut.2 i x).trans (and_iff_right hi)).symm.trans ((same i x hi).trans
        ((old i x ((hp i).mpr (Or.inl (hnb i hi)))).trans (fg₁ i x).symm))
    exact ⟨q, f₁, hq, update, (read q hq f₁ update g₁ hg₁ fg₁).mpr
      ⟨(lift cg).transport_l K hZF hω (widen hg) hg₁ trace agree, ht, g, hg, cg, cut⟩⟩

/-- 任意固定原公式都可在内部元组上求值；编译结果只绑定实际元组图。 -/
theorem st_tuple_bind_l {ω w v b n : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hw : M.mem w b) (hv : M.mem v b) (hn : M.mem n ω) (hnb : M.MemberSubset n b)
    {k : Nat} (φ : Formula 1 (k+1)) (hφ : φ.FreeClosed) (σ : Fin k → M.Domain) (hσ : ∀ i, M.mem (σ i) b) :
    ∃ a m G u, Sformula_d Q ω a m G u ∧ ∀ ν μ X Y c R f (hm : Smem_d Q c Y R)
      (ρ : Env (smdl_structure_l Q (R := R) hm.1.2.1) k),
      V_d Q ν X → V_d Q μ Y → M.SuccessorOf μ ν → M.mem ω Y → M.IsSetFunctionFromTo Q f ω Y →
      M.PairMember Q w ω f → M.PairMember Q v n f → (∀ i, M.PairMember Q (σ i) (ρ.bound i).val f) →
        (Satisfies_d Q ω c a f ↔ ∃ h : (smdl_structure_l Q (R := R) hm.1.2.1).Domain,
          M.IsSetFunctionFromTo K h.val n X ∧
            (∀ i x, M.mem i n → (M.PairMember K i x h.val ↔ M.PairMember Q i x f)) ∧ Formula.satisfies (ρ.push h) φ) := by
  obtain ⟨a₀, m₀, G₀, u₀, form₀, tuple⟩ := st_tuple_build_l hZF hω hb hw hv hn hnb
  obtain ⟨j, hj, hjω⟩ := hω.1.2 b hb
  obtain ⟨m₁, G₁, u₁, add, compile⟩ := source_compile_core_l Q hZF hω (source_core_l φ)
    (source_core_closed_l φ hφ) (Fin.cases b σ) hjω
    (Fin.cases hj.predecessor_mem (fun i => (hj (σ i)).mpr (Or.inl (hσ i)))) form₀.2.1
  obtain ⟨m₂, G₂, u₂, a₂, both⟩ := sfm_and_l Q hZF hω add.program (add.span u₀ form₀.2.2) add.root
  obtain ⟨m, G, u, a₃, ex⟩ := sfm_ex_l Q hZF hω a₂.program hb a₂.root
  obtain ⟨a, ha⟩ := (Q).total G u
  have form : Sformula_d Q ω a m G u := ⟨ha, a₃.program, a₃.root⟩
  refine ⟨a, m, G, u, form, fun ν μ X Y c R f hm ρ hV hW hs hωY fn fw fv values => ?_⟩
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF Q ω Y
  have hf := (hE f).mpr fn
  have body (h : (smdl_structure_l Q (R := R) hm.1.2.1).Domain) f₁ (update : Senv_update_d Q f b h.val f₁) :
      Ssat_d Q Y R E G₂ m₂ u₂ f₁ ↔ M.IsSetFunctionFromTo K h.val n X ∧
        (∀ i x, M.mem i n → (M.PairMember K i x h.val ↔ M.PairMember Q i x f)) ∧ Formula.satisfies (ρ.push h) φ := by
    have fn₁ := update.function_l Q fn hb h.property
    have hf₁ := (hE f₁).mpr fn₁
    have old := update.agree_l Q (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    have fh := (update.2 b h.val).mpr (Or.inl ⟨rfl, rfl⟩)
    have tuples := (add.sat_l Q hZF form₀.2.1 form₀.2.2 Y R E f₁).symm.trans
      ((satisfies_decode_l Q hZF.1 hm.1 form₀ hE).symm.trans
        (tuple ν μ X Y c R f₁ h.val hV hW hs hωY hm fn₁ ((old w ω hw).mp fw) ((old v n hv).mp fv) fh))
    have atom := (compile Y R hm.1.2.1 E hE f₁ hf₁ (ρ.push h)
      (Fin.cases fh (fun i => (old (σ i) (ρ.bound i).val (hσ i)).mp (values i)))).trans (source_core_sat_l φ (ρ.push h))
    refine (both Y R E f₁ hf₁).trans ((and_congr tuples atom).trans ⟨?_, ?_⟩)
    · rintro ⟨⟨fn, same⟩, truth⟩
      exact ⟨fn, fun i x hi => (same i x hi).trans (old i x (hnb i hi)).symm, truth⟩
    · rintro ⟨fn, same, truth⟩
      exact ⟨⟨fn, fun i x hi => (same i x hi).trans (old i x (hnb i hi))⟩, truth⟩
  refine (satisfies_decode_l Q hZF.1 hm.1 form hE).trans ((ex Y R E f hf).trans ⟨?_, ?_⟩)
  · rintro ⟨h, f₁, hh, update, truth⟩
    exact ⟨⟨h, hh⟩, (body ⟨h, hh⟩ f₁ update).mp truth⟩
  · rintro ⟨h, truth⟩
    obtain ⟨f₁, update, _⟩ := senv_update_exists_l Q hZF fn hb h.property
    exact ⟨h.val, f₁, h.property, update, (body h f₁ update).mpr truth⟩

end YesMetaZFC.SetTheory.Internal

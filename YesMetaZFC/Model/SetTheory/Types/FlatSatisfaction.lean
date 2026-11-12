import YesMetaZFC.SetTheory.FlatPairing.Finite
import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.SetTheory.FlatPairing.RankObjects
import YesMetaZFC.SetTheory.FlatPairing.Functions
import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.SetTheory.FlatPairing.AssignmentSource

/-! # 以有限前缀为坐标的平坦真值表

表直接记录 (程序行, 前缀编码)，不再把赋值集合逐行嵌入函数图。
四条语义方程只量化单份赋值和编码轨道，均可放进一个后继秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ft_arg_d (k : Nat) (ω X R b T f p i j : M.Domain) : Prop := match k with
  | 0 => ∃ x y, M.PairMember I i x f ∧ M.PairMember I j y f ∧ M.PairMember I x y R
  | 1 => ∃ x, M.PairMember I i x f ∧ M.PairMember I j x f
  | 2 => ¬ (M.PairMember I i p T ∨ M.PairMember I j p T)
  | _ => ∃ x g q, M.mem x X ∧ Senv_update_d I f i x g ∧ Fs_code_d I ω X g b q ∧ M.PairMember I j q T

def ft_arg_m (k : Nat) {d} (ω X R b T f p i j : Term d) : Formula 1 d := match k with
  | 0 => .existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 i.weaken.weaken (.bound 1) f.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 j.weaken.weaken .newest f.weaken.weaken)
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken))))
  | 1 => .existsE (.conj (Formula.orderedPairMem 𝒞 i.weaken .newest f.weaken)
    (Formula.orderedPairMem 𝒞 j.weaken .newest f.weaken))
  | 2 => .neg (.disj (Formula.orderedPairMem 𝒞 i p T) (Formula.orderedPairMem 𝒞 j p T))
  | _ => .existsE (.existsE (.existsE (.conj (.mem (.bound 2) X.weaken.weaken.weaken) (.conj
    (senv_update_m (𝒞 := 𝒞) f.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 2) (.bound 1)) (.conj
    (fs_code_m (𝒞 := 𝒞) ω.weaken.weaken.weaken X.weaken.weaken.weaken (.bound 1) b.weaken.weaken.weaken .newest)
    (Formula.orderedPairMem 𝒞 j.weaken.weaken.weaken .newest T.weaken.weaken.weaken))))))
@[simp] theorem ft_arg_closed_l (k : Nat) {d} (ω X R b T f p i j : Term d)
    (hω : ω.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hb : b.freeSupport = []) (hT : T.freeSupport = []) (hf : f.freeSupport = [])
    (hp : p.freeSupport = []) (hi : i.freeSupport = []) (hj : j.freeSupport = []) :
    (ft_arg_m (𝒞 := 𝒞) k ω X R b T f p i j).FreeClosed := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp -implicitDefEqProofs [ft_arg_m, Definitional.Formula.FreeClosed, hω, hX, hR, hb, hT, hf, hp, hi, hj]

theorem ft_arg_sat_l (hE : Extensional M) (k : Nat) {d} (ρ : Env M d) (ω X R b T f p i j : Term d) :
    Formula.satisfies ρ (ft_arg_m (𝒞 := 𝒞) k ω X R b T f p i j) ↔
      Ft_arg_d I k (ω.eval ρ) (X.eval ρ) (R.eval ρ) (b.eval ρ) (T.eval ρ)
        (f.eval ρ) (p.eval ρ) (i.eval ρ) (j.eval ρ) := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp only [ft_arg_m, Ft_arg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, senv_update_sat_l I hE, fs_code_sat_l I hE,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

def Ft_node_d (ω X R b T c f p : M.Domain) : Prop :=
  ∃ k : Fin 4, ∃ i j, Sop_d I k.val c i j ∧ Ft_arg_d I k.val ω X R b T f p i j

private def ft_case_m (k : Nat) {d} (ω X R b T c f p : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (sop_m (𝒞 := 𝒞) k c.weaken.weaken (.bound 1) .newest)
  (ft_arg_m (𝒞 := 𝒞) k ω.weaken.weaken X.weaken.weaken R.weaken.weaken b.weaken.weaken T.weaken.weaken
    f.weaken.weaken p.weaken.weaken (.bound 1) .newest)))
derive_free_closed ft_case_m

def ft_node_m {d} (ω X R b T c f p : Term d) : Formula 1 d := .disj
  (ft_case_m (𝒞 := 𝒞) 0 ω X R b T c f p) (.disj (ft_case_m (𝒞 := 𝒞) 1 ω X R b T c f p)
    (.disj (ft_case_m (𝒞 := 𝒞) 2 ω X R b T c f p) (ft_case_m (𝒞 := 𝒞) 3 ω X R b T c f p)))
derive_free_closed ft_node_m

theorem ft_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R b T c f p : Term d) :
    Formula.satisfies ρ (ft_node_m (𝒞 := 𝒞) ω X R b T c f p) ↔
      Ft_node_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (b.eval ρ) (T.eval ρ) (c.eval ρ) (f.eval ρ) (p.eval ρ) := by
  simp only [ft_node_m, Ft_node_d, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, ft_case_m,
    Formula.satisfies_disj_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sop_sat_l I, ft_arg_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]; rfl

theorem ft_node_decode_l (hKP : M.Models KP) {ω X R b T c f p i j} (k : Fin 4) (hs : Sop_d I k.val c i j) :
    Ft_node_d I ω X R b T c f p ↔ Ft_arg_d I k.val ω X R b T f p i j := by
  refine ⟨?_, fun h => ⟨k, i, j, hs, h⟩⟩
  rintro ⟨l, a, d, ht, h⟩
  obtain ⟨eq, rfl, rfl⟩ := sop_injective_l I hKP hs ht
  have kl : k = l := Fin.ext eq
  exact kl ▸ h

def Ft_eval_d (ω X R b F n T : M.Domain) : Prop := M.IsSetRelation I T ∧
  (∀ r p, M.PairMember I r p T → M.mem r n ∧
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ Fs_code_d I ω X f b p) ∧
  ∀ r c f p, M.PairMember I r c F → M.IsSetFunctionFromTo I f ω X → Fs_code_d I ω X f b p →
    (M.PairMember I r p T ↔ Ft_node_d I ω X R b T c f p)

def ft_eval_m {d} (ω X R b F n T : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 T) (.conj
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest T.weaken.weaken)
    (.conj (.mem (.bound 1) n.weaken.weaken) (.existsE (.conj
      (Formula.isFunctionFromTo 𝒞 .newest ω.weaken.weaken.weaken X.weaken.weaken.weaken)
      (fs_code_m (𝒞 := 𝒞) ω.weaken.weaken.weaken X.weaken.weaken.weaken .newest b.weaken.weaken.weaken (.bound 1))))))))
  (.forallE (.forallE (.forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 2) F.weaken.weaken.weaken.weaken) (.imp
    (Formula.isFunctionFromTo 𝒞 (.bound 1) ω.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken) (.imp
    (fs_code_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken (.bound 1)
      b.weaken.weaken.weaken.weaken .newest) (.iff
    (Formula.orderedPairMem 𝒞 (.bound 3) .newest T.weaken.weaken.weaken.weaken)
    (ft_node_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
      b.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))))))))
derive_free_closed ft_eval_m

theorem ft_eval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R b F n T : Term d) :
    Formula.satisfies ρ (ft_eval_m (𝒞 := 𝒞) ω X R b F n T) ↔
      Ft_eval_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (b.eval ρ) (F.eval ρ) (n.eval ρ) (T.eval ρ) := by
  simp only [ft_eval_m, Ft_eval_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    fs_code_sat_l I hE, Formula.satisfies_iff_iff, ft_node_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 平坦真值方程与原满足关系一致

原程序的内部强归纳同时处理全部前缀编码。存在量词的更新赋值重新编码于
同一秩层；因而新方程不依赖外部良基性，也没有额外的真值或编码存在假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
local notation "J" => fp_interpretation_l (ZF.models_kpi_l hZF)

/-- 对严格较早行的一次语义归纳步，供存在性和正确性两处共用。 -/
theorem ft_step_l {ω ν X R E F n b H T r c f p : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hων : M.MemberSubset ω ν) (hF : Sfm_d J ω n F)
    (hE : M.IsFunctionSpace J E ω X) (hH : Seval_d J X R E F n H)
    (hc : M.PairMember J r c F) (hf : M.mem f E) (hp : Fs_code_d J ω X f b p)
    (read : ∀ s, M.mem s r → ∀ g q, M.mem g E → Fs_code_d J ω X g b q →
      (M.PairMember J s q T ↔ Ssat_d J X R E F n s g)) :
    Ft_node_d J ω X R b T c f p ↔ Ssat_d J X R E F n r f := by
  rcases hF.2.2 r c hc with ⟨i, j, code, _, _⟩ | ⟨i, j, code, _, _⟩ |
    ⟨i, j, code, hi, hj⟩ | ⟨i, j, code, hi, hj⟩
  · rw [ft_node_decode_l J (ZF.modelsKP hZF) 0 code, ssat_op_l J hZF hF hH hc 0 code f]
    exact ⟨fun h => ⟨hf, h⟩, And.right⟩
  · rw [ft_node_decode_l J (ZF.modelsKP hZF) 1 code, ssat_op_l J hZF hF hH hc 1 code f]
    exact ⟨fun h => ⟨hf, h⟩, And.right⟩
  · rw [ft_node_decode_l J (ZF.modelsKP hZF) 2 code, ssat_nor_l J hZF hF hH hc code hf]
    exact not_congr (or_congr (read i hi f p hf hp) (read j hj f p hf hp))
  · rw [ft_node_decode_l J (ZF.modelsKP hZF) 3 code, ssat_exists_l J hZF hF hH hc code hf]
    constructor
    · rintro ⟨x, g, q, hx, update, cq, truth⟩
      have hg := (hE g).mpr (update.function_l J ((hE f).mp hf) hi hx)
      exact ⟨x, g, hx, update, (read j hj g q hg cq).mp truth⟩
    · rintro ⟨x, g, hx, update, truth⟩
      have hg := update.function_l J ((hE f).mp hf) hi hx
      obtain ⟨q, _, cq⟩ := fp_finite_rank_l I hZF hω hV hων hg (hp.bound_l J).1
      exact ⟨x, g, q, hx, update, cq, (read j hj g q ((hE g).mpr hg) cq).mpr truth⟩

/-- 任意满足四条平坦方程的实际表，都等于原内部满足关系。 -/
theorem Ft_eval_d.correct_l {ω ν X R E F n b T r f p : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hων : M.MemberSubset ω ν) (hF : Sfm_d J ω n F)
    (hE : M.IsFunctionSpace J E ω X) (h : Ft_eval_d J ω X R b F n T)
    (hr : M.mem r n) (hf : M.mem f E) (hp : Fs_code_d J ω X f b p) :
    M.PairMember J r p T ↔ Ssat_d J X R E F n r f := by
  obtain ⟨H, hH⟩ := seval_exists_l J hZF X R E F hF.2.1.1
  let ρ : Env M 8 := ⟨Fin.cases T (Fin.cases b (Fin.cases n (Fin.cases F
    (Fin.cases E (Fin.cases R (Fin.cases X (fun _ => ω))))))), fun _ => X⟩
  let φ : UnarySchema 8 := { body := .forallE (.forallE (.imp (.mem (.bound 1) (.bound 7)) (.imp
    (fs_code_m (𝒞 := FlatPairing.convention) (.bound 10) (.bound 9) (.bound 1) (.bound 4) .newest) (.iff
    (Formula.orderedPairMem FlatPairing.convention (.bound 2) .newest (.bound 3))
    (ssat_m (𝒞 := FlatPairing.convention) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 1)))))) }
  have sat s : φ.denote ρ s ↔ ∀ g q, M.mem g E → Fs_code_d J ω X g b q →
      (M.PairMember J s q T ↔ Ssat_d J X R E F n s g) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, fs_code_sat_l J hZF.1, Formula.satisfies_iff_iff,
      Formula.satisfies_orderedPairMem_iff J, ssat_sat_l J hZF.1]; rfl
  apply (sat r).mp (sfm_induction_l J hZF hF φ ρ ?_ hr) f p hf hp
  intro s hs ih
  apply (sat s).mpr
  intro g q hg cq
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 s).mp hs
  exact (h.2.2 s c g q hc ((hE g).mp hg) cq).trans
    (ft_step_l I hZF hω hV hων hF hE hH hc hg cq (fun t ht => (sat t).mp (ih t ht)))

/-- 平坦表由原满足关系分离得到，且整个表只占用一个后继秩层。 -/
theorem ft_eval_rank_l {ω ν μ X Y R E F n b : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hW : V_d I μ Y) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hF : Sfm_d J ω n F) (hb : Sbound_d J F b) (hE : M.IsFunctionSpace J E ω X) :
    ∃ T, M.mem T Y ∧ Ft_eval_d J ω X R b F n T := by
  obtain ⟨H, hH⟩ := seval_exists_l J hZF X R E F hF.2.1.1
  let ρ : Env M 7 := ⟨Fin.cases b (Fin.cases n (Fin.cases F (Fin.cases E
    (Fin.cases R (Fin.cases X (fun _ => ω)))))), fun _ => X⟩
  let φ : BinarySchema 7 := { body := .conj (.mem (.bound 1) (.bound 3)) (.existsE (.conj
    (.mem .newest (.bound 6)) (.conj
    (fs_code_m (𝒞 := FlatPairing.convention) (.bound 9) (.bound 8) .newest (.bound 3) (.bound 1))
    (ssat_m (𝒞 := FlatPairing.convention) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest)))) }
  have sat r p : φ.denote ρ r p ↔ M.mem r n ∧
      ∃ f, M.mem f E ∧ Fs_code_d J ω X f b p ∧ Ssat_d J X R E F n r f := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, fs_code_sat_l J hZF.1, ssat_sat_l J hZF.1]; rfl
  obtain ⟨T, hT, val⟩ := ZF.exists_setRelationOn_of_denote hZF J φ ρ X
  have read r p : M.PairMember J r p T ↔ M.mem r n ∧
      ∃ f, M.mem f E ∧ Fs_code_d J ω X f b p ∧ Ssat_d J X R E F n r f := by
    refine (val r p).trans ⟨fun h => (sat r p).mp h.2.2, ?_⟩
    intro h
    obtain ⟨hr, f, hf, cp, ht⟩ := h
    have hrω := (hω.isOrdinal (ZF.modelsKP hZF)).transitive n hF.1 r hr
    exact ⟨ZF.v_ordinal_mem_l I hZF hV (hων r hrω), (cp.bound_l J).2, (sat r p).mpr ⟨hr, f, hf, cp, ht⟩⟩
  have truth r (hr : M.mem r n) f p (hf : M.mem f E) (cp : Fs_code_d J ω X f b p) :
      M.PairMember J r p T ↔ Ssat_d J X R E F n r f := by
    refine (read r p).trans ⟨?_, fun h => ⟨hr, f, hf, cp, h⟩⟩
    rintro ⟨_, g, hg, cq, h⟩
    have agree := (cq.prefix_l J hZF hω ((hE g).mp hg) ((hE f).mp hf) cp).mp rfl
    exact (ssat_agree_l J hZF hF hb hE hr hg hf agree).mp h
  refine ⟨T, (ZF.v_successor_l I hZF hV hW hs T).mpr (fp_relation_rank_l I hZF hω hV hων hT),
    hT.1, ?_, ?_⟩
  · intro r p hp
    obtain ⟨hr, f, hf, cp, _⟩ := (read r p).mp hp
    exact ⟨hr, f, (hE f).mp hf, cp⟩
  · intro r c f p hc hf cp
    have hr := (hF.2.1.2.2 r).mpr ⟨c, hc⟩
    exact (truth r hr f p ((hE f).mpr hf) cp).trans
      (ft_step_l I hZF hω hV hων hF hE hH hc ((hE f).mpr hf) cp
        (fun s hs => truth s (hF.2.1.1.transitive r hr s hs))).symm

end YesMetaZFC.SetTheory.Internal

/-! ## 平坦程序的秩界和指令绝对性

程序长度及所有编号仍来自内部 ω；只有四个固定构造符的标签使用外部有限归纳。
程序图是任意 Vν（ν≥ω）的子集，因此可在 V(ν+1) 中读取全部内部程序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sfm_node_naturals_l (hZF : M.Models ZF) {ω r c i j : M.Domain} {k : Nat}
    (hω : M.IsOmega ω) (hr : M.mem r ω) (h : Sfm_node_d I ω r c) (hs : Sop_d I k c i j) :
    M.mem i ω ∧ M.mem j ω := by
  rcases h with ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ <;>
    obtain ⟨rfl, rfl, rfl⟩ := sop_injective_l I (ZF.modelsKP hZF) hs ht
  · exact ⟨ha, hb⟩
  · exact ⟨ha, hb⟩
  · exact ⟨hω.transitive (ZF.modelsKP hZF) r hr i ha, hω.transitive (ZF.modelsKP hZF) r hr j hb⟩
  · exact ⟨ha, hω.transitive (ZF.modelsKP hZF) r hr j hb⟩

/-- 任一合法指令的三项坐标均为自然数，结论与配对约定无关。 -/
theorem sfm_node_components_l (hZF : M.Models ZF) {ω r c k p i j : M.Domain}
    (hω : M.IsOmega ω) (hr : M.mem r ω) (h : Sfm_node_d I ω r c)
    (hc : I.Codes c k p) (hp : I.Codes p i j) : M.mem k ω ∧ M.mem i ω ∧ M.mem j ω := by
  have read {l a b} (hs : Sop_d I l c a b) : M.mem k ω ∧ M.mem i ω ∧ M.mem j ω := by
    have ij := sfm_node_naturals_l I hZF hω hr h hs
    obtain ⟨q, o, ho, hq, ht⟩ := hs
    obtain ⟨rfl, rfl⟩ := I.injective hc ht
    obtain ⟨rfl, rfl⟩ := I.injective hp hq
    exact ⟨num_mem_l hZF.1 hω ho, ij⟩
  rcases h with ⟨_, _, hs, _, _⟩ | ⟨_, _, hs, _, _⟩ | ⟨_, _, hs, _, _⟩ | ⟨_, _, hs, _, _⟩ <;> exact read hs

variable (hZF : M.Models ZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem fp_program_rank_l {ω ν X n F : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hων : M.MemberSubset ω ν) (hF : Sfm_d K ω n F) : M.MemberSubset F X := by
  have natural x (hx : M.mem x ω) := ZF.v_ordinal_mem_l I hZF hV (hων x hx)
  have pair {p x y} (h : (K).Codes p x y) (hx : M.mem x X) (hy : M.mem y X) :=
    ((fp_fixed_l hZF.1 hω).mp h).rank_mem_l I hZF hω hV hων hx hy
  intro p hp
  obtain ⟨r, c, code⟩ := hF.2.1.2.1.1 p hp
  have hc : M.PairMember K r c F := ⟨p, code, hp⟩
  have hr := hω.transitive (ZF.modelsKP hZF) n hF.1 r ((hF.2.1.2.2 r).mpr ⟨c, hc⟩)
  have op {k i j} (hs : Sop_d K k c i j) : M.mem c X := by
    have ij := sfm_node_naturals_l K hZF hω hr (hF.2.2 r c hc) hs
    obtain ⟨a, o, ho, ca, cc⟩ := hs
    exact pair cc (natural o (num_mem_l hZF.1 hω ho)) (pair ca (natural i ij.1) (natural j ij.2))
  apply pair code (natural r hr)
  rcases hF.2.2 r c hc with ⟨_, _, h, _, _⟩ | ⟨_, _, h, _, _⟩ | ⟨_, _, h, _, _⟩ | ⟨_, _, h, _, _⟩ <;> exact op h

/-- 包含 ω 的秩层已经容纳全部平坦程序，不要求该层为极限层。 -/
theorem fp_program_mem_l {ω μ Y n F : M.Domain} (hω : M.IsOmega ω)
    (hW : V_d I μ Y) (hωY : M.mem ω Y) (hf : Sfm_d K ω n F) : M.mem F Y := by
  obtain ⟨W, hw⟩ := ZF.v_exists_l I hZF (hω.isOrdinal (ZF.modelsKP hZF))
  exact v_subset_mem_l I hW
    (ZF.v_mem_l I hZF hw hW (ZF.v_ordinal_height_l hZF hW (hω.isOrdinal (ZF.modelsKP hZF)) hωY))
    (fp_program_rank_l I hZF hω hw (fun _ h => h) hf)

theorem rt_num_l {Y : M.Domain} (hY : M.TransitiveSet Y) (ny : Nonempty {y // M.mem y Y})
    (hE : Extensional M) (k : Nat) (x : (rt_model_l Y ny).Domain) :
    Num_d (M := rt_model_l Y ny) k x ↔ Num_d k x.val := by
  induction k generalizing x with
  | zero => exact ⟨fun h y hy => h ⟨y, hY x.val x.property y hy⟩ hy, fun h y => h y.val⟩
  | succ k ih =>
    constructor
    · rintro ⟨y, hn, succ⟩
      exact ⟨y.val, (ih y).mp hn, (rt_successor_l hY ny hE x y).mp succ⟩
    · rintro ⟨y, hn, succ⟩
      let y' : (rt_model_l Y ny).Domain := ⟨y, hY x.val x.property y succ.predecessor_mem⟩
      exact ⟨y', (ih y').mpr hn, (rt_successor_l hY ny hE x y').mpr succ⟩

variable {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY
include hω hW

theorem fp_sop_coordinates_l {c i j : M.Domain} {k : Nat} (hc : M.mem c Y) (h : Sop_d K k c i j) :
    M.mem i Y ∧ M.mem j Y := by
  obtain ⟨a, o, _, ha, ht⟩ := h
  have oa := ((fp_fixed_l hZF.1 hω).mp ht).inverse_rank_l I hZF hω.1 hW hc
  exact ((fp_fixed_l hZF.1 hω).mp ha).inverse_rank_l I hZF hω.1 hW oa.2

theorem rt_fp_sop_l (k : Nat) (c i j : (N).Domain) :
    Sop_d J k c i j ↔ Sop_d K k c.val i.val j.val := by
  have num := rt_num_l (v_transitive_l I hW) (Nonempty.intro (Subtype.mk ω hωY)) hZF.1 k
  constructor
  · rintro ⟨a, o, ho, ha, hc⟩
    exact ⟨a.val, o.val, (num o).mp ho, (fp_fixed_l hZF.1 hω).mpr ha, (fp_fixed_l hZF.1 hω).mpr hc⟩
  · rintro ⟨a, o, ho, ha, hc⟩
    have oa := ((fp_fixed_l hZF.1 hω).mp hc).inverse_rank_l I hZF hω.1 hW c.property
    let a' : (N).Domain := ⟨a, oa.2⟩
    let o' : (N).Domain := ⟨o, oa.1⟩
    exact ⟨a', o', (num o').mpr ho, (fp_fixed_l hZF.1 hω).mp ha, (fp_fixed_l hZF.1 hω).mp hc⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 平坦真值方程在后继秩层中的绝对性

存在量词的对象、更新赋值和新前缀均有已经实现的秩界；把这些见证收回源内，
便得到四种逻辑构造的双向相对化，不假设后继秩层是 ZF 模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY

theorem rt_ft_arg_l (k : Nat) (A R b T f p i j : (N).Domain) {ν : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hf : M.IsSetFunctionFromTo K f.val ω A.val) (hi : M.mem i.val ω) :
    Ft_arg_d J k ⟨ω, hωY⟩ A R b T f p i j ↔
      Ft_arg_d K k ω A.val R.val b.val T.val f.val p.val i.val j.val := by
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have trans := v_transitive_l I hW
  rcases k with _ | (_ | (_ | k))
  · refine ⟨fun ⟨x, y, hx, hy, hR⟩ => ⟨x.val, y.val, (entry i x f).mp hx,
      (entry j y f).mp hy, (entry x y R).mp hR⟩, ?_⟩
    rintro ⟨x, y, hx, hy, hR⟩
    let x' : (N).Domain := ⟨x, (rt_fp_coordinates_l I hZF hω hW f.property hx).2⟩
    let y' : (N).Domain := ⟨y, (rt_fp_coordinates_l I hZF hω hW f.property hy).2⟩
    exact ⟨x', y', (entry i x' f).mpr hx, (entry j y' f).mpr hy, (entry x' y' R).mpr hR⟩
  · refine ⟨fun ⟨x, hx, hy⟩ => ⟨x.val, (entry i x f).mp hx, (entry j x f).mp hy⟩, ?_⟩
    rintro ⟨x, hx, hy⟩
    let x' : (N).Domain := ⟨x, (rt_fp_coordinates_l I hZF hω hW f.property hx).2⟩
    exact ⟨x', (entry i x' f).mpr hx, (entry j x' f).mpr hy⟩
  · exact not_congr (or_congr (entry i p T) (entry j p T))
  · constructor
    · rintro ⟨x, g, q, hx, update, code, truth⟩
      exact ⟨x.val, g.val, q.val, hx, (rt_fp_update_l I hZF hω hW hωY f i x g).mp update,
        (rt_fs_code_l I hZF hω hW hωY A g b q hV hων).mp code, (entry j q T).mp truth⟩
    · rintro ⟨x, g, q, hx, update, code, truth⟩
      have hg := update.function_l K hf hi hx
      have bound := fp_function_rank_l I hZF hω hV hων
        (fun t ht => ZF.v_ordinal_mem_l I hZF hV (hων t ht)) hg
      let x' : (N).Domain := ⟨x, trans A.val A.property x hx⟩
      let g' : (N).Domain := ⟨g, (ZF.v_successor_l I hZF hV hW hs g).mpr bound⟩
      let q' : (N).Domain := ⟨q, trans A.val A.property q (code.bound_l K).2⟩
      exact ⟨x', g', q', hx, (rt_fp_update_l I hZF hω hW hωY f i x' g').mpr update,
        (rt_fs_code_l I hZF hω hW hωY A g' b q' hV hων).mpr code, (entry j q' T).mpr truth⟩

theorem rt_ft_node_l (A R b T c f p : (N).Domain) {ν r : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hf : M.IsSetFunctionFromTo K f.val ω A.val) (hr : M.mem r ω) (hc : Sfm_node_d K ω r c.val) :
    Ft_node_d J ⟨ω, hωY⟩ A R b T c f p ↔ Ft_node_d K ω A.val R.val b.val T.val c.val f.val p.val := by
  constructor
  · rintro ⟨k, i, j, code, arg⟩
    have code' := (rt_fp_sop_l I hZF hω hW hωY k.val c i j).mp code
    have hi := (sfm_node_naturals_l K hZF hω hr hc code').1
    exact ⟨k, i.val, j.val, code', (rt_ft_arg_l I hZF hω hW hωY k.val A R b T f p i j hV hs hων hf hi).mp arg⟩
  · rintro ⟨k, i, j, code, arg⟩
    have ij := fp_sop_coordinates_l I hZF hω hW c.property code
    let i' : (N).Domain := ⟨i, ij.1⟩
    let j' : (N).Domain := ⟨j, ij.2⟩
    have hi := (sfm_node_naturals_l K hZF hω hr hc code).1
    exact ⟨k, i', j', (rt_fp_sop_l I hZF hω hW hωY k.val c i' j').mpr code,
      (rt_ft_arg_l I hZF hω hW hωY k.val A R b T f p i' j' hV hs hων hf hi).mpr arg⟩

theorem rt_ft_eval_l (A R b F n T : (N).Domain) {ν : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hF : Sfm_d K ω n.val F.val) :
    Ft_eval_d J ⟨ω, hωY⟩ A R b F n T ↔ Ft_eval_d K ω A.val R.val b.val F.val n.val T.val := by
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have fn f := rt_fp_function_from_l I hZF hω hW hωY f ⟨ω, hωY⟩ A
  have code f p := rt_fs_code_l I hZF hω hW hωY A f b p hV hων
  have trans := v_transitive_l I hW
  have own f (hf : M.IsSetFunctionFromTo K f ω A.val) : M.mem f Y :=
    (ZF.v_successor_l I hZF hV hW hs f).mpr (fp_function_rank_l I hZF hω hV hων
      (fun t ht => ZF.v_ordinal_mem_l I hZF hV (hων t ht)) hf)
  have row r c (hc : M.PairMember K r c F.val) : M.mem r ω :=
    hω.transitive (ZF.modelsKP hZF) n.val hF.1 r ((hF.2.1.2.2 r).mpr ⟨c, hc⟩)
  constructor
  · rintro ⟨rel, bound, eval⟩
    refine ⟨(rt_fp_relation_l I hZF hω hW hωY T).mp rel, ?_, ?_⟩
    · intro r p hp
      have rp := rt_fp_coordinates_l I hZF hω hW T.property hp
      let r' : (N).Domain := ⟨r, rp.1⟩
      let p' : (N).Domain := ⟨p, rp.2⟩
      obtain ⟨hr, f, hf, cp⟩ := bound r' p' ((entry r' p' T).mpr hp)
      exact ⟨hr, f.val, (fn f).mp hf, (code f p').mp cp⟩
    · intro r c f p hc hf cp
      have rc := rt_fp_coordinates_l I hZF hω hW F.property hc
      let r' : (N).Domain := ⟨r, rc.1⟩
      let c' : (N).Domain := ⟨c, rc.2⟩
      let f' : (N).Domain := ⟨f, own f hf⟩
      let p' : (N).Domain := ⟨p, trans A.val A.property p (cp.bound_l K).2⟩
      exact (entry r' p' T).symm.trans ((eval r' c' f' p' ((entry r' c' F).mpr hc)
        ((fn f').mpr hf) ((code f' p').mpr cp)).trans
        (rt_ft_node_l I hZF hω hW hωY A R b T c' f' p' hV hs hων hf (row r c hc) (hF.2.2 r c hc)))
  · rintro ⟨rel, bound, eval⟩
    refine ⟨(rt_fp_relation_l I hZF hω hW hωY T).mpr rel, ?_, ?_⟩
    · intro r p hp
      obtain ⟨hr, f, hf, cp⟩ := bound r.val p.val ((entry r p T).mp hp)
      let f' : (N).Domain := ⟨f, own f hf⟩
      exact ⟨hr, f', (fn f').mpr hf, (code f' p).mpr cp⟩
    · intro r c f p hc hf cp
      have hc' := (entry r c F).mp hc
      have hf' := (fn f).mp hf
      exact (entry r p T).trans ((eval r.val c.val f.val p.val hc' hf' ((code f p).mp cp)).trans
        (rt_ft_node_l I hZF hω hW hωY A R b T c f p hV hs hων hf'
          (row r.val c.val hc') (hF.2.2 r.val c.val hc')).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 在一个后继秩层中表达完整内部满足关系

单一公式量化坐标界、前缀及平坦真值表。坐标界由程序自动产生，其余见证
由实际秩界自动回收；与原满足关系的等价覆盖所有内部程序，包含非标准长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ft_sat_d (ω X R F n r f : M.Domain) : Prop := M.IsSetFunctionFromTo I f ω X ∧
  ∃ b p T, Fs_code_d I ω X f b p ∧ Ft_eval_d I ω X R b F n T ∧ M.PairMember I r p T

def ft_sat_m {d} (ω X R F n r f : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 f ω X)
  (.existsE (.existsE (.existsE (.conj
    (fs_code_m (𝒞 := 𝒞) ω.weaken.weaken.weaken X.weaken.weaken.weaken f.weaken.weaken.weaken (.bound 2) (.bound 1))
    (.conj (ft_eval_m (𝒞 := 𝒞) ω.weaken.weaken.weaken X.weaken.weaken.weaken R.weaken.weaken.weaken (.bound 2)
      F.weaken.weaken.weaken n.weaken.weaken.weaken .newest)
      (Formula.orderedPairMem 𝒞 r.weaken.weaken.weaken (.bound 1) .newest))))))
derive_free_closed ft_sat_m

theorem ft_sat_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R F n r f : Term d) :
    Formula.satisfies ρ (ft_sat_m (𝒞 := 𝒞) ω X R F n r f) ↔
      Ft_sat_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ) (f.eval ρ) := by
  simp only [ft_sat_m, Ft_sat_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_exists_iff, fs_code_sat_l I hE, ft_eval_sat_l I hE,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF) {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY

theorem ft_sat_source_l (A R F n r f : (N).Domain) {ν E : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hF : Sfm_d K ω n.val F.val) (hr : M.mem r.val n.val)
    (hE : M.IsFunctionSpace K E ω A.val) (hf : M.IsSetFunctionFromTo K f.val ω A.val) :
    Ft_sat_d J ⟨ω, hωY⟩ A R F n r f ↔ Ssat_d K A.val R.val E F.val n.val r.val f.val := by
  have entry := rt_fp_entry_l I hZF hω hW hωY
  have trans := v_transitive_l I hW
  constructor
  · rintro ⟨_, b, p, T, code, eval, truth⟩
    have code' := (rt_fs_code_l I hZF hω hW hωY A f b p hV hων).mp code
    have eval' := (rt_ft_eval_l I hZF hω hW hωY A R b F n T hV hs hων hF).mp eval
    exact (eval'.correct_l I hZF hω hV hων hF hE hr ((hE f.val).mpr hf) code').mp ((entry r p T).mp truth)
  · intro truth
    obtain ⟨b, hb, bound⟩ := sbound_exists_l K hZF hω hF
    obtain ⟨p, hp, code⟩ := fp_finite_rank_l I hZF hω hV hων hf hb
    obtain ⟨T, ht, eval⟩ := ft_eval_rank_l I hZF hω hV hW hs hων hF bound hE
    let b' : (N).Domain := ⟨b, trans ω hωY b hb⟩
    let p' : (N).Domain := ⟨p, trans A.val A.property p hp⟩
    let T' : (N).Domain := ⟨T, ht⟩
    exact ⟨(rt_fp_function_from_l I hZF hω hW hωY f ⟨ω, hωY⟩ A).mpr hf, b', p', T',
      (rt_fs_code_l I hZF hω hW hωY A f b' p' hV hων).mpr code,
      (rt_ft_eval_l I hZF hω hW hωY A R b' F n T' hV hs hων hF).mpr eval,
      (entry r p' T').mpr ((eval.correct_l I hZF hω hV hων hF hE hr ((hE f.val).mpr hf) code).mpr truth)⟩

/-- 自动构造赋值空间，并把源内单一原公式接回已有统一满足关系。 -/
theorem ft_source_satisfaction_l (A R F n r f : (N).Domain) {ν c a : M.Domain}
    (hV : V_d I ν A.val) (hs : M.SuccessorOf μ ν) (hων : M.MemberSubset ω ν)
    (hc : Smdl_d K c A.val R.val) (ha : Sformula_d K ω a n.val F.val r.val)
    (hf : M.IsSetFunctionFromTo K f.val ω A.val) :
    Ft_sat_d J ⟨ω, hωY⟩ A R F n r f ↔ Satisfies_d K ω c a f.val := by
  obtain ⟨E, hE, _⟩ := senv_space_l K hZF ω hc.2.1
  exact (ft_sat_source_l I hZF hω hW hωY A R F n r f hV hs hων ha.2.1 ha.2.2 hE hf).trans
    (satisfies_decode_l K hZF.1 hc ha hE).symm

end YesMetaZFC.SetTheory.Internal
